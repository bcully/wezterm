//! The tmux client control control protocol (tmux -CC)
//! TODOS:
//!   * parse the output from the above to process responses from tmux
//!   * connect windows/tabs to our local Mux via a TmuxTab struct that
//!     implements Tab
//!   * Recognize when a tab is in tmux mode and prevent routing raw input
//!     to the tmux control channel.  Perhaps show an overlay in the gui
//!     similar to ALT-9 mode, but that shows tmux status info.
//!   * When an %error line is returned, emit to the output of the original
//!     tab so that the user can see it.  (this might require some tricky
//!     layering; probably better/easier to do show in the overlay and
//!     let it linger at the end of the session).
//!   * If using an overlay for tmux status, dismiss the overlay when
//!     exit_tmux_mode is called... if there was no error in the above case.

use crate::mux::domain::{alloc_domain_id, Domain, DomainId, DomainState};
use crate::mux::renderable::{Renderable, RenderableDimensions, StableCursorPosition};
use crate::mux::tab::{Tab, TabId, alloc_tab_id};
use crate::mux::window::WindowId;
use crate::mux::Mux;
use anyhow::{anyhow, bail};
use async_trait::async_trait;
use enum_dispatch::enum_dispatch;
use filedescriptor::Pipe;
use log::info;
use portable_pty::{CommandBuilder, PtySize};
use promise::spawn::spawn_into_main_thread;
use rangeset::RangeSet;
use std::cell::{RefCell, RefMut};
use std::collections::{HashMap, VecDeque};
use std::io::{Read, Write};
use std::ops::Range;
use std::rc::Rc;
use term::{KeyCode, KeyModifiers, MouseEvent, TerminalHost, StableRowIndex};
use term::color::ColorPalette;
use termwiz::surface::Line;
use url::Url;

/// The tmux state machine works as follows:
/// The control protocol is line-based, so we consume input a line at a time.
/// The input can be either unsolicited, or in response to a command we have issued.
/// We can tell the difference because command responses are bracketed within %begin/%end/%error
/// lines, inside of which only command responses can appear
///
/// We can issue commands whenever we want, tmux should process them in the order they were issued.
/// We'll want to pipeline commands for latency (at least the send-keys command) but we may choose
/// to buffer a bit to amortize amplification of keys to commands:
/// a single client keystroke can turn into a send-keys command and expect a %begin/%end block
/// in response.
/// One strategy that might work would be to limit the number of commands that could
/// be in the pipe, so that if we start getting too many keys ahead we'll just have to buffer them
/// until an earlier command is retired.
///
/// We can be in the following states:
/// Start: we are waiting for tmux to send an unsolicited %begin/%end pair before we can issue
///   commands. We can't start issuing commands until we move out of this state.
/// Handshaking: we've received the handshake %begin, and are waiting for %end or %error
/// Idle: we are waiting for either tmux to tell us something, or for a user to give us input
/// CommandOutput: we're processing command response data (we've received %begin).
/// Done: we have hit a terminal state, e.g. because we've failed to handshake. Ignore everything.
///
/// In Start, we ignore everything until %begin, which moves us to Handshaking
/// In Handshaking, we move to Done on %error, and %Idle on %end
/// In Idle, we can:
/// * receive notifications, leaving us in idle
/// * receive %begin, moving us to CommandOutput
/// In CommandOutput, we can:
/// * receive %end or %error, moving us to Idle, or
/// * receive command output, leaving us in CommandOutput
/// In Done, we treat all output as error
///
/// Each command knows how to parse its own responses, so we'll route lines received during
/// CommandInFlight to the individual command handlers. They can return events as a result of
/// each line (they may choose to buffer internally if event data spans lines).
///
/// Error handling strategy is log and ignore:
/// If we do not understand an unsolicited message, we'll log it and ignore it
/// If we get an error response from a command, we'll log it and ignore it
/// If we don't understand a command response, we'll log it and ignore it

/// States the tmux controller can be in
#[derive(Copy, Clone)]
enum State {
    /// waiting for tmux %begin handshake
    Start,
    /// waiting for tmux %end or %error handshake
    Handshaking,
    /// receiving notifications
    Idle,
    /// receiving command output
    CommandOutput,
    /// terminal state, we are disconnecting
    Done
}

/// Commands that we can send to tmux
#[derive(Debug, Clone)]
struct CapturePaneCommand {
    window_id: u32,
    command: String
}

#[derive(Debug, Clone)]
struct ListWindowsCommand;

#[derive(Debug, Clone)]
struct SendKeysCommand {
    command: String
}

#[enum_dispatch(TmuxCommand)]
#[derive(Debug, Clone)]
enum Command {
    CapturePaneCommand,
    ListWindowsCommand,
    SendKeysCommand
}

// https://github.com/tmux/tmux/blob/22e9cf04cafeb18c88ef1232d63dff5b5173abac/cmd-queue.c#L491
#[derive(Debug)]
struct TmuxCommandId { time: i64, number: u64, flags: i32 }

/// Event received from tmux
#[derive(Debug)]
enum Event {
    Begin(TmuxCommandId),
    End(TmuxCommandId),
    Error(TmuxCommandId),

    Output { window_id: u32, text: String },

    // events synthesize from command output
    AddWindow { window_id: u32 },

    // notifications we don't yet parse
    Unhandled
}

#[enum_dispatch]
trait TmuxCommand {
    /// command in the form of a string that tmux can parse
    fn command_string(&self) -> &str;

    /// parse a line of tmux output
    fn parse_line(&self, line: &str) -> anyhow::Result<Event>;
}

fn parse_output(s: &str) -> anyhow::Result<Event> {
    let mut fields = s.splitn(3, ' ');
    if fields.next() != Some("%output") {
        bail!("not %output");
    }
    let window_id: u32 = fields.next().ok_or(anyhow!("no window id"))?[1..].parse()?;
    let text = fields.next().ok_or(anyhow!("no text"))?.to_string();
    Ok(Event::Output { window_id, text })
}

fn parse_notification(line: &str) -> anyhow::Result<Event> {
    // str.strip_prefix is only in nightly
    fn strip_prefix<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
        if s.starts_with(prefix) {
            Some(&s[prefix.len()..])
        } else {
            None
        }
    }

    fn parse_command_id(s: &str) -> anyhow::Result<TmuxCommandId> {
        let mut words = s.split(' ');
        let time = words.next().ok_or(anyhow!("%begin missing time: {}", s)).map(|w| w.parse())??;
        let number = words.next().ok_or(anyhow!("%begin missing number: {}", s)).map(|w| w.parse())??;
        let flags = words.next().ok_or(anyhow!("%begin missing flags: {}", s)).map(|w| w.parse())??;

        Ok(TmuxCommandId { time, number, flags })
    }

    if let Some(rest) = strip_prefix(line,"%begin ") {
        Ok(Event::Begin(parse_command_id(rest)?))
    } else if let Some(rest) = strip_prefix(line, "%end ") {
        Ok(Event::End(parse_command_id(rest)?))
    } else if let Some(rest) = strip_prefix(line, "%error ") {
        Ok(Event::Error(parse_command_id(rest)?))
    } else if let Some(_rest) = strip_prefix(line, "%output ") {
        parse_output(line)
    } else {
        Ok(Event::Unhandled)
    }
}

impl TmuxCommand for ListWindowsCommand {
    fn command_string(&self) -> &str {
        "list-windows -F '#{window_id}'"
    }

    fn parse_line(&self, line: &str) -> anyhow::Result<Event> {
        // response is @window_id for some reason
        Ok(Event::AddWindow { window_id: line[1..].parse()? })
    }
}

impl SendKeysCommand {
    fn new(window_id: u32, keys: &[u8]) -> Self {
        let utf8 = std::str::from_utf8(keys).expect("valid utf-8");
        let command = format!("send-keys -l -t {} {}", window_id, utf8);

        Self { command }
    }
}

impl TmuxCommand for SendKeysCommand {
    fn command_string(&self) -> &str {
        &self.command
    }

    fn parse_line(&self, line: &str) -> anyhow::Result<Event> {
        Err(anyhow!("unexpected response: {}", line))
    }
}

impl CapturePaneCommand {
    fn new(window_id: u32) -> Self {
        let command = format!("capture-pane -peCJt {}", window_id);
        Self { window_id, command }
    }
}

impl TmuxCommand for CapturePaneCommand {
    // -J joins lines (there will be only one CR for the entire screen), which lets us continue
    // to process command output a line at a time, with the downside that we have to be able
    // to figure out which part of the response belongs to which line for rendering. For the short
    // term we can use a dumb, expensive alternative to parsing lines, which is to send a separate
    // command for each line. We can at least pipeline them.
    fn command_string(&self) -> &str {
        &self.command
    }

    fn parse_line(&self, line: &str) -> anyhow::Result<Event> {
        Err(anyhow!("unexpected response: {}", line))
    }
}

struct TmuxTabRenderable {
    control_tab: TabId
}

impl TmuxTabRenderable {
    fn new(control_tab: TabId) -> Self {
        Self { control_tab }
    }
}

impl Renderable for TmuxTabRenderable {
    fn get_cursor_position(&self) -> StableCursorPosition {
        StableCursorPosition::default()
    }

    fn get_dirty_lines(&self, lines: Range<StableRowIndex>) -> RangeSet<StableRowIndex> {
        log::error!("get_dirty_lines called for {:#?}", lines);
        let mut result = RangeSet::new();
        result.add_range(lines);
        result
    }

    fn get_lines(&mut self, lines: Range<StableRowIndex>) -> (StableRowIndex, Vec<Line>) {
        log::error!("get_lines called for {:#?}", lines);
        let mux = Mux::get().expect("tmux processing to be on main thread");
        let domain = mux.tmux_domain_for_tab(self.control_tab).expect("to have a tmux domain");
        let _tmux = domain.downcast_ref::<TmuxDomain>().expect("to have a tmux domain");

        let rendered: Vec<Line> = (0..lines.len()).map(|_| Line::with_width(80)).collect();
        (lines.start, rendered)
    }

    fn get_dimensions(&self) -> RenderableDimensions {
        RenderableDimensions { cols: 80, viewport_rows: 24, scrollback_rows: 0, physical_top: 0, scrollback_top: 0 }
    }
}

struct TmuxTab {
    domain_id: DomainId,
    tab_id: TabId,
    // control tab for tmux IO
    control_tab: TabId,
    // tmux window ID for this tab
    window_id: u32,
    reader: Pipe,
    writer: RefCell<TmuxTabWriter>,
    renderable: RefCell<TmuxTabRenderable>,
    lines: RefCell<Vec<Line>>
}

impl TmuxTab {
    fn new(domain_id: DomainId, control_tab: TabId, window_id: u32) -> Self {
        let reader = Pipe::new().expect("Pipe::new failed");
        let writer = RefCell::new(TmuxTabWriter { control_tab, window_id });
        let renderable = RefCell::new(TmuxTabRenderable::new(control_tab));
        let tab_id = alloc_tab_id();

        Self {
            domain_id,
            tab_id,
            control_tab,
            window_id,
            reader,
            writer,
            renderable,
            lines: RefCell::new(vec![]),
        }
    }

    fn send_bytes(&self, bytes: &[u8]) {
        log::error!("tab {} got data of length {}", self.window_id, bytes.len());
    }
}

struct TmuxTabWriter {
    control_tab: TabId,
    window_id: u32
}

impl Write for TmuxTabWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mux = Mux::get().expect("tmux processing to be on main thread");
        let domain = mux.tmux_domain_for_tab(self.control_tab).expect("to have a tmux domain");
        let tmux = domain.downcast_ref::<TmuxDomain>().expect("to have a tmux domain");

        let command = Command::SendKeysCommand(SendKeysCommand::new(self.window_id, buf));
        tmux.send_command(command);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl Tab for TmuxTab {
    fn tab_id(&self) -> TabId {
        self.tab_id
    }

    fn renderer(&self) -> RefMut<dyn Renderable> {
        self.renderable.borrow_mut()
    }

    fn get_title(&self) -> String {
        format!("tmux {}", self.window_id)
    }

    fn send_paste(&self, text: &str) -> anyhow::Result<()> {
        log::error!("got paste: {}", text);
        Ok(())
    }

    fn reader(&self) -> anyhow::Result<Box<dyn Read + Send>> {
        info!("made reader for TmuxTab");
        Ok(Box::new(self.reader.read.try_clone()?))
    }

    fn writer(&self) -> RefMut<dyn Write> {
        self.writer.borrow_mut()
    }

    fn resize(&self, _size: PtySize) -> anyhow::Result<()> {
        Ok(())
    }

    fn key_down(&self, key: KeyCode, _mods: KeyModifiers) -> anyhow::Result<()> {
        log::error!("{} got key {:?}", self.window_id, key);
        if let KeyCode::Char(c) = key {
            let mut s = [0; 4];
            c.encode_utf8(&mut s);
            self.writer.borrow_mut().write(&s);
        }
        Ok(())
    }

    fn mouse_event(&self, _event: MouseEvent, _host: &mut dyn TerminalHost) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn advance_bytes(&self, buf: &[u8], _host: &mut dyn TerminalHost) {
        log::error!("{} got bytes: {}", self.window_id, String::from_utf8_lossy(buf));
    }

    fn is_dead(&self) -> bool {
        false
    }

    fn palette(&self) -> ColorPalette {
        ColorPalette::default()
    }

    fn domain_id(&self) -> DomainId {
        self.domain_id
    }

    fn is_mouse_grabbed(&self) -> bool {
        false
    }

    fn get_current_working_dir(&self) -> Option<Url> {
        None
    }
}

pub struct TmuxDomain {
    id: DomainId,
    embedding_tab_id: TabId,
    line_buffer: RefCell<Vec<u8>>,
    state: RefCell<State>,
    command_queue: RefCell<VecDeque<Command>>,

    tmux_window_to_tab: RefCell<HashMap<u32, TabId>>,
}

impl TmuxDomain {
    pub fn new(embedding_tab_id: TabId) -> Self {
        let id = alloc_domain_id();
        Self {
            id,
            embedding_tab_id,
            line_buffer: RefCell::new(vec![]),
            state: RefCell::new(State::Start),
            command_queue: RefCell::new(VecDeque::new()),
            tmux_window_to_tab: RefCell::new(HashMap::new()),
        }
    }

    /// process a byte sent by the remote tmux instance
    pub fn advance(&self, c: u8) {
        log::trace!("TmuxDomain advance {:x} {}", c, (c as char).escape_debug());
        let mut line_buffer = self.line_buffer.borrow_mut();

        if c == b'\n' {
            // We've got a line.
            // Lines are usually (always?) CRLF terminated
            if line_buffer.last() == Some(&b'\r') {
                line_buffer.pop();
            }

            // iTerm accepts invalid utf8 for lines produced by tmux, so we do too.
            let line = String::from_utf8_lossy(&line_buffer);

            log::error!("TmuxDomain: {}", line.escape_debug());

            if let Some(err) = self.process_line(&line).err() {
                self.handle_error(err);
            }

            line_buffer.clear();
        } else {
            line_buffer.push(c);
        }
    }

    /// consume a line of input from tmux according to current state, move to new state if
    /// appropriate, and perform appropriate operations on terminal
    fn process_line(&self, line: &str) -> anyhow::Result<()> {
        let state = *self.state.borrow();
        match state {
            State::Start => {
                match parse_notification(line)? {
                    Event::Begin(_) => *self.state.borrow_mut() = State::Handshaking,
                    _ => self.handle_error(anyhow!("unexpected message while handshaking: {}", line))
                }
            }
            State::Handshaking => {
                match parse_notification(line)? {
                    Event::End(_) => {
                        *self.state.borrow_mut() = State::Idle;
                        self.send_command(Command::ListWindowsCommand(ListWindowsCommand))
                    },
                    Event::Error(_) => {
                        *self.state.borrow_mut() = State::Done;
                        self.handle_error(anyhow!("error handshaking"));
                    }
                    _ => self.handle_error(anyhow!("error handshaking: {}", line))
                }
            }
            State::Idle => {
                match parse_notification(line)? {
                    Event::Begin(_) => *self.state.borrow_mut() = State::CommandOutput,
                    Event::End(_) | Event::Error(_) => self.handle_error(anyhow!("invalid state! {}", line)),
                    evt => self.handle_event(evt)?
                }
            }
            State::CommandOutput => {
                match parse_notification(line)? {
                    Event::End(_) => {
                        self.retire_command();
                        *self.state.borrow_mut() = State::Idle
                    },
                    Event::Error(_) => {
                        self.handle_error(anyhow!("command returned error: {:?}", self.current_command()));

                        self.retire_command();
                        *self.state.borrow_mut() = State::Idle;
                    }
                    _ => self.handle_event(self.current_command().expect("no command in progress").parse_line(line)?)?
                }
            }
            State::Done => self.handle_error(anyhow!("received data while done: {}", line))
        }

        Ok(())
    }

    fn handle_error(&self, err: anyhow::Error) {
        log::error!("TmuxDomain: error {}", err)
    }

    fn handle_event(&self, event: Event) -> anyhow::Result<()> {
        match event {
            Event::AddWindow { window_id } => self.add_window(window_id)?,
            Event::Output { window_id, text } => self.send_output(window_id, &text)?,
            _ => log::error!("received event: {:?}", event)
        };
        Ok(())
    }

    fn add_window(&self, window_id: u32) -> anyhow::Result<()> {
        log::error!("adding tab for tmux window {}", window_id);
        let mux = Mux::get().expect("to be called on main thread");
        let tab: Rc<dyn Tab> = Rc::new(TmuxTab::new(self.id, self.embedding_tab_id, window_id));
        mux.add_tab(&tab)?;

        self.tmux_window_to_tab.borrow_mut().insert(window_id, tab.tab_id());

        let local_window_id = get_window_for_tab(self.embedding_tab_id);
        mux.add_tab_to_window(&tab, local_window_id)
    }

    fn send_output(&self, window_id: u32, text: &str) -> anyhow::Result<()> {
        log::error!("sending output to {}: {}", window_id, text);
        let tab_id = *self.tmux_window_to_tab.borrow().get(&window_id).expect("to have a tab");
        let mux = Mux::get().expect("to be called on main thread");
        let tab = mux.get_tab(tab_id).unwrap();
        let tmux_tab: &TmuxTab = tab.downcast_ref().unwrap();

        tmux_tab.send_bytes(text.as_bytes());
        Ok(())
    }

    fn send_command(&self, cmd: Command) {
        let tab_id = self.embedding_tab_id;
        let cmdstr = cmd.command_string().to_owned();

        self.command_queue.borrow_mut().push_back(cmd);

        spawn_into_main_thread(async move {
            let mux = Mux::get().expect("tmux processing to be on main thread");
            let tab = mux.get_tab(tab_id).expect("tmux tab to exist");
            log::error!("send tmux command: {}", cmdstr);
            write!(tab.writer(), "{}\n", cmdstr).ok();
        });
    }

    // retires the first command in the queue
    fn retire_command(&self) {
        self.command_queue.borrow_mut().pop_front().expect("no command to retire");
    }

    fn current_command(&self) -> Option<Command> {
        self.command_queue.borrow().front().map(|cmd| cmd.clone())
    }
}

// feels like we might want this somewhere shared?
fn get_window_for_tab(tab_id: TabId) -> WindowId {
    let mux = Mux::get().expect("to be called on main thread");
    let window_id = *mux.windows.borrow().iter().find(|(_, window)| {
        window.idx_by_id(tab_id).is_some()
    }).unwrap().0;

    window_id
}

#[async_trait(?Send)]
impl Domain for TmuxDomain {
    async fn spawn(
        &self,
        _size: PtySize,
        _command: Option<CommandBuilder>,
        _command_dir: Option<String>,
        _window: WindowId,
    ) -> anyhow::Result<Rc<dyn Tab>> {
        bail!("spawn not impl for TmuxDomain");
    }

    /// Returns the domain id, which is useful for obtaining
    /// a handle on the domain later.
    fn domain_id(&self) -> DomainId {
        self.id
    }

    /// Returns the name of the domain
    fn domain_name(&self) -> &str {
        "tmux"
    }

    /// Re-attach to any tabs that might be pre-existing in this domain
    async fn attach(&self) -> anyhow::Result<()> {
        panic!("not expecting attach")
    }

    /// Detach all tabs
    fn detach(&self) -> anyhow::Result<()> {
        bail!("detach not impl for TmuxDomain");
    }

    /// Indicates the state of the domain
    fn state(&self) -> DomainState {
        DomainState::Attached
    }
}
