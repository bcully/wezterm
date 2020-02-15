//! The tmux client control control protocol (tmux -CC)
//! TODOS:
//!   * proper parser for %begin/%end delimited lines in advance()
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
use crate::mux::tab::{Tab, TabId};
use crate::mux::window::WindowId;
use crate::mux::Mux;
use anyhow::bail;
use async_trait::async_trait;
use portable_pty::{CommandBuilder, PtySize};
use promise::spawn::spawn_into_main_thread;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Copy, Clone, PartialEq, Eq)]
enum State {
    WaitingForFirstResponse,
    Running,
}

pub struct TmuxDomain {
    id: DomainId,
    embedding_tab_id: TabId,
    line_buffer: RefCell<Vec<u8>>,
    state: RefCell<State>,
}

impl TmuxDomain {
    pub fn new(embedding_tab_id: TabId) -> Self {
        let id = alloc_domain_id();
        Self {
            id,
            embedding_tab_id,
            line_buffer: RefCell::new(vec![]),
            state: RefCell::new(State::WaitingForFirstResponse),
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

            if *self.state.borrow() == State::WaitingForFirstResponse && line.starts_with("%end ") {
                *self.state.borrow_mut() = State::Running;
                // Now we can interrogate tmux about the available windows and tabs
                self.send_command("list-windows -F '#{session_name}\t#{window_id}\t#{window_width}\t#{window_height}'");
            }

            log::error!("TmuxDomain: {}", line.escape_debug());

            line_buffer.clear();
        } else {
            line_buffer.push(c);
        }
    }

    fn send_command(&self, cmd: &str) {
        let cmd = cmd.to_owned();
        let tab_id = self.embedding_tab_id;
        spawn_into_main_thread(async move {
            let mux = Mux::get().expect("tmux processing to be on main thread");
            let tab = mux.get_tab(tab_id).expect("tmux tab to exist");
            log::error!("send tmux command: {}", cmd);
            write!(tab.writer(), "{}\n", cmd).ok();
        });
    }
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
        Ok(())
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
