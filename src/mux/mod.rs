use crate::mux::tab::{Tab, TabId};
use crate::mux::window::{Window, WindowId};
use crate::ratelim::RateLimiter;
use crate::server::pollable::{pollable_channel, PollableReceiver, PollableSender};
use anyhow::{anyhow, Error};
use domain::{Domain, DomainId};
use log::{debug, error};
use portable_pty::ExitStatus;
use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashMap;
use std::io::Read;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use term::TerminalHost;
use termwiz::escape::DeviceControlMode;
use thiserror::*;

pub mod domain;
pub mod renderable;
pub mod tab;
pub mod tmux;
pub mod window;

use tmux::TmuxDomain;

#[derive(Clone, Debug)]
pub enum MuxNotification {
    TabOutput(TabId),
}

static SUB_ID: AtomicUsize = AtomicUsize::new(0);

pub type MuxSubscriber = PollableReceiver<MuxNotification>;

pub struct Mux {
    tabs: RefCell<HashMap<TabId, Rc<dyn Tab>>>,
    windows: RefCell<HashMap<WindowId, Window>>,
    default_domain: RefCell<Option<Arc<dyn Domain>>>,
    domains: RefCell<HashMap<DomainId, Arc<dyn Domain>>>,
    domains_by_name: RefCell<HashMap<String, Arc<dyn Domain>>>,
    subscribers: RefCell<HashMap<usize, PollableSender<MuxNotification>>>,
    tmux_domains: RefCell<HashMap<TabId, Arc<dyn Domain>>>,
}

fn read_from_tab_pty(tab_id: TabId, mut reader: Box<dyn std::io::Read>) {
    const BUFSIZE: usize = 32 * 1024;
    let mut buf = [0; BUFSIZE];

    let mut lim = RateLimiter::new(|config| config.ratelimit_output_bytes_per_second);

    loop {
        match reader.read(&mut buf) {
            Ok(size) if size == 0 => {
                error!("read_pty EOF: tab_id {}", tab_id);
                break;
            }
            Err(err) => {
                error!("read_pty failed: tab {} {:?}", tab_id, err);
                break;
            }
            Ok(size) => {
                let buf = &buf[..size];
                let mut pos = 0;

                while pos < size {
                    match lim.admit_check((size - pos) as u32) {
                        Ok(len) => {
                            let len = len as usize;
                            let data = buf[pos..pos + len].to_vec();
                            pos += len;
                            promise::spawn::spawn_into_main_thread_with_low_priority(async move {
                                let mux = Mux::get().unwrap();
                                if let Some(tab) = mux.get_tab(tab_id) {
                                    let domain = mux.tmux_domain_for_tab(tab_id);
                                    let tmux_domain = domain
                                        .as_ref()
                                        .and_then(|domain| domain.downcast_ref::<TmuxDomain>());

                                    tab.advance_bytes(
                                        &data,
                                        &mut Host {
                                            tab_id,
                                            writer: &mut *tab.writer(),
                                            tmux_domain,
                                        },
                                    );
                                    mux.notify(MuxNotification::TabOutput(tab_id));
                                }
                            });
                        }
                        Err(delay) => {
                            log::trace!("RateLimiter: sleep for {:?}", delay);
                            std::thread::sleep(delay);
                        }
                    }
                }
            }
        }
    }
    promise::spawn::spawn_into_main_thread(async move {
        let mux = Mux::get().unwrap();
        mux.remove_tab(tab_id);
    });
}

/// This is just a stub impl of TerminalHost; it really only exists
/// in order to parse data sent by the peer (so, just to parse output).
/// As such it only really has Host::writer get called.
/// The GUI driven flows provide their own impl of TerminalHost.
struct Host<'a> {
    tab_id: TabId,
    writer: &'a mut dyn std::io::Write,
    tmux_domain: Option<&'a TmuxDomain>,
}

impl<'a> TerminalHost for Host<'a> {
    fn writer(&mut self) -> &mut dyn std::io::Write {
        &mut self.writer
    }

    fn handle_device_control(&mut self, control: DeviceControlMode) {
        match control {
            DeviceControlMode::Enter {
                params,
                intermediates,
                ignored_extra_intermediates: false,
            } => {
                if params.len() == 1 && params[0] == 1000 && intermediates.is_empty() {
                    log::error!("tmux -CC mode requested");

                    // Create a new domain to host these tmux tabs
                    let domain: Arc<dyn Domain> = Arc::new(TmuxDomain::new(self.tab_id));
                    let mux = Mux::get().expect("to be called on main thread");
                    mux.add_tmux_domain(self.tab_id, &domain);

                // TODO: do we need to proactively list available tabs here?
                // if so we should arrange to call domain.attach() and make
                // it do the right thing.
                } else {
                    log::error!(
                        "unknown DeviceControlMode::Enter params={:?}, intermediates={:?}",
                        params,
                        intermediates
                    );
                }
            }
            DeviceControlMode::Data(c) => {
                // This could simply lookup the tmux domain for each byte that
                // passes through here, but that could be a lot for a large read,
                // so we take on a bit of complexity to pre-cache the domain reference
                // when we crate the Host instance so that we can do a slightly
                // cheaper call here.
                if let Some(tmux) = self.tmux_domain.as_ref() {
                    tmux.advance(c);
                } else {
                    // If we're still processing the read in which we created the
                    // tmux domain in the Enter case above, we'll need to look it
                    // up each time here.
                    let mux = Mux::get().expect("to be called on main thread");
                    if let Some(domain) = mux.tmux_domain_for_tab(self.tab_id) {
                        if let Some(tmux) = domain.downcast_ref::<TmuxDomain>() {
                            tmux.advance(c);
                        }
                    } else {
                        log::error!(
                            "unhandled DeviceControlMode::Data {:x} {}",
                            c,
                            (c as char).escape_debug()
                        );
                    }
                }
            }
            _ => {
                log::error!("unhandled: {:?}", control);
            }
        }
    }
}

thread_local! {
    static MUX: RefCell<Option<Rc<Mux>>> = RefCell::new(None);
}

impl Mux {
    pub fn new(default_domain: Option<Arc<dyn Domain>>) -> Self {
        let mut domains = HashMap::new();
        let mut domains_by_name = HashMap::new();
        if let Some(default_domain) = default_domain.as_ref() {
            domains.insert(default_domain.domain_id(), Arc::clone(default_domain));

            domains_by_name.insert(
                default_domain.domain_name().to_string(),
                Arc::clone(default_domain),
            );
        }

        Self {
            tabs: RefCell::new(HashMap::new()),
            windows: RefCell::new(HashMap::new()),
            default_domain: RefCell::new(default_domain),
            domains_by_name: RefCell::new(domains_by_name),
            domains: RefCell::new(domains),
            subscribers: RefCell::new(HashMap::new()),
            tmux_domains: RefCell::new(HashMap::new()),
        }
    }

    pub fn subscribe(&self) -> anyhow::Result<MuxSubscriber> {
        let sub_id = SUB_ID.fetch_add(1, Ordering::Relaxed);
        let (tx, rx) = pollable_channel()?;
        self.subscribers.borrow_mut().insert(sub_id, tx);
        Ok(rx)
    }

    pub fn notify(&self, notification: MuxNotification) {
        let mut subscribers = self.subscribers.borrow_mut();
        subscribers.retain(|_, tx| tx.send(notification.clone()).is_ok());
    }

    pub fn default_domain(&self) -> Arc<dyn Domain> {
        self.default_domain
            .borrow()
            .as_ref()
            .map(Arc::clone)
            .unwrap()
    }

    pub fn set_default_domain(&self, domain: &Arc<dyn Domain>) {
        *self.default_domain.borrow_mut() = Some(Arc::clone(domain));
    }

    pub fn get_domain(&self, id: DomainId) -> Option<Arc<dyn Domain>> {
        self.domains.borrow().get(&id).cloned()
    }

    pub fn get_domain_by_name(&self, name: &str) -> Option<Arc<dyn Domain>> {
        self.domains_by_name.borrow().get(name).cloned()
    }

    pub fn add_tmux_domain(&self, tab_id: TabId, domain: &Arc<dyn Domain>) {
        self.tmux_domains
            .borrow_mut()
            .insert(tab_id, Arc::clone(domain));
        self.add_domain(domain);
    }

    pub fn tmux_domain_for_tab(&self, tab_id: TabId) -> Option<Arc<dyn Domain>> {
        self.tmux_domains.borrow().get(&tab_id).cloned()
    }

    pub fn add_domain(&self, domain: &Arc<dyn Domain>) {
        if self.default_domain.borrow().is_none() {
            *self.default_domain.borrow_mut() = Some(Arc::clone(domain));
        }
        self.domains
            .borrow_mut()
            .insert(domain.domain_id(), Arc::clone(domain));
        self.domains_by_name
            .borrow_mut()
            .insert(domain.domain_name().to_string(), Arc::clone(domain));
    }

    pub fn set_mux(mux: &Rc<Mux>) {
        MUX.with(|m| {
            *m.borrow_mut() = Some(Rc::clone(mux));
        });
    }

    pub fn get() -> Option<Rc<Mux>> {
        let mut res = None;
        MUX.with(|m| {
            if let Some(mux) = &*m.borrow() {
                res = Some(Rc::clone(mux));
            }
        });
        res
    }

    pub fn get_tab(&self, tab_id: TabId) -> Option<Rc<dyn Tab>> {
        self.tabs.borrow().get(&tab_id).map(Rc::clone)
    }

    pub fn add_tab(&self, tab: &Rc<dyn Tab>) -> Result<(), Error> {
        self.tabs.borrow_mut().insert(tab.tab_id(), Rc::clone(tab));

        let reader = tab.reader()?;
        let tab_id = tab.tab_id();
        thread::spawn(move || read_from_tab_pty(tab_id, reader));

        Ok(())
    }

    pub fn remove_tab(&self, tab_id: TabId) {
        debug!("removing tab {}", tab_id);
        self.tabs.borrow_mut().remove(&tab_id);
        self.prune_dead_windows();
    }

    pub fn prune_dead_windows(&self) {
        let live_tab_ids: Vec<TabId> = self.tabs.borrow().keys().cloned().collect();
        let mut windows = self.windows.borrow_mut();
        let mut dead_windows = vec![];
        for (window_id, win) in windows.iter_mut() {
            win.prune_dead_tabs(&live_tab_ids);
            if win.is_empty() {
                dead_windows.push(*window_id);
            }
        }

        let dead_tab_ids: Vec<TabId> = self
            .tabs
            .borrow()
            .iter()
            .filter_map(|(&id, tab)| if tab.is_dead() { Some(id) } else { None })
            .collect();

        for tab_id in dead_tab_ids {
            self.tabs.borrow_mut().remove(&tab_id);
        }

        for window_id in dead_windows {
            error!("removing window {}", window_id);
            windows.remove(&window_id);
        }
    }

    pub fn kill_window(&self, window_id: WindowId) {
        let mut windows = self.windows.borrow_mut();
        if let Some(window) = windows.remove(&window_id) {
            for tab in window.iter() {
                self.tabs.borrow_mut().remove(&tab.tab_id());
            }
        }
    }

    pub fn get_window(&self, window_id: WindowId) -> Option<Ref<Window>> {
        if !self.windows.borrow().contains_key(&window_id) {
            return None;
        }
        Some(Ref::map(self.windows.borrow(), |windows| {
            windows.get(&window_id).unwrap()
        }))
    }

    pub fn get_window_mut(&self, window_id: WindowId) -> Option<RefMut<Window>> {
        if !self.windows.borrow().contains_key(&window_id) {
            return None;
        }
        Some(RefMut::map(self.windows.borrow_mut(), |windows| {
            windows.get_mut(&window_id).unwrap()
        }))
    }

    pub fn get_active_tab_for_window(&self, window_id: WindowId) -> Option<Rc<dyn Tab>> {
        let window = self.get_window(window_id)?;
        window.get_active().map(Rc::clone)
    }

    pub fn new_empty_window(&self) -> WindowId {
        let window = Window::new();
        let window_id = window.window_id();
        self.windows.borrow_mut().insert(window_id, window);
        window_id
    }

    pub fn add_tab_to_window(&self, tab: &Rc<dyn Tab>, window_id: WindowId) -> anyhow::Result<()> {
        let mut window = self
            .get_window_mut(window_id)
            .ok_or_else(|| anyhow!("add_tab_to_window: no such window_id {}", window_id))?;
        window.push(tab);
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.tabs.borrow().is_empty()
    }

    pub fn iter_tabs(&self) -> Vec<Rc<dyn Tab>> {
        self.tabs
            .borrow()
            .iter()
            .map(|(_, v)| Rc::clone(v))
            .collect()
    }

    pub fn iter_windows(&self) -> Vec<WindowId> {
        self.windows.borrow().keys().cloned().collect()
    }

    pub fn iter_domains(&self) -> Vec<Arc<dyn Domain>> {
        self.domains.borrow().values().cloned().collect()
    }

    pub fn domain_was_detached(&self, domain: DomainId) {
        self.tabs
            .borrow_mut()
            .retain(|_tab_id, tab| tab.domain_id() != domain);
        // Ideally we'd do this here, but that seems to cause problems
        // at the moment:
        // self.prune_dead_windows();
    }
}

#[derive(Debug, Error)]
#[allow(dead_code)]
pub enum SessionTerminated {
    #[error("Process exited: {:?}", status)]
    ProcessStatus { status: ExitStatus },
    #[error("Error: {:?}", err)]
    Error { err: Error },
    #[error("Window Closed")]
    WindowClosed,
}
