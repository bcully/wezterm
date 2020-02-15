//! The tmux client control control protocol (tmux -CC)

use crate::mux::domain::{alloc_domain_id, Domain, DomainId, DomainState};
use crate::mux::tab::{Tab, TabId};
use crate::mux::window::WindowId;
use anyhow::bail;
use async_trait::async_trait;
use portable_pty::{CommandBuilder, PtySize};
use std::cell::RefCell;
use std::rc::Rc;

pub struct TmuxDomain {
    id: DomainId,
    #[allow(unused)]
    embedding_tab_id: TabId,
    line_buffer: RefCell<Vec<u8>>,
}

impl TmuxDomain {
    pub fn new(embedding_tab_id: TabId) -> Self {
        let id = alloc_domain_id();
        Self {
            id,
            embedding_tab_id,
            line_buffer: RefCell::new(vec![]),
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

            // TODO: something useful with this line
            log::error!(
                "TmuxDomain: {}",
                String::from_utf8_lossy(&line_buffer).escape_debug()
            );

            line_buffer.clear();
        } else {
            line_buffer.push(c);
        }
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
