use std::cell::RefCell;

use smithay_client_toolkit::{
    compositor::CompositorState,
    delegate_compositor, delegate_output, delegate_registry, delegate_shm, delegate_xdg_shell,
    delegate_xdg_window,
    output::{OutputHandler, OutputState},
    registry::{ProvidesRegistryState, RegistryState},
    registry_handlers,
    shell::xdg::XdgShell,
    shm::{slot::SlotPool, Shm, ShmHandler},
};
use wayland_client::{
    delegate_dispatch,
    globals::GlobalList,
    protocol::{wl_output::WlOutput, wl_surface::WlSurface},
    Connection, QueueHandle,
};

use super::SurfaceUserData;

// We can't combine WaylandState and WaylandConnection together because
// the run_message_loop has &self(WaylandConnection) and needs to update WaylandState as mut
pub(super) struct WaylandState {
    registry: RegistryState,
    pub(super) output: OutputState,
    pub(super) compositor: CompositorState,
    pub(super) xdg: XdgShell,

    shm: Shm,
    pub(super) mem_pool: RefCell<SlotPool>,
}

impl WaylandState {
    pub(super) fn new(globals: &GlobalList, qh: &QueueHandle<Self>) -> anyhow::Result<Self> {
        let shm = Shm::bind(&globals, qh)?;
        let mem_pool = SlotPool::new(1, &shm)?;
        let wayland_state = WaylandState {
            registry: RegistryState::new(globals),
            output: OutputState::new(globals, qh),
            compositor: CompositorState::bind(globals, qh)?,
            xdg: XdgShell::bind(globals, qh)?,
            shm,
            mem_pool: RefCell::new(mem_pool),
        };
        Ok(wayland_state)
    }
}

impl ProvidesRegistryState for WaylandState {
    fn registry(&mut self) -> &mut RegistryState {
        &mut self.registry
    }

    registry_handlers!(OutputState);
}

impl ShmHandler for WaylandState {
    fn shm_state(&mut self) -> &mut Shm {
        &mut self.shm
    }
}

impl OutputHandler for WaylandState {
    fn output_state(&mut self) -> &mut OutputState {
        &mut self.output
    }

    fn new_output(&mut self, _conn: &Connection, _qh: &QueueHandle<Self>, _output: WlOutput) {
        log::trace!("new output: OutputHandler");
    }

    fn update_output(&mut self, _conn: &Connection, _qh: &QueueHandle<Self>, _output: WlOutput) {
        log::trace!("update output: OutputHandler");
        todo!()
    }

    fn output_destroyed(&mut self, _conn: &Connection, _qh: &QueueHandle<Self>, _output: WlOutput) {
        log::trace!("output destroyed: OutputHandler");
        todo!()
    }
}
// Undocumented in sctk 0.17: This is required to use have user data with a surface
// Will be just delegate_compositor!(WaylandState, surface: [SurfaceData, SurfaceUserData]) in 0.18
delegate_dispatch!(WaylandState: [ WlSurface: SurfaceUserData] => CompositorState);

delegate_registry!(WaylandState);

delegate_shm!(WaylandState);

delegate_output!(WaylandState);
delegate_compositor!(WaylandState);

delegate_xdg_shell!(WaylandState);
delegate_xdg_window!(WaylandState);