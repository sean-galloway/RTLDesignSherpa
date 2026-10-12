# TASK-042: Dedicated val/amba tests for monitor/monbus child modules without test roots

**Priority:** P3
**Status:** open
**Owner:** TBD

Thirty-one `rtl/amba` modules never appear as a DUT/toplevel in any val/amba test root (found by the GTKW coverage audit, 2026-10-12). Most get indirect exercise as children of tested monbus/monitor groups, but several are top-level-usable blocks with no coverage of their own:

- monitors/reporting: `axi_monitor_reporter`, `axi_monitor_reporter_compl`, `axi_monitor_reporter_debug`, `axi_monitor_reporter_error`, `axi_monitor_reporter_perf`, `axi_monitor_reporter_threshold`, `axi_monitor_reporter_timeout`, `axi_monitor_timeout`, `axi_monitor_timer`, `axi_monitor_trans_mgr`, `axis_monitor_lite`, `axi4ace_snoop_monitor_lite`
- monbus fabric: `monbus_arbiter`, `monbus_axi4_axi4_group`, `monbus_cam_pipe`, `monbus_group_core`, `monbus_halfbeat_packer`, `monbus_wb4_axi4_group`, `monbus_wb4_rd_shim`
- stubs: `apb4_master_cg`, `apb4_master_stub`, `apb4_slave_cg`, `apb4_slave_stub`, `axi4_master_stub`, `axi4_slave_stub`, `axi5_master_stub`, `axi5_slave_stub` (other protocols' stubs DO have dedicated tests — these are inconsistent)
- shared: `axis4_master_injector`, `axis4_slave_pattern_check`, `sdpram_core`, `wb4_retry`

## Done when
- at minimum: dedicated smoke tests for the stub family (consistency with axi4/axi5 stub coverage elsewhere) and `sdpram_core`/`axis_monitor_lite`
- the monbus fabric children are either covered by directed tests or explicitly documented as covered-by-parent
