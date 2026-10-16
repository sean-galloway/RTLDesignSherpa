# TASK-006: cxs_intf_observer -- the CXS link observer

**Priority:** P2
**Status:** closed 2026-10-16
**Owner:** sean galloway

Owner 2026-10-16: CXS observers for the rapids FPGA systems.

## Done

- rtl/cxs_intf_observer.sv: axis4_intf_observer's shell (obs_regs, APB,
  arbiter, groups, telemetry) with per port a cxs_link_snoop -> cxs_monitor_lite
  tap and an axis_bus_meter mapped to CXS (productive = flit, backpressure =
  RUN with no credit, starvation = RUN with credit and no flit, idle = not
  RUN; flit-granular bytes). METRIC 17/18 = snoop credits / protocol error.
- dv/tests/fub/test_cxs_intf_observer.py (3/3): caps, exact meters on
  interleaved streams with backpressure only when throttled, Completion per
  packet, a forced no-credit flit caught as Error/PROTOCOL.
- Doc: docs/cxs_intf_observer.md.

## Not in scope

- Hooking it into a Genesys2 rapids-cxs harness build.
