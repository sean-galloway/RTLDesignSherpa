# TASK-044: CXS `_monlite` wrappers (a CXS ocelus core)

**Priority:** P3
**Status:** closed 2026-10-15
**Owner:** Sean (scope confirmed 2026-10-15: build the core + protocol code; no `_cg`, FPGA-only)

Shipped:
- `rtl/amba/ocelus/cxs_monitor_lite.sv` -- the CXS lite Ocelus (axis_monitor_lite's
  delivery contract: registered events, two picks/cycle, 4-deep unreset queue,
  drop-and-count, microsecond timeouts). Taps the FUB handshake and the endpoint's
  registered status, never the link pins.
- `PROTOCOL_CXS = 4'h6` in `ocelus_common_pkg`; event codes in
  `includes/ocelus_cxs_pkg.sv` (package `monitor_cxs_pkg`, not re-exported).
- `rtl/amba/cxs/cxs_{master,slave}_monlite.sv` (generated from the endpoint port
  lists); endpoints gained a `credit_starved` status output.
- Python decode: `bin/TBClasses/monbus` (ProtocolType, six CXS*Code enums, lookup,
  stats), checked against the SV by `bin/TBClasses/monbus/tests/test_monbus_cxs.py`.
- Tests: `val/amba/monitor-lite/test_cxs_{master,slave}_monlite.py` on the CXS grid,
  TB `bin/TBClasses/cxs/cxs_monlite_tb.py`. GATE 6/6, FUNC 16/16, FULL 24/24 from
  clean. Seven monitor mutations killed.
- Docs: `docs/markdown/rtl-amba/monitor/cxs_monitor_lite.md`,
  `includes/monitor_cxs_pkg.md`, package spec, wrappers Table 4, indexes.

Found on the way: the credit timeout read the previous episode's stamp on the first
starved cycle (false timeouts with a one-credit receiver) -- fixed, lesson in
`vault/handbook/design/registered-status-outputs.md`.
