# TASK-047: CXS pattern injector and checker

**Priority:** P2
**Status:** closed 2026-10-16
**Owner:** sean galloway

Owner 2026-10-16: CXS versions of the injectors the rapids FPGA systems use.

## Done

- rtl/amba/shared/cxs_master_injector.sv (axis4_master_injector -> axis_to_cxs
  -> cxs_master) and cxs_slave_pattern_check.sv (cxs_slave -> cxs_to_axis ->
  axis4_slave_pattern_check): CRCs bit-identical to the AXIS pair.
- val/amba/test_cxs_pattern_pair.py over tb_cxs_pattern_pair.sv: every AXIS
  pair scenario (incl. interleaved schedules) plus a wire CXSMonitor, link
  flags low, link reached RUN; 4x512, 2x256, 8x1024 (no 128: rule 6).
- Doc: docs/markdown/rtl-amba/shared/cxs_injectors.md.

## Not in scope

- Hooking them into a Genesys2 rapids-cxs harness build.
