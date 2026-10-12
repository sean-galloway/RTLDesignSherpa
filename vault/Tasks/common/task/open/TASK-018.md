# TASK-018: Dedicated val/common tests for utility modules with no test root

**Priority:** P3
**Status:** open
**Owner:** TBD

Five `rtl/common` modules never appear as a `dut_name`/toplevel in any `val/common/test_*.py`:

- `arbiter_single_client` — `rtl/common/arbiter_single_client.sv`
- `dataint_crc_xor_shift` — `rtl/common/dataint_crc_xor_shift.sv`
- `dataint_crc_xor_shift_cascade` — `rtl/common/dataint_crc_xor_shift_cascade.sv`
- `fifo_control` — `rtl/common/fifo_control.sv`
- `icg` — `rtl/common/icg.sv`

Note: `.gtkw` views for `dataint_crc_xor_shift`, `dataint_crc_xor_shift_cascade`, `fifo_control`, and `icg` exist in `val/common/GTKW/`, but those were produced from other areas' runs — a saved view is not a dedicated area test. Found by the GTKW coverage audit (2026-10-12).

## Done when
- each module has a `val/common/test_<name>.py` root wired into the area Makefile grammar
