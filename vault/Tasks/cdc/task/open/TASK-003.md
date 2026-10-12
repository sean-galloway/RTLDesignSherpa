# TASK-003: Add a dedicated val/cdc test root for cdc_synchronizer

**Priority:** P3
**Status:** open
**Owner:** TBD

`rtl/cdc/cdc_synchronizer.sv` has its own filelist (`rtl/cdc/filelists/cdc_synchronizer.f`) and is instantiated as a child in several project areas, but it is never the toplevel of a `val/cdc` test — the only coverage it gets is indirect, through `glitch_free_n_dff_arn` tests.

Found by the GTKW coverage audit (2026-10-12): it is the only `rtl/cdc` module without a dedicated test root.

## Done when
- `val/cdc/test_cdc_synchronizer.py` exists, follows the area's make/tests.mk grammar, and exercises reset + multi-bit crossing behavior
- gate/func/full levels wired like its neighbors (test_reset_sync.py is the closest template)
