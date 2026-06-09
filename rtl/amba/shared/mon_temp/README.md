# mon_temp/ — Parked legacy versions of monitor RTL

This directory holds previous-generation revisions of monitor modules
that have been superseded in production but are kept available for
rollback, timing comparison, and synth-shape investigation.

**Not on the synth path.** Nothing here is referenced from any
`rtl/amba/filelists/*.f`. Verilator's `-y rtl/amba/shared` is
non-recursive so it will not pick these files up by accident. The
production modules in `rtl/amba/shared/` are authoritative.

## Status

| File | Role | Notes |
|---|---|---|
| `axi_monitor_trans_mgr.sv` | legacy in-place revision (pre-CAM, 2026-04-23 refactor) | superseded 2026-06-08 by the CAM-backed version at `rtl/amba/shared/axi_monitor_trans_mgr.sv` |

## How to roll back / compare

The active monitor regressions accept a `TRANS_MGR_VARIANT` env-var
knob that picks between the CAM-backed (default) and the legacy
in-place revision parked here:

```bash
# Default: CAM-backed trans_mgr
pytest val/amba/test_axi4_master_rd_mon.py -v

# Roll back to the legacy in-place revision
TRANS_MGR_VARIANT=legacy pytest val/amba/test_axi4_master_rd_mon.py -v
```

The other `*_mon` tests in `val/amba/` always include
`monitor_trans_cam.sv` in their source lists (the current production
trans_mgr depends on it). Adding the same knob to those tests is a
~30-line copy of the `_trans_mgr_sources(rtl_dict)` helper from
`test_axi4_master_rd_mon.py` if you want to flip them too.

## Differential equivalence

`val/amba/test_axi_monitor_trans_mgr_equiv.py` runs 500 cycles of
deterministic random stimulus against both builds and asserts every
field of `trans_table` matches bit-exact every cycle. FULL sweep
covers AXI4/AXI-Lite × read/write × MAX_TRANS 8/16 × ID_WIDTH 4/8
(6 configs × 2 builds = 12 tests). This is the primary parity gate;
the per-monitor regressions are supplementary coverage of the full
monitor stack with realistic stimulus.
