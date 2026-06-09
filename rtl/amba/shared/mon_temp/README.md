# mon_temp/ — Staging area for the CAM-backed monitor rewrite

This directory holds in-progress versions of the AXI monitor RTL that
move the per-transaction keying + payload storage out of inline
`always_ff` blocks and into the shared `monitor_trans_cam` module
(see `../monitor_trans_cam.sv`).

**Not on the synth path.** Nothing here is referenced from any
`rtl/amba/filelists/*.f`. Verilator's `-y rtl/amba/shared` is
non-recursive so it will not pick these files up by accident. The
production modules in `rtl/amba/shared/` are still authoritative.

When a staged module reaches functional + timing parity with its
production sibling, the swap is a single filelist edit:

```
- $REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
+ $REPO_ROOT/rtl/amba/shared/mon_temp/axi_monitor_trans_mgr.sv
+ $REPO_ROOT/rtl/amba/shared/monitor_trans_cam.sv
```

Module names mirror the production names so the swap doesn't require
hierarchy edits in the parents (e.g. `axi_monitor_base.sv`).

## Status

| Module                   | Source        | Status      |
|--------------------------|---------------|-------------|
| `axi_monitor_trans_mgr.sv` | this dir    | passes differential equivalence + full `axi4_master_rd_mon` regression (2026-06-08) |

## How to validate

Two layers of confidence, both passing today:

1. **Bit-exact differential equivalence** (500 cycles random stim, all
   `bus_transaction_t` fields cross-checked):

   ```
   pytest val/amba/test_axi_monitor_trans_mgr_equiv.py -v
   ```

   Two pytest entries: `test_a_*_prod` captures cycle-by-cycle outputs
   from the production trans_mgr; `test_b_*_stage` runs the same
   stimulus against the staging file and asserts every snapshot
   matches. FULL sweep covers AXI4/AXI-Lite read + write, MAX_TRANS
   8/16, ID_WIDTH 4/8.

2. **Full monitor regression with the swap flipped** (env-var knob):

   ```
   # Default: production trans_mgr
   pytest val/amba/test_axi4_master_rd_mon.py -v

   # Same regression, staging trans_mgr + monitor_trans_cam
   TRANS_MGR_VARIANT=stage pytest val/amba/test_axi4_master_rd_mon.py -v
   ```

   The `_trans_mgr_sources(rtl_dict)` helper in
   `test_axi4_master_rd_mon.py` swaps the source set based on the
   `TRANS_MGR_VARIANT` env var (`prod` default, `stage` opt-in). Other
   monitor regression test files (`test_axi4_master_wr_mon.py`,
   `test_axi4_slave_*_mon.py`, `*_cg.py`, the enable-sweep) still pin
   the production file -- copy the helper to extend the swap there.
