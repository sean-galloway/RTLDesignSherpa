# mc_* FUB extraction — knob inventory (Phase 2, Task 2)

Measured 2026-10-10. "changed" = `diff` lines between the two files;
"rock-named" = those that only mention the rock prefix (mechanical).
Canonical source for each common FUB = pumice's version (reference logic,
board-proven); parameters named from pumice's headers.

| FUB | pumice file | p↔s changed (rock-named) | s↔a changed (rock-named) | Class |
|---|---|---|---|---|
| bank_timer | `bank_timer.sv` (unprefixed) | 10 (7) | 39 (13) | knobs |
| bank_timers | `pumice_bank_timers.sv` | 22 (16) | 32 (18) | knobs |
| global_timers | `global_timers.sv` (unprefixed) | 12 (9) | 115 (13) | knobs — andesite adds DDR4 L/S pairs + BG windows as first-class counters ("ANDESITE L/S DELTA" comments), same one-next-state structure |
| wr_intake | `pumice_wr_intake.sv` | 22 (18) | 46 (25) | knobs |
| rd_intake | `pumice_rd_intake.sv` | 16 (13) | 37 (18) | knobs |
| wr_data_cam | `pumice_wr_data_cam.sv` | 18 (18) | 29 (12) | mechanical |
| rd_cmd_cam | `pumice_rd_cmd_cam.sv` | 25 (18) | 36 (14) | knobs |
| wr_splitter | `pumice_wr_splitter.sv` | 16 (16) | 34 (14) | mechanical |
| axi_burst_chopper | `pumice_axi_burst_chopper.sv` | 14 (14) | 45 (13) | knobs (BG fields for andesite) |

Classification rule (plan Task 2 Step 1): a delta is knob-class when it is
timing values, widths, or generation-gated features expressible as module
parameters with the full port union (unused inputs tied off); it is
architecture-class only if the control structure itself differs. None of
the nine is architecture-class on this measure. global_timers' L/S delta is
the largest: parameters `NUM_BG`/`BGW`/`HAS_LS_PAIRS` with pumice/scoria
using NUM_BG=1, HAS_LS_PAIRS=0 (L/S inputs tied to 0, outputs constant-1
ready), andesite using NUM_BG=4, HAS_LS_PAIRS=1.

## Deferred FUBs (not in this task)

refresh_ctrl, init_sequencer, mode_register, zq_ctrl, page_policy,
cmd_arbiter, addr_mapper, powerdown_ctrl, cmd_history_checker, lp_cal,
ca_train_ifc: their three-way diffs include protocol-specific behavior
beyond shape (command encodings, MR maps, LPDDR4 CA training), they are not
in the axi4/storage closure, and the two-customer rule can be revisited
per-FUB later. Recorded here so the deferral is explicit, not silent.

## Adoption-cycle verification ruling

Per-FUB adoption (within Task 2) is verified by: (a) the rock's verilator
lint PASS with exactly one definition of the module, (b) the FUB's own DV
test file(s) green at pre-extraction counts, (c) dependent compiles clean.
Full rock suites run once at Task 2 Step 5 (final gates), not per FUB —
nine FUBs times three rocks of 30-minute suites would bury signal. The
interaction risk a per-FUB suite would catch is caught at Step 5.

## Naming

`mc_<fub>.sv` under `common-ip/rtl/fub/`, one `.f` per FUB under
`common-ip/rtl/filelists/fub/`, all added to `mc_common_all.f`.
