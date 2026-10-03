# TASK-005: scoria claims DFI v3.1 but omits three of its signal names

The HAS declares the PHY interface as **DFI v3.1**. Three signals the v3.1
control/data interface defines are not present on `scoria_top` under their DFI
names, which the DV repository's `DFISlavePHY` found by checking the required
set for the declared version and naming what was absent:

| DFI signal | version gating (measured) | scoria before | Severity |
|---|---|---|---|
| `dfi_reset_n` | **min 2.1**, gated on MEMORY TYPE (ddr3/4/5, lpddr4/5); renamed `dfi_reset` in v6.0 | exists as `dram_reset_n_o`, documented as "a device PIN" | naming only |
| `dfi_wrdata_cs_n` | **min 3.1, max 3.1** (renamed `dfi_wrdata_cs` in v4.0) | not driven | functional for multi-rank |
| `dfi_rddata_cs_n` | **min 3.1, max 3.1** (renamed `dfi_rddata_cs` in v4.0) | not driven | functional for multi-rank |

**Correction to this task's first version.** It said `dfi_reset_n` was a v3.1
addition ("DFI v3.1 carries DRAM RESET# as part of the control interface"). It
is not: measured against the DV framework's signal catalog
(`CocoTBFramework.components.dfi.dfi_signal_catalog`), `reset_n` is
`min_version=2.1` and gated on memory type rather than version. DFI has carried
it for DDR3 since 2.1 -- scoria simply never presented the DFI name. Only the
two data-phase selects are genuinely v3.1-specific, and they are v3.1-ONLY.

**The two selects have a SECOND role** the first version missed. The catalog
describes them as "Write-data chip select, active low (v3.0; also the
CS-under-training indicator during write leveling)" and the read-side
equivalent for read training. scoria HAS a write-leveling interface
(`scoria_wrlvl_ifc`, `dfi_phy_wrlvl_cs_n_o`), so that role is live -- it is
just degenerate at one rank, where the CS under training is always CS0. A
multi-rank scoria must drive these from the granted command's rank AND from the
rank being levelled.

**Priority:** P2 — nothing is wrong on the Genesys 2 board. `dfi_reset_n` is a
rename of a signal that is already there and already correct, and the two
per-data-phase selects are new in v3.1 for selecting a rank on the DATA phases;
with `NUM_RANKS=1` the only legal value is rank 0, which is what a PHY sees
whether scoria drives it or not.
**Status:** CLOSED 2026-10-03. RTL done 2026-10-01; the HAS text landed in
v0.8 (Ch 4.1) in the same pass that replaced the PRD stub. Found the same
day standing up `dv/tests/top/test_scoria_core.py`, where the BFM refused
to bind until all three were presented.

What changed in the RTL:

| | before | after |
|---|---|---|
| `dfi_reset_n` | `dram_reset_n_o`, documented as a device pin | **renamed** `dfi_reset_n_o` on `scoria_core`, `scoria_top`, `scoria_top_geared` |
| `dfi_wrdata_cs_n` | absent | driven, `'0` for NUM_RANKS=1 |
| `dfi_rddata_cs_n` | absent | driven, `'0` for NUM_RANKS=1 |

The rename stops at the DFI BOUNDARY. `scoria_init_sequencer` and
`scoria_mem_cmd_scheduler` keep `dram_reset_n_o`, which is the right name
there -- inside the controller it is device reset sequencing, and it becomes a
DFI signal at the module that presents the DFI bus. `scoria_core` connects
`.dram_reset_n_o (dfi_reset_n_o)` and says so.

The two data-phase selects are DRIVEN rather than left to the integrator, even
though a single-rank part admits only one value, because presenting them is the
controller's side of the v3.1 contract. A multi-rank scoria must drive them
from the granted command's rank, in step with `dfi_cs_n` -- noted at the port.

`dv/tb/scoria_core_tb.sv` lost its alias and its two tie-offs; all three are
plain DUT outputs now. Verified: lint PASS 54 modules, top tier 4/4 from a
clean build.

## Why each one matters, and why neither is urgent

`dfi_reset_n` is the interesting one, and not for the reason first written.
DFI carries DRAM RESET# on the command interface for DDR3 from v2.1 onward, so
ANY scoria DFI claim -- not just v3.1 -- implied this name. scoria had the
signal and drove it correctly; it called it `dram_reset_n_o` and described it
as a device pin rather than a DFI signal. That is a *documentation and
port-naming* discrepancy, not a missing feature -- but a PHY integrator wiring
to DFI will look for `dfi_reset_n` and not find it.

The same wrong belief was written down in the FPGA harness:
`projects/fpga-systems/Genesys2/scoria/rtl/scoria_char_macro.sv` said "RESET_n
is a real DRAM pin: the DFI spec carries no reset signal, so it leaves the
controller directly". Corrected in the same pass, with the catalog measurement
beside it.

`dfi_wrdata_cs_n` / `dfi_rddata_cs_n` are a real gap the day scoria gets a
second rank, and these two ARE v3.1-specific (min 3.1, max 3.1). scoria qualifies commands with `dfi_cs_n` on the command phases
only. v3.1 added the per-data-phase selects precisely because a multi-rank
system has to say which rank owns the DQ bus during the data window, and
scoria has nothing to drive there. Single rank hides it completely: the DV
wrapper ties both to 0 and the model is satisfied, because rank 0 is the only
answer.

## Where the workaround lives now

`dv/tb/scoria_core_tb.sv` aliases `phy_dfi_reset_n = dram_reset_n_o` and ties
`phy_dfi_wrdata_cs_n` / `phy_dfi_rddata_cs_n` to `'0`, with the reasoning in a
comment block. That is the right place for it while this is open -- it keeps
the DV wrapper honest about what scoria does and does not present -- but it
means the top-tier suite is not exercising those three as scoria signals.

## Done when

- [x] the ports are added/renamed and driven from the DUT
- [x] the alias and tie-offs come out of `dv/tb/scoria_core_tb.sv`
- [x] **the HAS is updated to match.** Done in HAS v0.8 (2026-10-03),
      Chapter 4.1: `dfi_reset_n` presented under its DFI name, the two
      data-phase selects listed as driven and constant `'0` at
      `NUM_RANKS = 1`, and the multi-rank requirement stated (drive them
      from the granted command's rank, in step with `dfi_cs_n`).

Multi-rank is a precondition for the second half: see also the rank handling in
`scoria_cmd_arbiter` (RK0 is hardcoded in the readiness terms).
