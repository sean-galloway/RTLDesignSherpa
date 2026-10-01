# TASK-005: scoria claims DFI v3.1 but omits three of its signal names

The HAS declares the PHY interface as **DFI v3.1**. Three signals the v3.1
control/data interface defines are not present on `scoria_top` under their DFI
names, which the DV repository's `DFISlavePHY` found by checking the required
set for the declared version and naming what was absent:

| DFI v3.1 signal | scoria today | Severity |
|---|---|---|
| `dfi_reset_n` | exists as `dram_reset_n_o`, documented as "a device PIN" | naming only |
| `dfi_wrdata_cs_n` | not driven | functional for multi-rank |
| `dfi_rddata_cs_n` | not driven | functional for multi-rank |

**Priority:** P2 — nothing is wrong on the Genesys 2 board. `dfi_reset_n` is a
rename of a signal that is already there and already correct, and the two
per-data-phase selects are new in v3.1 for selecting a rank on the DATA phases;
with `NUM_RANKS=1` the only legal value is rank 0, which is what a PHY sees
whether scoria drives it or not.
**Status:** OPEN. Found 2026-10-01 standing up `dv/tests/top/test_scoria_core.py`,
where the BFM refused to bind until all three were presented.

## Why each one matters, and why neither is urgent

`dfi_reset_n` is the interesting one. DFI v3.1 carries DRAM RESET# as part of
the control interface, so a controller claiming v3.1 should present it by that
name. scoria has the signal and drives it correctly; it just calls it
`dram_reset_n_o` and describes it as a device pin rather than a DFI signal.
That is a *documentation and port-naming* discrepancy against the HAS, not a
missing feature -- but a PHY integrator wiring to the v3.1 contract will look
for `dfi_reset_n` and not find it.

`dfi_wrdata_cs_n` / `dfi_rddata_cs_n` are a real gap the day scoria gets a
second rank. scoria qualifies commands with `dfi_cs_n` on the command phases
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

Either the ports are added/renamed and the HAS updated to match, or the HAS
stops claiming unqualified v3.1 and states the deviation explicitly (which
signals, and that multi-rank needs the data-phase selects before it works).
Whichever way it lands, the alias and tie-offs come out of
`dv/tb/scoria_core_tb.sv` and the signals are driven from the DUT.

Multi-rank is a precondition for the second half: see also the rank handling in
`scoria_cmd_arbiter` (RK0 is hardcoded in the readiness terms).
