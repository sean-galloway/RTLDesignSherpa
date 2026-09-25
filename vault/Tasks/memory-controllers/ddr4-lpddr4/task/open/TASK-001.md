# TASK-001: Advanced scheduling / refresh modes (from the DDR2 papers — see `../ADVANCED_MODES_ROADMAP.md`)
> Migrated 2026-09-25 from `projects/components/memory-controllers/ddr4-lpddr4/TASKS.md` (tooling TOOL-001). That file was a stub: "To be populated as RTL work begins."

**Priority:** P3 — there is no ddr4-lpddr4 RTL yet; this is the design-requirements survey that precedes it.
**Status:** open 2026-09-25 (carried forward unchanged from the stub)
**Owner:** TBD

Config-bit-selectable, OFF-by-default, faithful-DRAM-model red→green each; commodity here
because LPDDR4/DDR5 add controller-directed per-bank refresh + bank groups + FGR.

- [ ] **`refpb_ooo`** — out-of-order per-bank refresh (idle / lowest-queue bank, not round-robin). Commodity via LPDDR4 controller-directed per-bank refresh. *(Chang DARP #1)*
- [ ] **`refpb_wrp`** — write-refresh parallelization (REFpb the lowest-queue bank during a write-drain window). *(Chang DARP #2)*
- [ ] **`darp`** = `refpb_ooo` + `refpb_wrp`.
- [ ] **Refresh pausing** — pause a refresh bundle at `tRPC = tRFC/N` pause points, resume via a checkpointed row counter; forced-refresh at the `8×tREFI` deadline. **Research / model-only** (no JEDEC standard; needs a modified DRAM refresh FSM). *(Nair 2014)*
- [ ] **`sarp` / `dsarp`** — subarray access-refresh parallelism. **Research / model-only** (DRAM array microarchitecture). *(Chang SARP/DSARP)*
- [ ] **DDR4-native (new commodity):** Fine-Granularity Refresh (FGR 1x/2x/4x, MR3), bank-group scheduling (tCCD_L vs tCCD_S), commodity LPDDR4 per-bank refresh.
