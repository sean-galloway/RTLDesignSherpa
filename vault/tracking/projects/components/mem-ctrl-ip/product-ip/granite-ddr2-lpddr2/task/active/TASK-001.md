---
title: TASK-001 — granite first build (wrapper dissolution + product top)
summary: Dissolve the pumice layer wrappers into the common-ip layer macros, then compose the granite product top from common-ip only.
---

# TASK-001 — granite first build (wrapper dissolution + product top)

**State:** active · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-11

## Progress

**Done 2026-10-11 (commit 3dee3d1fb + fixups):**
1. Wrapper dissolution — `pumice_scheduler_layer` / `pumice_training_layer`
   deleted; their child composition moved INTO `mc_scheduler_layer` /
   `mc_training_layer` (parameters select the v2 child set; scoria/andesite
   keep their own children via the preserved external pass-through ports).
2. **granite_core.sv exists** — 758-line product top, and per the owner's
   ruling it has **NO mc_storage_layer**: a new common
   `mc_xddr2_entry_store` (N=1 in-order entry + write-data staging) closes
   the seam between `mc_axi4_layer` and `mc_scheduler_layer`. RAS layer
   absent. **Reduced refresh options**: `mc_xddr2_refresh_ctrl`
   parameterized — granite ties off postpone/pull-in/per-bank REFpb
   (fixed-tREFI REFab only); pumice keeps full options.
3. All four cores lint clean (pumice/scoria/andesite/granite, 0 warnings);
   registry check + audit PASS.

**Remaining:**
3. Product CSR baseline (`regs/granite_csr.rdl`, narrowed from pumice —
   no RAS decode beyond reserved, no research-harness knobs). — DONE (commit
   `3767b10ae`; verified 2026-10-12: all 66 register addresses + field
   offsets + defaults identical to pumice).
4. Board pick + frequency plan commit (timer CSRs derive from it). — DONE
   (Nexys A7-100T @ 75 MHz, `targets/granite`, `FLOW=ddr2_char`).

## A7 bring-up (2026-10-12)

**Done:**
- Bitstream builds clean: 30,453 LUT (48.0%), WNS +9.272 ns @ 75 MHz.
- init + training + maintenance path works on silicon (STATUS=0x1).
- **Fixed + committed (`3d690ab3f`):** `mc_xddr2_entry_store` write
  deadlock — early-arriving next-sub-burst W beats consumed fdone; the
  1-deep store deadlocked with zero DFI commands. Board now applies
  backpressure and recovers. Reproduced and verified in the new
  `granite_top_geared` cocotb smoke (true x16 geometry, NE=8,
  multi-outstanding mode).
- Second defect **precisely characterized, open**: multi-beat (split)
  bursts (blen>=2) wedge — sub-entries neither issue to the DFI nor emit
  the host B; blen=1 passes fully. Full evidence + next steps in
  `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/char_results/FINDINGS_granite_bringup_2026-10-11.md`.
  Next diagnostic: whole-harness granite UART sim (clone
  `ddr2_char_framework/dv/tests/test_ddr2_char_uart.py` onto
  `granite_char_harness`) — reproduces the real engines' AXI flavor that
  the passing BFM sim cannot.

## Acceptance (unchanged)

- `granite.f` elaborates a lint-clean `granite_core` with zero research-ip
  filelist references (registry audit proves it) — DONE.
- pumice lint + registry green after wrapper dissolution — DONE.
- Product config values that were TBD are committed or carry an explicit
  bring-up owner — pending steps 3-4.
