<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# RAPIDS tasks — open (not started)

### TASK-057: Enforce register-map hygiene in RAPIDS DV (port the STREAM lessons)

**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

**Context:** STREAM had three register-map defects that a coverage/board
bring-up exposed on 2026-07-28/29 (fix: commit `729c774b` + the stream_top_tb
descriptor-fetch proof). RAPIDS is the sibling DMA under `dmas/` and almost
certainly shares the patterns — audit and fix all three:

- [ ] **Use the by-name regmap.** All RAPIDS DV must resolve registers through
  the peakrdl-emitted `rapids_regmap.py` (`RegisterMap` by name), never
  hardcoded APB offsets. STREAM's top TB kicked by hardcoded `0x000 + ch*8` and
  so never touched the regmap — a regmap break passed 8/8 top tests and only
  blew up in the cosims. Mirror the `stream_top_tb` fix (load the regmap in
  setup, resolve `_reg_addr(name)`).

- [ ] **Kick writes MUST look for descriptor reads.** The top/kick tests must
  assert that writing a kick register actually causes a descriptor FETCH —
  observe the descriptor-engine AR channel and prove the kicked descriptor
  address was read — not merely that data moved (a dead/mis-decoded kick path
  still "passes" a datapath-only check if src/dst happen to line up). See
  `stream_top_tb._watch_desc_fetches()` + `assert_descriptors_fetched()`.

- [ ] **No registers done by hand.** Every register must be DEFINED IN THE RDL
  (kick registers as WO, `sw=w; hw=na`, routed to apbtodescr by the cmdrsp
  decode). STREAM had 16 `CHx_CTRL` aliases hand-stuffed into `stream_regmap.py`
  while the RDL declared them "NOT defined here"; a regmap regen dropped them and
  broke every by-name consumer. Verify `rapids_regmap.py` has NO hand-added
  entries — anything a clean `bin/peakrdl_generate.py` run does not emit is a
  latent showstopper. (Regenerate via the bin wrapper only — see
  [[feedback_peakrdl_generate_bin]] equivalent.)

**Done when:** RAPIDS DV resolves every register by name from a regen-clean
`rapids_regmap.py`, the top/kick tests fail if a kick does not fetch a
descriptor, and no register is hand-added.
