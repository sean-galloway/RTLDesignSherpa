# TASK-006: .rdl regen gate extended from 1 block to 9
> **Was `TASK-088` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-24  **Priority:** Medium

`bin/check_rdl_regen.py` now carries 14 entries across 9 distinct RDLs:
stream_regs, rapids_regs, rapids_regmap, pumice_csr, obs_regs, tally_regs,
harness_csr_regs (Genesys2), chargen_regs, harness_csr (ddr2_char).

Every invocation determined EMPIRICALLY, never guessed. Two blocks this
task's own table missed: rapids has TWO RDLs describing DIFFERENT addrmaps
(`rapids_regs` vs `rapids`), and ddr2_char's `harness_csr.rdl` was unlisted.

**Semantic compare added** (opt-in 3-tuple; 2-tuples stay byte-exact).
`rapids_regmap.py` has a deliberately hand-written header, so byte comparison
would call it stale forever. Validated both ways: passes rapids (21 header
lines differ) and catches an injected register.

**One entry is regmap-only on purpose.** ddr2_char's `rtl/harness_csr.sv` is
HAND-WRITTEN (no PeakRDL banner, a fresh regen differs by 1787 lines, no
`_pkg.sv` tracked). Comparing it would declare hand-written RTL permanently
stale -- the false failure this gate must never cause.

**It caught a real defect on its first run:** rapids'
`regs/generated/docs/rapids_regs.md` was ~2900 lines stale (2416 -> 5316),
still describing a single register file when the RDL has described two halves
(SRC @ 0x0000 / SNK @ 0x1000) since the beats restructuring. Regenerated.

Validated: all 10 new entries dirtied one at a time, every one CAUGHT, all
restored. Full gate 4.0s (vs check_doc_examples.py 19.4s); hook no-op 0.03s.

NOT covered, carried forward as [[TASK-005]]: the RLB `--copy-rtl` family.

### Follow-up 2026-09-24 — coverage completed, three gaps closed

Audited after [[TASK-005]] landed, against every `.rdl` in the tree rather
than against the manifest's own list. Three things the "1 block to 9" and
"26 entries / 18 RDLs" claims did not cover:

1. **pumice_csr was entered TWICE.** This task and `4f8394ce3` added it
   independently within the hour -- same RDL, same flags, same compare
   targets, two copies. The gate ran those two invocations twice on every
   commit. De-duplicated (kept the version using a named path constant and
   carrying the ISSUE-003 rationale); 27 -> 25 entries, full gate 7.05s ->
   6.54s. A structural check now backs the name check: 0 duplicate
   (rdl, flags, regmap_output) triples and 0 files compared by two entries.

2. **The rapids entries did not list their transitive includes, so editing
   one was invisible to the gate.** `rapids_regs.rdl` and
   `rapids_regmap.rdl` both `include` `rapids_engine_regs.rdl`, which
   `include`s `rapids_mon_regs.rdl`; neither appeared in any `sources`, and
   `--staged` filters on `sources`. Proven by A/B rather than asserted:
   changing a real field default in `rapids_mon_regs.rdl` (TIMEOUT_CYCLES
   10000 -> 12345) and staging only that file exits **0** with the old
   sources and **1** with them added, flagging both rapids entries. This is
   the same class the `stream_mon_regs.rdl` source entry exists to prevent.
   (A first probe appended a trailing COMMENT and "passed" -- it changes no
   generated output, so exit 0 could not distinguish "ignored the file" from
   "checked and found nothing". The probe has to move an artifact.)

3. **cdc_demo_csr was unlisted.** Regmap-only, like ddr2_char's harness_csr:
   the demo tracks no generated RTL or docs. Invocation established
   empirically, regmap reproduces byte-for-byte, mutation-proven (a dirtied
   default exits 1 naming the entry).

**Every `.rdl` in the tree is now accounted for: 24 = 19 gated as entries + 3
reached as `sources` includes + 2 documented exclusions**, the exclusions
recorded in the manifest header so nobody re-derives them --
`misc/rdl/dma_address_gen.rdl` (a register DEFINITION; the `.sv` is
hand-written and only mentions PeakRDL in a comment) and
`bridge_pkg/peakrdl/bridge_cfg_proto.rdl` (a generator template, nothing
committed). 26 entries, full gate 6.99s.

Process note written up as [[regenerating-peakrdl-blocks]].

---
