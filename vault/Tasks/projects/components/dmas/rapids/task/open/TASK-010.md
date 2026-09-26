# TASK-010: 26 ASCII placeholder figures name dead signals; 2 figures have no test to capture from

**Priority:** P3. Cosmetic on art already marked for replacement -- but the
missing test sources are real.
**Status:** open 2026-09-26.

**Part A -- the placeholder figures.** 26 fenced ASCII figures across the MAS/HAS
books still label signals that no module has: `drain_gnt`, `drain_beats`,
`sram_rd_*`, `sram_wr_*`, `fill_last`, `drain_last`, `snk_fill_*`, `src_drain_*`,
`channel_empty/full`, `tkeep`. Measured 2026-09-26: 64 occurrences in plain
fences, 11 in wavedrom.

**Why relabelling was NOT done.** 13 of the 26 contain UTF-8 box-drawing and
overline glyphs (`│`, `└`, `‾`), so a label change shifts a waveform built from
multi-byte characters and the padding has to be reasoned in DISPLAY columns, not
bytes -- unverifiable from a diff. Every replacement is also longer
(`sram_wr_en` -> `axi_rd_sram_valid`, +7), and the box figures share a fixed right
border, so each needs full re-layout of ALL its rows, not just the changed ones.
And 21 of these pages carry `**TODO:** Replace with simulation-generated
waveform`, so the art is due for wholesale replacement anyway.

**Recommendation:** replace with generated waveforms rather than hand-relabel.
`docs/rapids_beats_mas/TODO.md` is the per-figure work list and its signal lists
and test citations were corrected in `d587852c2`, so a generation pass now has
correct inputs.

**Part B -- two figures cannot be generated at all.** `TODO.md` Figures 2.3.2
(AXI Read Burst) and 2.4.2 (AXI Write Burst) are marked `NONE YET`: **no test
under `dv/tests/` exercises `axi_read_engine_beats` or `axi_write_engine_beats`**.
Only the testplans and `rapids_coverage/coverage_config.py` name them. Either
write an engine-level test or drop the two figures.

**Also in wavedrom:** `monbus_pkt_type` at
`rapids_beats_has/ch05_programming/04_error_handling.md:217` is a DECODED FIELD of
`mon_packet` (bits [39:38] per `scheduler_beats.sv:993`), not a port. Correct as a
waveform row -- do not "fix" it to `mon_packet`.

**Related:** [[TASK-009]]
