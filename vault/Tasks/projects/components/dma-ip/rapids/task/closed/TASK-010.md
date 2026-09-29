# TASK-010: 26 ASCII placeholder figures name dead signals; 2 figures have no test to capture from

**Priority:** P3. Cosmetic on art already marked for replacement -- but the
missing test sources are real.
**Status:** CLOSED 2026-09-27 (closing note at the end); was open 2026-09-26.

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

---

**Progress 2026-09-27.** Part B done: `dv/tests/fub_beats/test_axi_read_engine_beats.py`
and `test_axi_write_engine_beats.py` (TBs in `dv/tbclasses/`), AXI4 slave BFM + memory
model on the bus side, GAXI slave on the SRAM-fill side, level models for the scheduler and
SRAM ports; both found real RTL defects on their first run (rapids BUG-004, BUG-005).
Part A: 7 of the 26 placeholders replaced with generated waveforms (`assets/wavedrom/*.png`
+ `.json`, produced by `scratchpad/mkwave.py` over `bin/vcd2wavedrom2`, wavedrom-cli and
rsvg-convert): Figures 2.1.3, 2.2.3, 2.3.2, 2.4.2, 2.5.2, 2.6.2, 2.7.2. `TODO.md` rows
updated. Remaining 19 (ch01 1.1.4/1.3.1, ch02 2.9.3, ch03 3.3.3/3.4.3/3.5.2/3.6.3/3.7.3/3.8.2,
ch04 x6, HAS ch05 wavedrom) need macro/top-level wave captures; same recipe.

**Progress 2026-09-27 (later).** Part A now 12 of 26: added 1.1.4 (`rapids_core_beats_sink_kick`),
1.3.1 (`scheduler_reset`), 3.3.3 as three panels (`snk_data_path_fill_alloc`,
`snk_data_path_axi_write_aw`, `snk_data_path_axi_write_b`) and 3.4.3
(`snk_data_path_axis_ingress`), all cut from the core sink and scheduler dumps already on
disk. Remaining 14: 2.9.3 (ctrlwr doorbell), 3.5.2/3.8.2 (SRAM controller drain select),
3.6.3/3.7.3 (source path, AXIS egress), ch04 x6 interface figures, HAS ch05 wavedrom --
each needs its own WAVES=1 capture from the named test; recipe unchanged (mkwave.py).

## Closing note (2026-09-27)

Part A complete: all 26 placeholder figures are simulation-generated WaveDrom renders
(PNG plus WaveJSON under `docs/rapids_beats_mas/assets/wavedrom/`, each page naming
the test, configuration and level it was cut from). The last nine came from four
WAVES=1 captures made today: the core sink and source paths at 4 beats (AXI4 write
and read bursts, descriptor fetch, AXIS ingress and egress, the source transfer),
ctrlwr's doorbell, and the snk/src SRAM controllers' multi-channel drain selection;
the monbus group figure came from the basic_flow dump. Part B (the engine unit
tests) closed earlier today and found BUG-004/005. `TODO.md` carries the per-figure
table with sources. Two of the captures record behaviour worth knowing when reading
the pages: the source half's `system_idle` returns on the done strobe while words
are still draining to AXIS (the sink half waits for write commits), and the source
egress packetises per drain request, so `tlast` marks every beat when words arrive
singly.
