# TASK-019: the byte-granular RAPIDS -- lengths in bytes, AXI4 byte enables, partial AXIS beats

**Priority:** P1 -- the beats architecture was always the first step, not the
product. Sean, 2026-09-29: "begin looking into the actual version of rapids
where bytes are counted, BYTE ENABLES are used on AXI4 and there could be a
single byte written on AXIS4."
**Status:** ACTIVE 2026-09-29. First cut committed (2bc82c2c3): the
un-suffixed tree lints, and its fub, macro and top gate suites pass (see
"Design as built" and "Verification record" below). Still open: the FPGA
harness variant for the byte build, the HAS/MAS chapters, EXT descriptors
with byte offsets, the full-level regressions.

**Intent (Sean, 2026-09-29):** "The intent was always for rapids to be byte
access. The beats version was a stepping stone. This is why there are
fub/macro-beats areas." So the byte version is not an edit of the beats
tree. It is the product RAPIDS and it lands in the un-suffixed areas that
were reserved for it: `rtl/fub/` (today only `ctrlrd_engine`,
`ctrlwr_engine`, shared by both), `rtl/macro/` (today only
`monbus_axil_group_2in`, shared), and a new `rtl/top/`, with `dv/tests/fub`,
`dv/tests/macro`, `dv/tests/top` and un-suffixed TB classes beside them.
`fub_beats/`, `macro_beats/`, `top_beats/` stay intact as the working
reference and the characterized design (BUG-009 closure, perf report v2.2,
the three FPGA books). Byte-version modules take the beats module's name
without the `_beats` suffix, and BUG-009's lessons (AxLEN clamp, partial
allocation, the settle window) carry over on day one.

## Where bytes stand today (beats RTL, 256-bit, Genesys 2)

| Place | Today | Consequence |
|---|---|---|
| descriptor `length` [159:128] | beats (HAS ch05, `rapids_pkg::descriptor_t`); software rounds bytes up | a transfer is a whole number of 32-byte beats; a 5-byte payload moves 32 |
| `src_addr`, `dst_addr` | must be `DATA_WIDTH/8`-aligned (HAS: "unaligned addresses may cause AXI protocol violations") | no byte offset anywhere |
| sink `s_axis_tstrb` | a port on `rapids_beats_top`; `snk_data_path_axis_beats` does not forward it, the fill interface and `sram_controller` carry `DW` only | strobes are dropped at the door; a one-byte AXIS beat is stored as a full beat |
| sink `m_axi_wstrb` | `axi_write_engine_beats.sv:772`: all ones | every W beat writes all 32 bytes, whatever arrived |
| source `m_axis_tstrb` | `src_data_path_axis_beats.sv:352`: all ones | the egress stream never marks a partial beat |
| top-level byte counter | `rapids_beats_top.sv:671` sums `$countones(m_axi_wr_wstrb)` | correct machinery, always counts full beats today |
| harness generator | `axis4_master_pattern_gen.sv:282`: `tstrb` all ones | cannot produce a partial beat |
| harness checker | `axis4_slave_pattern_check` takes `s_axis_tstrb` and does not use it | cannot check one |
| harness write CRC | `axi4_slave_wr_crc_check` passes `wstrb` through to the memory model only; the CRC hashes the full data word | a partial beat would CRC bytes that were never written |
| golden model | `rapids_char_golden.py` hashes whole 32-bit words | no byte-wise reference |
| AXIS meters and observer | count bytes as `popcount(tstrb)` per productive beat | already byte-correct; they would show partial beats as lower bytes per beat |
| HAS `ch01_overview/03_system_context.md` | "TKEEP/TSTRB supported for partial beat handling" | not true of the RTL; the MAS AXIS spec also names `tkeep` where the ports are `tstrb` |

## What existed before, and what is still lying around

The pre-beats RAPIDS (`projects/components/rapids/rtl/rapids_fub/*`, removed
in 3c308050b, 2026-01-11: "getting it going first on a beat boundary, as in
stream. Will create new versions of the required fubs working on a chunk
boundary after this is all clean") counted in **4-byte chunks**, not bytes.
Its scheduler computed an `alignment_info_t` per descriptor and drove the
engines through three phases (align to the 64-byte boundary, stream full
beats, final partial beat) with 16-bit chunk enables that became `wstrb`,
and it narrowed AWSIZE/ARSIZE to 4 bytes in the edge phases
(`sink_axi_write_engine.sv` lines 180-236 at that commit).
`docs/ADDRESS_INCREMENT_PATTERNS.md` section 2 and 4.2 describe that scheme.

The helpers survive, unused: `rapids_pkg.sv` still carries
`RAPIDS_NUM_CHUNKS`, `alignment_info_t`, `bytes_to_chunks`,
`chunks_to_bytes`, `bytes_to_boundary`, `generate_chunk_enables`,
`select_alignment_strategy` and `calculate_efficiency` (lines ~225-450).
Nothing in the beats RTL calls them; `dv/tests/README.md` and
`snk_datapath_beats_tb.py` still mention them. They are a starting point for
the byte version's arithmetic, once generalized from 4-byte chunks to bytes
and from a 64-byte beat to `DATA_WIDTH/8`.

## What the byte version has to do

1. **Descriptor.** `length` in bytes; `src_addr` and `dst_addr` byte-granular
   with no alignment requirement. The extended descriptor's strides are
   already signed bytes, so the row/column generator is consistent once the
   base length is bytes too. The scheduler derives per-descriptor: first-beat
   byte offset, whole beats, last-beat byte count; its beat accounting
   (`sched_*_beats`, `beats_done`, commit) stays in beats above that.
2. **Sink data path.** Carry `tstrb` from `s_axis` through the fill
   interface into the SRAM (`DW + DW/8` per entry: 4 KB becomes 4.5 KB per
   channel, 12.5 % more BRAM bits) and out through the drain to
   `m_axi_wstrb`. A one-byte AXIS beat becomes one W beat with one strobe
   bit. AXI4 allows sparse `wstrb` within a full-size beat and an INCR burst
   from an unaligned address, so the pre-beats trick of narrowing AWSIZE for
   the edge phases is not needed; the first beat's low lanes are masked from
   the address offset and the last from the remaining byte count. Where the
   SINK's `tlast` packets and the descriptor's byte length disagree is a
   contract to write down (a packet shorter than the descriptor, a packet
   spanning descriptors).
3. **Source data path.** AXI reads carry no strobes, so the source knows the
   valid bytes of a beat only from the address and the remaining length: it
   must set `m_axis_tstrb` on the first and last beats from those. The
   design decision here is whether the stream wants the bytes **where the
   address put them** (lane = address low bits, sparse `tstrb`, no data
   movement) or **packed from lane 0** (a byte-realignment shifter on the
   egress, the expensive option). Most AXIS consumers expect packed data;
   the sink would then need the mirror shifter on ingress if the memory
   address is unaligned.
4. **Counting.** `r_wr_bytes` at the top already counts strobed bytes; add
   the read side (bytes from address and length, since R has no strobes),
   and give the harness and report a bytes-per-beat efficiency beside
   utilization, because a byte-granular transfer can sit at 100 % beat
   utilization while moving one byte per beat.
5. **Harness.** `axis4_master_pattern_gen` needs a partial-beat mode
   (byte length per packet, a chosen last-beat `tstrb`, and a first-beat
   offset if packed data is not the contract) with the LFSR and CRC advanced
   per valid byte, not per beat; `axis4_slave_pattern_check` must honour
   `tstrb` the same way; `axi4_slave_wr_crc_check` must CRC only strobed
   bytes (verified 2026-09-29: it forwards `wstrb` to the memory model and
   hashes the whole word); the golden model follows. `run_characterization.py`
   gains byte lengths and offsets as knobs, and the report gains the
   efficiency column.
6. **Monitors and observers.** The AXIS observer's `STRB_INVALID` error
   fires on an all-zero `tstrb` beat and its byte counts are already right.
   The in-core AXIS monitor-lites need nothing new. The AXI write monitor's
   byte accounting, if any, should be checked against `wstrb`.
7. **Docs.** HAS ch05 (descriptor), ch01 (the false TKEEP claim), MAS AXIS
   spec (`tkeep` vs `tstrb`), `ADDRESS_INCREMENT_PATTERNS.md` (chunk phases
   become byte phases), the register descriptions if any length register
   changes, all in the same pass as the RTL.
8. **Tests, RED first.** Unit: the write engine drives `wstrb` from stored
   strobes; the ingress forwards `tstrb`; the source marks first and last
   beats. Macro: sink and source with unaligned addresses, lengths not a
   multiple of the beat, and one-byte packets. Harness sim and board:
   byte-length campaign rows with the byte-wise golden CRC. STREAM stays
   beat-granular by design (tutorial), so its tests do not change.

## Decisions needed before RTL

- [x] Packed egress: the stream carries bytes from lane 0, a byte shifter
      on both halves (source egress, sink ingress). Decided 2026-09-29.
- [x] Descriptor `length` in bytes in the existing 32-bit field; `src_addr`
      and `dst_addr` byte-granular, no separate offset field. Decided
      2026-09-29.
- [x] SINK contract, first cut: a `tlast` packet equals the descriptor byte
      length; a mismatch raises an error event and is never silently padded.
      Decided 2026-09-29.
- [x] `DATA_WIDTH` = 256 for the first byte-granular build so every existing
      perf cell stays comparable. Decided 2026-09-29.
- [x] TYPE=EXT (row/column striding) stays beat-aligned: aligned addresses,
      beat-multiple lengths. Permanent, decided 2026-09-30.
- [x] Where it lives: the un-suffixed `rtl/fub`, `rtl/macro`, `rtl/top`
      areas; the beats tree is kept, not converted (Sean, 2026-09-29).

## Design as built (2026-09-29, first cut)

The byte tree is a clone of the beats tree (module names without `_beats`,
`rapids_beats_top` -> `rapids_top`; `rapids_config_block` and the regs stay
shared) with these changes:

- **Scheduler** (`rtl/fub/scheduler.sv`): `length` is bytes; a direction moves
  `ceil((addr[OFF_W-1:0] + length) / BYTE_LANES)` beats (zero length moves
  none); addresses advance aligned-down plus beats after the first burst; a
  DATA descriptor leaving `CH_FETCH_DESC` pulses a **packet record**
  `{bytes, offset}` per enabled direction (`sched_rd_pkt_*`, `sched_wr_pkt_*`)
  and waits there while the data path's record queue (depth 4 per channel)
  is full. EXT descriptors keep beat-granular rows: TYPE=EXT requires
  beat-aligned addresses and beat-multiple lengths. **Permanent** (Sean,
  2026-09-30: "That is an acceptable permanent limitation"); linear
  descriptors have no alignment requirement.
- **Engines**: AWADDR/ARADDR are issued **beat-aligned** (the offset lives in
  the strobes), every burst is capped at the 4 KB boundary, and the write
  engine drives WSTRB from a new `axi_wr_sram_strb` input. AXI4 would also
  allow an unaligned first address; aligned was chosen so every slave and
  BFM sees the same thing and the strobes alone carry the byte truth.
- **Sink ingress** (`snk_data_path_axis.sv`): a barrel shifter places packed
  stream bytes at `offset + lane`, holds the spill for the next memory beat,
  flushes it after `tlast`, and stores `{strb, data}` in the SRAM
  (`DATA_WIDTH + DATA_WIDTH/8` wide). **Contract:** the ingress holds
  `s_axis_tready` low until the channel's packet record exists, so software
  issues the descriptor before or concurrently with the stream (the beats
  design buffered data first; the beat-era tests were changed to send
  descriptors first or stream in the background). A `tlast` packet whose
  byte count differs from the record sets the channel's sticky
  `sched_wr_error` bit.
- **Source egress** (`src_data_path_axis.sv`): pops memory beats, drops the
  offset bytes of the first, re-packs from lane 0, marks the last beat with a
  contiguous `tstrb` and `tlast`. **Packets follow descriptors**, not drain
  reservations (the beats design cut a descriptor into `cfg_drain_size`
  packets); the AXIS monitor completion counts change accordingly.
- **Tests** (`dv/tests/fub`, `macro`, `top`): the cloned beat-era suites run
  unchanged with lengths scaled to bytes in the TB descriptor builders, plus
  byte-specific cells: engine `strobes`/`unaligned`/`split4k`, scheduler
  `byte_lengths`/`pkt_backpressure`/`zero_length`, macro `byte_packets` on
  both halves (one byte, straddling beats, long unaligned, a 4 KB crossing,
  the length-mismatch contract).

## Board harness: its own Genesys 2 area (2026-09-30)

Sean: "In the genesys2 area create a rapids area separate from the
rapids-beats area." `projects/fpga-systems/Genesys2/rapids/` is that area:
`flows-rapids/` mirrors `flows-rapids-beats/` (same bench, UART host flow,
golden-CRC method), renamed `rapids_byte_*`, harness ID `RAPB`, built around
`rapids_top` only. The beats area is untouched except for one tie-off line
(the shared AXIS generator gained a `cfg_last_bytes` input) and a stale
observer-regmap path (`components/misc` -> `components/utility-ip/misc`)
that had broken its host readout independently of this task.

What the byte harness adds, all additive on the shared blocks:

- `axis4_master_pattern_gen.cfg_last_bytes`: the tlast beat of every packet
  carries that many strobed bytes (0 = all), so a packet of N bytes is
  ceil(N / lanes) beats with a partial last beat. CSR `GEN_LASTB` (0x02C).
- `axis4_slave_pattern_check` and `axi4_slave_wr_crc_check` parameter
  `BYTE_CRC` (default 0 keeps STREAM's harness byte-identical): the
  per-channel CRC runs over the strobed bytes in lane order, four bytes per
  cycle through `dataint_crc`'s cascade_sel, holding ready while a beat is
  fed. A one-byte transfer is checked as one byte. The word compare is
  replaced by a tstrb-contiguity check.
- Host: `BUILD.BYTE_DUT` (bit 27) tells the host which DUT it talks to; the
  beat campaigns scale beats to bytes and score against byte-wise goldens;
  `--byte-smoke` / `--bytes N --offset K` run byte campaigns on both halves.
  `rapids_byte_golden.py` gains `golden_sink_bytes` (the packet stream) and
  `golden_source_bytes` (memory beats re-packed from the offset).
- Sim: `make sim` in the new area runs the beat campaigns on the byte DUT
  plus four byte cases (1 B at 1, 77 B at 5, 33 B at 31, 203 B across a
  4 KB boundary).

## Verification record

| Run (from `make clean-all`) | Result |
|---|---|
| clone before any byte edit, gate: fub / macro / top | 64/0, 179/0, 12/0 (equal to the beats areas) |
| lint, both trees | 86/86 modules |
| byte engines gate: axi_write_engine, axi_read_engine | 7/0, 7/0 (incl. strobes, split4k / unaligned, split4k) |
| byte scheduler gate (`scheduler*`) | 17/0 (incl. byte_lengths, pkt_backpressure, zero_length) |
| byte macro gate: snk / src data path axis test | 56/0, 64/0 (incl. byte_packets) |
| byte top gate: rapids_top / rapids_core | 12/0 (incl. source_bytes, sink_bytes), 2/0 |
| all six areas gate, 2026-09-29 (commit 89526ac23 fixes the 10) | fub 71/0, fub_beats 46/0, macro 171/10 -> scheduler_group* 37/0 after, macro_beats 173/0, top 14/0, top_beats 12/0 |
| all six areas func, 2026-09-29 | fub 494/0, fub_beats 388/0, macro 457/1 (test_axi_write_operations, 512-bit slow_producer), macro_beats 430/0, top 28/0, top_beats 24/0 |
| macro snk_data_path_axis_test func after the stimulus reorder (descriptor first) | 112/0 |
| all six areas full, 2026-09-30 (after the venv restore) | fub 1521/0, fub_beats 1281/0, macro 813/0, macro_beats 771/0, top 42/0, top_beats 36/0 |
| all six areas full, 2026-09-30, after the channel-reset close (byte tree only; beats tree untouched) | fub 1521/0, fub_beats 1281/0, macro 819/0 (6 new channel-reset cells), macro_beats 771/0, top 42/0, top_beats 36/0 |
| channel reset: byte `test_channel_reset` on snk / src data path axis test, 8 ch, AW 64, DW 256, ID 8, SRAM 1024 | pass; mutation-checked (the tests fail with the reset removed) |
| `bin/check_doc_examples.py` after the HAS / MAS 0.2 edits | 0 fabricated |
| Genesys2/rapids harness sim after the channel-reset close (run from a scratch copy with HEAD versions of the perf agent's in-flight host/rtl files) | 10/10 (8 harness + 2 top_kick); one case (33 B at 31) aborted once in a full run on a cocotb_test StreamReader error and passed 5/5 when rerun alone |
| Genesys2/rapids harness sim (`make sim`) | 8/0: sink, source, 1 B at 1, 77 B at 5, 33 B at 31, 203 B across 4 KB, kick_enable, empty_mask |
| Genesys2/rapids_beats harness sim after the tie-off and path fix | 4/0 |
| val/amba axis4_pattern_pair gate; amba lint; rapids lint | 3/0; 402/402; 86/86 |
| Genesys 2 build, 8 ch, 256-bit, 4 KB/ch, observers on | WNS +0.258 ns, 89,746 LUTs (44%), 68 BRAM tiles (15%) |
| Board, beat smoke on the byte DUT (2 ch x 4 beats) | SINK PASS, SOURCE PASS, golden-validated |
| Board, `--byte-smoke` (2 ch): 1 B at 1, 2 B at 31, 32, 37, 100 at 7, 96 at 17, 203 B across 4 KB | 7/7 PASS, sink write-CRC and source egress-CRC each against the byte-wise golden |

The one func failure was stimulus order, not RTL: the beat-era sink tests
queued a channel's next packet before that channel's descriptor could be
issued (send_descriptor blocks until the scheduler is free), so the AXIS
master's head beat waited on the byte contract past the BFM's 1000-cycle
ready timeout and a dropped beat shifted the channel by one. The tests now
send the descriptor first (handbook dv/blocking-send-deadlock).

Bugs the tests caught on the way: the egress retired a packet's state in
the same cycle its final pop re-armed it (source beat loss 27/84 at
cfg_drain_size 1, `test_beat_conservation`); a 6-bit byte counter made the
512-bit build's tstrb mask a constant (Verilator UNSIGNED); the byte TB's
`expected_seq` shadowed the base class's EXT helper; the packet-record
pulse must be sampled mid-cycle by a TB that raises ready between edges.

## Channel reset (2026-09-30, byte tree only)

The per-channel `cfg_channel_reset` (SNK / SRC `CHANNEL_RESET.CH_RST` ORed
with `GLOBAL_CTRL.GLOBAL_RST`, a register level, so pulse and level both
work) used to reach only the scheduler; a length-mismatch, RRESP or BRESP
sticky flag needed `aresetn`. It now reaches every byte data path that
latches state, and a channel recovers without `aresetn`:

- scheduler: re-enters CH_IDLE without re-erroring; sticky flags, loaded
  descriptor, beats remaining and the control-issued flag clear in every state;
- sink ingress: clears the record queue, hold, byte count, length error,
  pending allocation and the output/flush beat; `s_axis_tready` low while in
  reset; a cut packet's tail is accepted and dropped up to `tlast`
  (`r_discard`). Head-of-line blocking on a shared stream stays, documented;
- read engine: no new AR while in reset or flushing, outstanding R beats
  accepted and dropped without setting RRESP;
- write engine: no new AW; an open burst is finished with null W beats
  (WSTRB 0); one presented-but-unaccepted beat is replayed; B responses
  consumed with the error flag suppressed;
- source egress: queue, hold, byte counters and reservation entries clear;
  a beat already in the output register completes; a mid-packet reset leaves
  the stream packet unterminated (documented);
- the byte SRAM wrappers reset their per-channel instances; the shared
  STREAM `sram_controller` and every `*_beats` file are unchanged.

No RTL assertions; resets use the reset macros. One channel's reset leaves
the other channels' traffic intact (tested). Books: HAS `04_error_handling`
and the affected MAS chapters, both at 0.2.

## Constraint: rapids-beats never loses functionality

Sean, 2026-09-29: "Ensure rapids-beats never loses functionality." The
beats tree is the characterized design and stays runnable and green for
as long as it exists. Concretely:

- no file under `fub_beats/`, `macro_beats/`, `top_beats/`, `dv/tests/*_beats`
  or `dv/tbclasses/*_beats_tb.py` changes for this task;
- files both trees share (`rtl/includes/rapids_pkg.sv`, `rtl/fub/ctrl*_engine.sv`,
  `rtl/macro/monbus_axil_group_2in.sv`, the `rtl/amba` blocks, the harness
  generators and checkers) change only additively: new types, parameters
  with defaults that reproduce today's behaviour, new ports only behind such
  a default;
- every commit that touches a shared file re-runs the beats gate suite from
  `make clean-all`, and the func suite before the task closes, with the
  counts recorded here (baseline 2026-09-29: gate 255/0, func 938/0);
- the Genesys 2 `rapids_beats` harness keeps building from the beats
  filelists unchanged; the byte design gets its own harness variant.

## Done when

- [x] the decisions above are recorded here, and the byte design has its
      own books: `docs/rapids_has/` and `docs/rapids_mas/` (v0.2, PDFs
      rebuilt 2026-09-30 with the channel-reset chapters), linking every chapter it shares with RAPIDS Beats
- [x] a one-byte AXIS beat lands as one strobed byte in memory, and a
      byte-length source descriptor produces a stream whose first and last
      beats carry the right `tstrb`, both on the board with the byte-wise
      golden CRC (2026-09-30, `Genesys2/rapids/reports/board/`)
- [x] the perf report has a bytes-per-beat efficiency column
      (`Genesys2/rapids/reports/perf/README.md`, v0.2, 2026-09-30: 117/117
      byte-wise points on the standard bitstream plus 28/28 aligned points on
      the word-wide checker bitstream, which reaches 3182 MB/s sink and
      3199 MB/s source of the 3200 MB/s peak at 8 channels, 4096 beats)
- [x] the utilization of the beat-aligned rows matches RAPIDS Beats in
      steady state, and the short-transfer differences are bounded
      one-time start-up latencies (amended 2026-09-30 by Sean's decision,
      rapids TASK-021; the original wording demanded 0.5 pp on every cell).
      Measured: 73 of 112 aligned cells differ by more than 0.5 pp, worst
      -84.85 pp on short transfers; the 4096-beat rows are within 1.13 pp and
      the 8-channel 4096-beat row within 0.32 pp. Mechanisms, isolated in sim:
      the byte data enters the SRAM only after the scheduler's packet record
      (sink write starvation +3 + (min(n, 9) - 1) cycles), the source's
      `m_axis_tvalid` is registered (+1 cycle), and the sink AXIS-in
      backpressure of 27 + 20 x channels cycles is the same record gating
      (a 4-deep skid absorbs the first beats at 1, 2 and 4 channels, 1 beat).
      Nothing can happen before the descriptor is loaded, so this is by design.
