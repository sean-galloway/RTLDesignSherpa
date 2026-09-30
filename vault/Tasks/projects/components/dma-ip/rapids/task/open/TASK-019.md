# TASK-019: the byte-granular RAPIDS -- lengths in bytes, AXI4 byte enables, partial AXIS beats

**Priority:** P1 -- the beats architecture was always the first step, not the
product. Sean, 2026-09-29: "begin looking into the actual version of rapids
where bytes are counted, BYTE ENABLES are used on AXI4 and there could be a
single byte written on AXIS4."
**Status:** OPEN 2026-09-29. This file is the investigation; the decisions
listed at the end gate the design.

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

- [ ] Packed egress (byte shifter) or address-positioned lanes with sparse
      `tstrb`? The shifter costs logic on both halves; sparse lanes cost the
      consumer.
- [ ] Descriptor length unit: bytes in the existing 32-bit field (4 GB max),
      or bytes plus a byte-offset field so addresses may stay aligned in the
      descriptor?
- [ ] SINK contract between `tlast` packets and descriptor byte length.
- [ ] Keep `DATA_WIDTH` = 256 for the first byte-granular build (the 4 KB
      design point), so every existing perf cell remains comparable?

## Done when

- [ ] the decisions above are recorded here and in the HAS
- [ ] a one-byte AXIS beat lands as one strobed byte in memory, and a
      byte-length source descriptor produces a stream whose first and last
      beats carry the right `tstrb`, both on the board with the byte-wise
      golden CRC
- [ ] the perf report has a bytes-per-beat efficiency column and the
      utilization cells of the beat-aligned rows are unchanged
