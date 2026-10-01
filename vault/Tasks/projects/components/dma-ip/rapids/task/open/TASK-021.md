# TASK-021: decide and close the beat-aligned utilization delta versus RAPIDS Beats

**Priority:** P1 -- it is the last open box of rapids TASK-019.
**Status:** open, filed 2026-09-30 from rapids TASK-019.
**Owner:** TBD

The measured comparison (perf report v0.2, section 3.1) shows fixed start-up
terms, not rate changes. Sink AXIS-in backpressure is 27 + 20 x channels
cycles because the byte ingress waits for the channel's packet record; sink
AXI4 write starvation is +11 cycles (+3 at 1 beat) and source starvation +1
cycle, causes not isolated. Unexplained: channels 1, 2 and 4 at 1 beat show
no AXIS-in backpressure.

## Done when

- [x] the +11 write and +1 source cycles are isolated in the harness sim to a
      named mechanism (the 1-beat low-channel oddity included)
- [ ] a decision is recorded: accept the terms as by design and amend the
      rapids TASK-019 criterion to a bound on the start-up terms, or add a
      fast path (no record gating for beat-aligned default cases) that puts
      the aligned rows within 0.5 pp
- [ ] if a fast path is added: the gate and func suites pass from
      `make clean-all`, and the word-wide aligned profile is re-run on the
      board
- [ ] rapids TASK-019's utilization box is closed or amended to match

## Isolated mechanisms (sim, 2026-09-30)

Method: rapids_top and rapids_beats_top under the same cocotb TB (BFM AXIS
master, AXI4 slave BFM), 1-descriptor aligned transfers at 1, 4 and 9 beats,
waves sampled per clock; cross-checked against the harness sim
(byte_sim_aligned_wordcrc, 1, 4 and 64 beats at 1/4/8 channels). The TB master
paces 3 cycles per beat, so only byte-minus-beats deltas under an identical TB
are used. No RTL was changed.

| Config | wr starv byte | wr starv beats | Delta |
|---|---:|---:|---:|
| 1 beat | 9 | 6 | +3 |
| 4 beats | 12 | 6 | +6 |
| 16 beats and up | 17 | 6 | +11 |

The delta is the same at 1, 2, 4 and 8 channels for the same per-channel size
(an occasional +9/+10 at ch4/ch8 64 beats is the scheduler arbitration order,
not a different mechanism).

**(a) Sink AXI4 write starvation +3/+6/+11.** In the byte build data enters
the SRAM only after the scheduler packet record exists (`snk_data_path_axis`:
`s_axis_tready` needs `!w_pq_empty`, then the `r_out_valid` output register
feeds `fill`, then the registered availability reaches the engine). 1-beat
timeline, byte: record (`sched_wr_pkt_valid`) at cycle 440, beat accepted 441,
`r_out_valid`/fill 442, `w_has_data`/`w_final_burst` 444, AWVALID 447, WVALID
450. Beats: the beat was accepted and filled at 374, before the descriptor, so
`w_has_data` is already high with `sched_wr_valid` at 441, AWVALID 444, WVALID
447. That is a fixed +3 (accept to output register to availability). The write
engine issues AW only when min(remaining, burst) beats are resident
(`w_has_data`, `w_final_burst` in `axi_write_engine.sv`) and the byte path
fills one beat per cycle after the record, so the delta is 3 + (min(n, 9) - 1)
= +3 / +6 / +11 for n = 1 / 4 / 9 or more (the harness burst is 9 beats,
AxLEN 8). The delayed WVALID with WREADY high is what the meter counts as write
starvation. It is a one-time launch cost per descriptor, not a rate change.

**(b) Source starvation +1.** `src_data_path_axis` registers the stream output
(`m_axis_tvalid = r_out_valid`, loaded on the pop); the beats egress drives
`m_axis_tvalid` combinationally from the drain. First m_axis tvalid is 16 vs 15
at 9 beats and 23 vs 22 at 1 beat; the last accept and last tvalid are
identical (33 in both), so the cycle is latency only. Source rd starvation is
15 byte vs 14 beats at every size.

**(c) No sink AXIS-in backpressure at ch1/2/4, 1 beat.** `rapids_snk.sv`
puts `axis4_slave_monlite` (`SKID_DEPTH(4)`, `OUT_DEPTH(4)`) between the pins
and the data path, so the top-level `s_axis_tready` accepts the first 4 beats
with no record. Total beats at the pins <= 4 (ch1 b1/b4, ch2 b1, ch4 b1) gives
bp = 0; the harness sim JSON confirms it (ch1 b1 and b4, ch4 b1: sin bp 0). At 5
or more beats the 5th is held until the record (9-beat probe: beats 1-4
accepted, bp 38 cycles, then 2, 5, 8, 11, 14). That wait is the 27 + 20 x
channels term (the harness kick sequencer stages about 20 cycles per channel
before GO). The beats build keeps accepting because it buffers before the
descriptor. Beats sin bp is 0 up to 4 channels (2 at ch4 b256 and up); the
8-channel 82-cycle term is a separate SRAM-fill effect, out of scope here.

**Recommendation (for the second box, not yet decided here):** accept. All
three are one-time per-descriptor latency (+1 source, +3 to +11 sink write,
27 + 20 x channels sink ingress) with no steady-state rate effect. Hoisting
data ahead of the record or collapsing the output register would give up the
packet-record contract (the offset and length must exist before a beat can be
shifted and length-checked). The terms matter only for tiny transfers: ch1 b1
is 320 MB/s = 0.1% of the 3200 MB/s peak on the byte path, dominated by launch
latency in both builds. Suggested amendment to rapids TASK-019: bound the
start-up terms (sink AXIS-in <= 27 + 20 x channels, sink write starvation <= 11,
source starvation <= 1 over the beats build) instead of a utilization delta.

