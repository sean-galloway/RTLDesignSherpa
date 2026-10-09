# TASK-018: an interleaved-channel mode for the harness AXIS generator, so the sink's aggregate window can be measured

**Priority:** P3. Filed 2026-09-28 from rapids ISSUE-006.
**Status:** CLOSED 2026-09-28 (closing note at the end).

## Why

`axis4_master_injector` streams channels sequentially (finish one channel,
then the next) so each channel's LFSR sequence stays contiguous for the golden
CRC. That means only one sink channel ever holds data, and every sink number
measured under memory latency (perf report 7.5) is ONE channel's window
(`AW_MAX_OUTSTANDING x burst`), while the source column reflects all eight
channels reading concurrently. The two columns are not comparable as they
stand.

## What to add

A `cfg_interleave` mode that round-robins the active channels beat by beat
(tid changes every beat, each channel's LFSR still advances only on its own
beats so the per-channel CRC is unchanged), plumbed through the harness CSRs
and `run_characterization.py` (`--interleave`), then re-run the 7.5 latency
sweep and add the aggregate-window row set to the report. STREAM's harness
generator is the same block and gains the mode for free.

---

**CLOSED 2026-09-28.** `axis4_master_injector` gained `cfg_interleave`
(latched with the mask on `cfg_start`): the same next-active scan hands the bus
to the next active channel after every accepted beat and wraps to the first, so
one round counter and one packet counter serve every channel; a channel's LFSR
and CRC still advance only on its own beats, so the per-channel data, CRCs and
packet boundaries are identical to the sequential schedule and the golden model
is untouched. `val/amba/test_axis4_pattern_pair.py` now reconstructs the bus
order from the wrapper's tid probe and checks it beat by beat in both modes
(four directed interleave scenarios, interleave randomised at full; the check
fails at beat 1 when the RUN branch is disabled). Harness: `GEN_MODE` @0x028
`[0]=INTERLEAVE`, regmaps regenerated; host `--interleave` /
`set_interleave()`, rows carry `gen_interleave`; harness TB knob
`TEST_GEN_INTERLEAVE=1` (sink self-check passes in sim, 8 channels). STREAM's
harness has its own generator path and did not need a change.

Board (Genesys 2, observers build with GEN_MODE, post-route WNS +0.245 ns):
interleaved 8-channel sink smoke 8/8 CRC PASS; the 7.5 latency sweep with
`--interleave` holds AXI4-wr at 99.9 % on every row to 512 cycles (no knee;
>= 512 beats in flight against a ~744-beat aggregate window), while the
sequential control sweep on the same bitstream reproduces every v1.4 cell
(~93 beats, one channel's window). Perf report v1.5: Table 7.5b, Figure 7.5b,
the rewritten 7.5 interpretation, `json/genesys_obs_E_interleave.json`.
