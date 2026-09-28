# TASK-018: an interleaved-channel mode for the harness AXIS generator, so the sink's aggregate window can be measured

**Priority:** P3. Filed 2026-09-28 from rapids ISSUE-006.
**Status:** OPEN.

## Why

`axis4_master_pattern_gen` streams channels sequentially (finish one channel,
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
