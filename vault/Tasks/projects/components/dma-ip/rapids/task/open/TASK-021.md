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

- [ ] the +11 write and +1 source cycles are isolated in the harness sim to a
      named mechanism (the 1-beat low-channel oddity included)
- [ ] a decision is recorded: accept the terms as by design and amend the
      rapids TASK-019 criterion to a bound on the start-up terms, or add a
      fast path (no record gating for beat-aligned default cases) that puts
      the aligned rows within 0.5 pp
- [ ] if a fast path is added: the gate and func suites pass from
      `make clean-all`, and the word-wide aligned profile is re-run on the
      board
- [ ] rapids TASK-019's utilization box is closed or amended to match
