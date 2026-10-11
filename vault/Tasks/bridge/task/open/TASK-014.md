# TASK-014: Perf methodology — saturation curves + adversarial traffic for the bridge dv suite

**Priority:** P3
**Status:** OPEN
**Owner:** bridge
**Filed:** 2026-10-11 from the interconnect-literature deep review (bridge citations commit e0be98508)

## Motivation

The bridge perf suite (`bridge/dv/tests/test_bridge_2x2_rw_perf.py`) measures
throughput floors and pipe latency under uniform-style traffic. The
interconnection literature is blunt about this blind spot:

- Dally & Towles, ch3 §3.2–3.3: uniform random traffic is the most benign
  pattern; permutation and hot-spot traffic expose allocation bottlenecks that
  uniform traffic hides.
- Duato et al., ch9: the standard evaluation is accepted-traffic vs.
  applied-load (throughput saturation curve) plus latency vs. applied-load,
  not a single-point floor.

## What to do

1. Add permutation and hot-spot (single-slaver) traffic patterns to the perf
   probe, alongside the existing uniform pattern.
2. Measure accepted vs applied load up to and past saturation, and latency vs
   load, for the 2x2 rw configs (combinational and `xbar_pipeline`).
3. Record the results in the HAS ch05 performance chapter; if a bottleneck
   appears (e.g. a single hot slave throttling all masters), file the fix as
   its own task.

## Done when

- [ ] perf tests emit saturation + latency-vs-load data for uniform,
      permutation, and hot-spot patterns
- [ ] HAS ch05 cites the methodology and links the data
- [ ] no regression in the existing FULL bridge regression

## References

- `projects/components/fabric-gen-ip/bridge/references/README.md` (Dally &
  Towles ch3; Duato ch9)
