# TASK-014: Perf methodology — saturation curves + adversarial traffic for the bridge dv suite

**Priority:** P3
**Status:** CLOSED 2026-10-24 (grouped with TASK-016; patterns and saturation curves in `test_bridge_perf_patterns.py`, recorded in HAS 5.1)
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

- [x] perf tests emit saturation + latency-vs-load data for uniform,
      permutation, and hot-spot patterns
- [x] HAS ch05 cites the methodology and links the data
- [x] no regression in the existing FULL bridge regression (FUNC run clean-all after the regeneration; see the commit)

## References

- `projects/components/fabric-gen-ip/bridge/references/README.md` (Dally &
  Towles ch3; Duato ch9)

## Done (2026-10-24)

- `dv/tbclasses/bridge_perf_patterns.py` + `dv/tests/test_bridge_perf_patterns.py`:
  open-loop sweeps (one 4-beat read per master every `gap` cycles) under
  uniform, permutation and hot-spot patterns on `bridge_2x2_rw`,
  `bridge_2x2_rw_pipe` and the mixed-width `bridge_4x4_rw`; accepted
  throughput against offered load in slave beats per cycle summed over the
  targeted ports, capacity = sum over slaves of min(offered, 1.0), mean and
  p95 latency per master; every read checked. Floors: accepted >= 0.85 of
  capacity; latency flat (base + 4) below half capacity. GATE runs three
  load points, FUNC and FULL the curve (minimal by default, the curve is
  the knob). 18/18 at FUNC.
- Measured (HAS 5.1 "Traffic Patterns Against Offered Load"): below
  capacity every pattern carries exactly what is offered at flat latency;
  permutation holds every slave at 1.000 however far overloaded, on the 2x2
  and the 4x4 (four widths at once, 0.89-1.00 of per-slave capacity);
  hot-spot holds its port at 1.000 with queueing latency beyond; the
  registered crossbar is the same curve one cycle later.
- Finding, filed as bridge TASK-021: UNIFORM traffic past saturation drops
  to 0.80 of capacity at 1.33x offered and 0.67 at 2x on both 2x2s, 0.61 on
  the 4x4 -- head-of-line blocking where a master's single in-order request
  stream meets the 2-deep per-(master, slave) request slots; permutation
  and hot-spot are immune. The test holds those points at 0.55 of capacity
  under TASK-021's ID until it lands.
- The sizing step (TASK-016) is measured with the same machinery in
  `test_bridge_perf_sizing.py`.
