# TASK-016: Buffer/CAM depth sizing rule vs pipeline + converter latency

**Priority:** P3
**Status:** CLOSED 2026-10-24 (grouped with TASK-014 by the owner: defaults derived from the rule, TOML overrides, documented)
**Owner:** bridge
**Filed:** 2026-10-11 from the interconnect-literature deep review (bridge citations commit e0be98508)

## Motivation

Response-tracking storage (W-destination FIFOs, `bridge_cam` entries, skid
stages) is sized at generation time with fixed defaults. Dally & Towles,
ch12 §13.3.1 / ch15 §16.3 tie the required depth to the credit/response loop
latency — `t_crt = t_f + t_c + 2*t_w + 1` class reasoning: as
`xbar_pipeline` stages and data-width converters add latency, fixed shallow
depths silently throttle throughput long before any deadlock.

## What to do

1. Write the sizing rule for each buffer class: W-destination FIFOs,
   `bridge_cam` depth, and the `xbar_pipeline` skid stages, as a function of
   configured pipeline depth, width-converter presence, and max outstanding
   per master.
2. Encode it as generator warnings when a TOML config's depths fall below the
   rule's minimum (warn, don't force — the user may know better).
3. Document the rule in HAS ch03 architecture and ch05 performance.

## Done when

- [x] sizing rule documented with the literature citation
- [x] generator emits a warning on undersized configurations
- [x] a config at the rule's boundary shows the predicted throughput step in
      the TASK-014 saturation data

## References

- `projects/components/fabric-gen-ip/bridge/references/README.md` (Dally &
  Towles ch12, ch15)

## Done (2026-10-24)

Owner's decision: group with TASK-014; the defaults become the rule's
minimum, every depth stays a TOML key, and both are documented.

- `bin/bridge_pkg/sizing.py`: per-path fabric round trip summed from the
  stages the generators build (wrapper cuts, request slot, registered
  crossbar, converters, CDC crossings, rate buffer, turnaround, response
  routing); calibrated to the measured single-beat round trips (2x2 8,
  registered 10, converter 12-13, CDC 13) as a bound within two cycles --
  `bin/tests/test_generator_pkg.py` holds it there. Rule: `max_outstanding`
  = pow2(1 + `latency_cycles` + round trip) over the port's paths, floored
  at `2**id_width` for a master that keeps its ID (the derivation never
  turns ID remapping on by itself); `rate_buffer` = pow2(`max_burst_beats` /
  ratio) on the widest upsized shared path, 0 without one; every skid stage
  2 (W was 4). New keys: slave `latency_cycles` (0..4096, default 0),
  master `max_burst_beats` (1..256, default 16). Explicit keys win and are
  only checked: a value under the minimum is a WARNING with the cost stated.
  The generator prints every depth with the rule beside it and writes
  `<bridge>_sizing.json` next to the RTL; the internal catch-all slave
  follows the bridge's defaults like every other port.
- Derived defaults land on 16 for every standard fixture (9-14 before
  rounding), 32 on the new `bridge_2x2_rw_slow` (`latency_cycles = 16`),
  4-8 where the fabric is cut to wires. A derived depth above 16 on a
  remapped master widens the slot and the fabric ID; the validator asks for
  the slave `id_width` it then needs (the slow fixture carries 6).
- The board fabrics (`bridge-stress` x7, `fabric-benchmark` x2) pin
  `max_outstanding = 16`, `rate_buffer = 16`, `defaults.skid_depths w = 4`
  -- what they were measured with -- and regenerate byte-identical.
- The step at the boundary, `test_bridge_perf_sizing.py` (HAS 5.1 table):
  single-beat streams against a 16-cycle slave run at 0.73 / 0.71 of peak
  on `bridge_2x2_rw` (derived 16, rule says 25) and saturate on
  `bridge_2x2_rw_slow` (derived 32); 8-beat bursts saturate both; at 64
  cycles both land on Little's law or a little above it. One ID per
  transaction in flight: the slave BFM answers same-ID reads in order.
- Docs: HAS 5.1 "Buffer Sizing Rule" + tables, HAS 3.2 "Buffer Sizing",
  HAS 6.2 key rows (`latency_cycles`, `max_burst_beats`, `rate_buffer`,
  derived `max_outstanding`, skid default), MAS 2.3 "Buffer Depths and the
  Sizing Rule", GENERATOR_ARCHITECTURE, PRD FR-6a, CLAUDE.md.
- Verification: generator unit tests 240/240; every fixture regenerated
  (266 generated files changed: W skid 4 -> 2 where not pinned, the derived
  depths on the cut fixtures, the catch-all following defaults) and the
  bridge FUNC regression run clean-all first -- result in the commit.
