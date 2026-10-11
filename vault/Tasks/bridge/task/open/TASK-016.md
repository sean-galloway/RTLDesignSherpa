# TASK-016: Buffer/CAM depth sizing rule vs pipeline + converter latency

**Priority:** P3
**Status:** OPEN
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

- [ ] sizing rule documented with the literature citation
- [ ] generator emits a warning on undersized configurations
- [ ] a config at the rule's boundary shows the predicted throughput step in
      the TASK-014 saturation data

## References

- `projects/components/fabric-gen-ip/bridge/references/README.md` (Dally &
  Towles ch12, ch15)
