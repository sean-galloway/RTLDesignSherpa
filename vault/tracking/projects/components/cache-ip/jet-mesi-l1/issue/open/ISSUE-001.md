# ISSUE-001: cpu_req→snoop-accept combinational chain fails 90 MHz timing on Kintex-7

**Priority:** P2 (performance/closure limitation, not a functional defect)
**Status:** OPEN
**Filed:** 2026-11-02, from the first jet Genesys2 build (T13 step 1).

## Observation

The jet pair-rig Genesys2 build (`projects/fpga-systems/Genesys2/cache-ip/jet/`,
first routed checkpoint) fails setup timing at the amber rig's 90 MHz clock:

- **WNS −4.065 ns, ~95,880 failing endpoints** (~22% of the design).
- Worst paths are all one shape: `u_cpu/u_req_skid/read_pointer` (RAMD32
  async read of the CPU-request skid) → **31 logic levels** →
  `u_fab/u_snoop/u_transport/ac_channel` skid data/CE.
- amber closes the same harness skeleton at WNS +0.083 ns; amber's snoop
  responder appears only in 0-level reset paths. The chain is jet-specific.

## Reading

In jet's non-blocking pipeline the CPU request and the snoop share the
lookup/classify stage (hit-under-miss, snoop-during-miss, pend_eff, cap_busy,
tag-full), so the snoop AC accept/window logic combinationally depends on the
freshly arriving CPU request. That sharing is jet's entire value proposition —
and it is a 31-level input-to-accept cone on this process. DV and formal are
green; this is purely an implementation-timing wall, found exactly where the
plan expected T13 to find such things (silicon, not sim).

## Implications

- The jet rig bring-up reclocks to 60 MHz (MMCM 1350/22.5; the cone needs
  ~15.2 ns). J7 metrics are cycle counts and bin rates, so the amber↔jet
  comparison is unaffected by the clock difference.
- Any ASIC target (asap7 flows) will hit the same cone at serious clocks.

## Likely fix (becomes a task when scoped)

Pipeline the snoop-accept path: register the CPU-request skid output
(or the classify result) before it can influence the snoop AC accept, and/or
register the snoop-safety window. Must preserve the coherence contract
(the pre-AR rule, the safe-window semantics) — jet DV + the formal harness
(safety depth 64, liveness depth 176) re-run green as the gate. This is jet
v2 work, deliberately not bolted onto T13.

## Evidence

- `projects/fpga-systems/Genesys2/cache-ip/jet/build-bringup/fpga/reports/timing_summary.txt`
  (Design Timing Summary + worst-path list; committed build-bringup collateral).
