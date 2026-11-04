# ISSUE-001: cpu_req→snoop-accept combinational chain fails 90 MHz timing on Kintex-7

**Priority:** P2 (performance/closure limitation, not a functional defect)
**Status:** ACTIVE (2026-11-03)
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

## Fix landed (2026-11-03)

Cone mapped on the routed MSHR=16 checkpoint (Vivado `report_timing`, not
guesswork): the entire top-20 critical list at 60 MHz is ONE 35-level cone —
`u_cpu/u_req_skid` RAMD32 async read → `u_coh` classify/tag-hit
(`u_tag w_hit_way*`) → `w_fill_accept` → `coh_req_addr` sideband →
`jet_pair_fabric.issue_peer_pulse_same` (the LIVE same-cycle kill-rule tap
on the peer's unregistered `coh_req`, `jet_pair_fabric.sv:649`) → peer
`l1_axi4_plane` AC skid D/CE. ~15.2 ns on Kintex-7.

Fix: `coh_req_valid/addr/type` registered one cycle at the `jet_coh_core`
boundary (`jet_coh_core.sv:963`). The fabric consumes the pulse purely as an
announcement — its live tap and its registered pend queue shift together, so
relative ordering is preserved and every fabric decision lands one cycle
later. Same-cycle assertions in `jet_top.sv`/`jet_ace_top.sv` moved to `|=>`.

Gates: jet component DV 41/41 (incl. pair-rig + amber-oracle parity);
Genesys2 harness DV 4/4 (AXIL+UART, func+gate). Formal re-run not applicable
— the jet_control formal closure does not include `jet_coh_core`.

## v2 pipelining program (2026-11-03, owner-approved)

The single cut exposed the rest of the iceberg at 100 MHz (attempt 1:
WNS −4.09 ns, 111k failing endpoints). v2 = three more cuts:

- **Step 1 — observation taps registered** (`jet_coh_core.sv`): both
  monitors' tap bundles + `mon_time` shift one cycle in lockstep; the
  worst paths were route-dominated into `u_monlite`/`u_jet_monlite`.
  Monitor group fully cleared from the failing list.
- **Step 2 — hit-serve pend** (`jet_control.sv`): the hit serve (array
  read / write + E→M tag write + response deposit) moves one cycle after
  the accept into a one-deep pend register; `jet_rsp_seq` deposits are
  tag-indexed and latency-agnostic, so the contract is unchanged. Hit
  latency 3→4 cycles (matches amber). Hazard rules: same-line stall while
  a write pends; miss-alloc blocked when the pend targets the victim slot
  (capture/fill would race the deferred serve); `sn_safe` gated on a
  pending write (address-agnostic — the transport's accept-mux rule);
  write-fire needs W port + deposit port (+ tag port for E→M). The
  accept-time port holds moved to the pend's fire condition, which also
  SHORTENED the accept cone. DV TB learned the serve-pend contract
  (`_await_serve`); 41/41.
- **Step 3 — fabric peer status** (`jet_pair_fabric.sv` + `lkup_live` out
  of `jet_top`): `peer*_state` registered at the fabric input; the live
  `peer_lkup_now` bit covers the one-cycle IDLE→classify-outcome window
  the stale view would miss (the kill-rule RU-conflict corner stays
  closed — naive state registration alone would have reopened it).
  Pair-rig + parity DV 32/32.

Progress at 100 MHz (WNS / failing endpoints): −4.09/111k (attempt 1,
step 0 only) → −4.43/139k (attempt 2, +step 1 — effort reshuffle) →
−3.37/41k (attempt 3, +step 2; the 55k-endpoint array cone is GONE) →
attempt 4 adds step 3. Remaining after step 2: the classify cone's
register endpoints (control/repl/MSHR, ~12.4–13.4 ns) and the read-serve
async-array-read→deposit path. Cutting those needs the lookup-stage split
(classify moves a cycle after accept — jet v3, changes the accept
handshake) or sync-read arrays.


## Original analysis

Pipeline the snoop-accept path: register the CPU-request skid output
(or the classify result) before it can influence the snoop AC accept, and/or
register the snoop-safety window. Must preserve the coherence contract
(the pre-AR rule, the safe-window semantics) — jet DV + the formal harness
(safety depth 64, liveness depth 176) re-run green as the gate. This is jet
v2 work, deliberately not bolted onto T13.

## Evidence

- `projects/fpga-systems/Genesys2/cache-ip/jet/build-bringup/fpga/reports/timing_summary.txt`
  (Design Timing Summary + worst-path list; committed build-bringup collateral).
