# ISSUE-007: MONCAP reads nothing on observer-only rapids builds -- the interface observers' monbus never reaches the capture buffer

**Priority:** P3
**Status:** open
**Owner:** TBD

## Observation

A rapids byte build with `USE_OBSERVERS=1 OBS_ENABLE_MON_TAPS=1 MON_CAPTURE=1`
(bitstream built and measured 2026-10-08, utility-ip/misc TASK-003 board
matrix, rapids leg) passes its golden self-checks with the observers live
(`tap_packets=8`, `tap_dropped=0` per seam, observer/meter productive deltas
0) — but `MONCAP_CNT` reads 0 words after traffic: the capture buffer is
structurally empty.

## Mechanism (rapids_byte_harness.sv)

The capture buffer (`gen_moncap`, ~line 2078) stores `mon_wdata` beats from
`m_axil_mon_*`, which is **rapids_top's in-core monitor egress**
(`USE_AXI_MONITORS`/`GEN_MON` cone, instantiation ~line 1518). The shared
interface observers (`gen_obs`, ~line 2344: `axi4_intf_master_observer` +
`axis4_intf_observer`) emit their monbus packets through their own
EGRESS_AXIL write masters into always-accept responders whose data is
discarded. Nothing routes the observer stream into `gen_moncap`, so on a
build with in-core monitors OFF and observers ON, the buffer's only source
is dead.

Consequence: the per-class packet matrix the TASK-003 board leg wanted from
the observers is not board-readable on this topology. What IS readable and
was A/B'd old-tap vs lite-tap on 2026-10-08: observer telemetry (buckets,
bytes/beats/packets, metrics 15/16, AXI latency histograms) — all exactly
equal between the two images on identical golden-validated traffic
(/tmp/task003/rapids_matrix_{lite,oldtap}.json, bitstreams sha
85861f46... vs 1632ff8e...).

## Options

- Hook the observer egress into `gen_moncap` when `USE_OBSERVERS &&
  !GEN_MON`: mux `oa_*`/`ox_*` W beats (3 per record, same 64-bit-word
  format the buffer already stores) into the buffer's push term. Small,
  but it is an RTL change to a characterization harness with design
  choices (both observers ORed? address filtering? new parameter vs
  reusing MON_CAPTURE semantics?).
- Or declare observer-class board coverage out of scope for rapids and
  rely on the component-level sim evidence (utility-ip 12/12 suite, all 7
  classes emittable, tap_dropped 11..13 -> 0 on the all_classes stimulus).

## Log

**2026-10-08 -- filed** from the TASK-003 board matrix (rapids leg).
Related: stream BUG-019/BUG-020 (the sibling session's monitor-campaign
findings on the same board night), tooling ISSUE-004 (hw_server partial
enumeration — hit 3x during this matrix).
