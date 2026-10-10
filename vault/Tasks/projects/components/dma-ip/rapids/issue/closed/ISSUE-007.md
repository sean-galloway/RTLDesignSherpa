# ISSUE-007: MONCAP reads nothing on observer-only rapids builds -- the interface observers' monbus never reaches the capture buffer

**Priority:** P3
**Status:** FIXED 2026-10-09 (sim-verified; board readout now structurally possible). `gen_moncap` captures the interface observers' monbus when `GEN_MON=0`, with record-contiguous two-source arbitration. The per-class packet matrix the TASK-003 board leg wanted is now board-readable on the observer-only topology.
**Owner:** TBD

## Fix (2026-10-09)

`flows-rapids/rtl/rapids_byte_harness.sv`:

1. The observers' EGRESS_AXIL write data was **unconnected at the harness
   boundary** (`m_axil_wdata()` open on both `u_obs_axi` and `u_obs_axis`) --
   the deeper reason no observer record could ever reach anything. The
   observers' `wvalid/wdata/wready` are now module-scope signals
   (`obs_oa_*` / `obs_ox_*`) so the capture buffer -- a sibling generate
   block -- can store the beats.
2. `gen_moncap` source mux: `CAP_OBS = !GEN_MON && USE_OBSERVERS`. In-core
   monitor builds (`GEN_MON=1`) keep today's behavior exactly; observer-only
   builds capture the observers' RAW 3-beat records instead.
3. Record-contiguous arbitration: both observers share the one-word-wide
   buffer, so a **grant-lock** (beats granted mod 3) keeps each record's
   beats adjacent -- the host's fixed-stride decoder never sees an
   interleaved record. Round-robin applies only at record boundaries; the
   losing observer is stalled via `wready` (AXI holds), making capture
   lossless until the documented stop-on-full point (which keeps its
   drop contract: `wready` stays 1, the push is gated, `WRAPPED` reports).
4. Responder model counters now tally ACCEPTED beats (`wvalid && wready`)
   so the B model stays exact under the new backpressure; with no buffer
   (`MON_CAPTURE=0`) or no observers, behavior is bit-identical to before.

New sim: `test_rapids_byte_harness_observer_moncap`
(`cocotb_test_observer_moncap`) -- builds `USE_OBSERVERS=1,
OBS_ENABLE_MON_TAPS=1, MON_CAPTURE=1, GEN_MON=0`, runs a SINK
self-check, reads the buffer back over the same CSRs the board host uses
(MONCAP_CNT/SEL/LO/HI) and decodes with the shared `TBClasses.monbus`
parser. Result: **27 words, 9 records, protocols [0, 1]** -- AXIS
observer completions on ch0-3 and AXI observer completions (plus two
Error/0x0B tap observations) all decode cleanly. Existing sink/source
self-checks on the default build unchanged.

**Board proof (Genesys 2, 2026-10-09, obs+capture rebuild, WNS +0.283
ns):** BUILD = 0x21090840 (OBSERVERS=1, GEN_MON=0, MON_CAPTURE=1), SINK
self-check golden-validated (4 ch x 64 beats, CRC == golden all
channels, observers' meters exact vs bare meters dprod_vs_meter=0), then
`MONCAP_CNT = 111 words, wrapped=0` -- pre-fix this read **0** on this
exact topology. Decoded **37 records, protocols [0, 1]**: AXI-observer
completions per channel plus its Error/0x0B tap observations and AXIS-
observer records, same decode as sim. The TASK-003 matrix's per-class
observer readout is board-real.

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
