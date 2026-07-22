# Monitor board-validation plan (owner-specified environment)

Written 2026-07-21. This is the owner's described FPGA environment for
exhaustively validating the AXI4/APB monitors on silicon, recorded here after
the session task tracker was lost. Execution is gated on the monitor subsystem
being fully clean in pre-si (saturation-wedge fix landed cb29e226; E1/E4/E5/E6
fixes + docs in flight; 100-seed backpressure sweep to run once RTL settles).

## The environment (owner's words, consolidated)

- STREAM with **2-4 channels** (owner 2026-07-21: the Genesys makes 2-4ch
  feasible and more interesting than the original 1ch -- multi-channel
  contention on the shared masters is exactly the geometry that exposed the
  saturation wedge, and it produces far richer packet-type/arbitration
  coverage). HARD BOUNDARY: stay at <= 4 channels until the known 8-channel
  ENGINE wedge (non-monitor, sim-reproducible, params7/9/11 family) is
  root-caused -- board hangs from a known engine bug would pollute the
  monitor campaign. Monitors added to the wr/rd blocks they send to.
- On the FPGA layout: **a wrapper around the rd/wr slaves**; connect their
  monitors to a **monitor group that writes directly to its own SRAMs**. The
  UART harness reads those SRAMs with **AXIL**.
- Goal is NOT hammering: **test all the different packet types and make sure
  they happen**. We know we can send packets faster than they can get out —
  **the goal is to match the send and xmit rates**.
- Matching, plus formally seeing as many packet types as is reasonable.
  **Most errors MUST be proven in pre-si** — the board run is confirmation,
  not discovery.
- APB monitors get the same treatment; APB address-match required (the
  apb_monitor_addr_check / apb5 128-bit work covers the pre-si half).

## Related owner decisions from the same discussions

- stream_cg variant: clock-gated STREAM on the FPGA using the CG AMBA models
  throughout. CG-model bugs are bugs to fix, not avoid; an FPGA flavor of the
  ICG is acceptable; timing does not matter — 60 MHz is fine, the point is
  **millions of cycles** on the gated design.
  SCHEDULE (owner 2026-07-22): stream_cg is a couple of WEEKS out — explicitly
  NOT part of the initial Genesys monitor campaign. Do not fold CG work into
  the first two board runs (coverage/rate-matching + undersized-table soak);
  it lands as its own campaign after the monitor work is signed off.
- Board flow reuses the established UART-harness pattern
  (ddr2_char / cdc_counter_display precedent: PeakRDL regmap-by-name,
  cocotb-UART sim equivalence so the same host program runs in sim and on
  the board).

## Pre-si gate (must be green before building the bitstream)

1. val/amba full suite green (674+ / 0) including the new E1/E4/E5 directed
   tests and the saturation phase.
2. Formal: all monitor dirs PASS with live assertions (mutation-checked).
3. stream_core: single_channel 12/12; mon_backpressure 100-seed sweep clean.
4. Packet-type coverage inventory: enumerate every packet type / event code
   the monitors can emit, and show each one produced at least once in pre-si
   (this is the "formally seeing as many types as is reasonable" half).
   The remaining runtime-config semantics (cfg_*_enable after E1,
   cfg_axi_pkt_mask) must be documented first so the inventory uses the
   supported knobs.

   COMMITTED WORK ITEM (owner-approved 2026-07-21, build immediately after the
   E1/E4/E5/E6 fixes land -- E1 changes which codes runtime-disabled configs
   emit, so building earlier would churn):
   a. Opt-in hook in bin/TBClasses/monbus/monbus_slave.py: MONBUS_COVERAGE=1
      -> on test end, append each decoded (protocol, pkt_type, event_code)
      tuple + test name as JSONL. One class covers the whole val/amba suite;
      MonbusSniffer covers interfaces the slave does not sit on. Decode ONLY
      via TBClasses.monbus.parse (house rule).
   b. Aggregator (bin/, ~60 lines): union the JSONLs, diff against the full
      enum space imported from monbus_types.py (AXIErrorCode, APBTimeoutCode,
      ARBPerformanceCode, ... -- the machine-readable ground truth; no SV
      parsing), emit: code -> emitting test(s) | NONE.
   c. The NONE rows are the pre-board sign-off list: each gets a provoking
      test or a documented unreachable/reserved rationale.

## Target board: Genesys 2 (owner decision 2026-07-21)

Primary target is the Genesys 2 (xc7k325t), not the Nexys A7. The K325T is
~3x the A7's logic with far more BRAM, which relieves the tight-board
constraint below; and the rapids_char campaign already established the port
pattern (rapids_characterization/flows-rapids-beats/flists/
rapids_char_genesys2_top.f, ran 8ch at 99.8-100% util / 6.4 GB/s). Needed:
a stream_* genesys2 top + XDC following that template. Board handling: JTAG
serial 200300B818A0 on the shared chain (RAPIDS_CHAR_JTAG_SERIAL), UART on
its own FT232R (AU05X8RM), do NOT power-cycle after programming, Adept kills
the ttyUSB. The A7 budget section below is retained in case an A7 build is
ever wanted; on the Genesys treat it as good hygiene, not a hard ceiling.

## Area/timing budget (A7 note, retained: "the board is tight -- be
## careful how much you monitor")

The xc7a100t is small and stream_char already closes timing on a knife-edge
(chronic monbus-compressor CAM route path; pblock floorplanning, not
pipelining, is the established fix). Monitoring hardware must be budgeted,
not maximal:

- Monitor CAM depth dominates monitor area (age matrix is O(N^2) compares).
  Size at the no-backpressure bound for the chosen channel count
  (NC * MAX_OUTSTANDING + 4: 12 at 1ch, 36 at 4ch -- comfortable on the
  K325T), not the 8-channel default (68).
- OPTIONAL second bitstream: the deliberately UNDERSIZED table (16 entries at
  4ch -- the mon_backpressure geometry) for millions of cycles of real
  blocking/recovery on silicon, the hardware twin of the 100-seed sim sweep.
- Packet SRAM is a COUNTING histogram, not a log (owner design 2026-07-21):
  address = {source, pkt_type[3:0], event_code[7:0]}, data = saturating
  count, RMW increment on packet accept. ~8K bins x 32b = a few BRAM36s,
  independent of run length. This removes the capture-bandwidth problem
  entirely (a counter absorbs any rate), removes the compressor (and its
  worst-path CAM) from the board build, and IS the coverage matrix in
  hardware: bin > 0 == "this type/msg happened on silicon", dumped in one
  AXIL/UART sweep. Front it with a ~32-entry CAM/CACHE (owner 2026-07-21):
  a CAM on the bin tag with per-entry partial counters -- REUSE the existing
  CAM collateral (monbus_cam / bridge_cam pattern: tag store, match-oh,
  alloc/evict, occupancy) rather than writing a new one-off; the counter
  payload is the only new piece. 32 x ~13b tags on the K325T at 60-100 MHz
  is comfortable (the chronic CAM timing path was the COMPRESSOR's larger
  CAM on the A7 at 100 MHz; pblock is the established fix if it ever
  bites). Hit =
  in-place increment (no SRAM touch -- handles back-to-back same-bin
  packets, the hard case for BRAM RMW); miss = allocate + victim's partial
  SATURATING-ADDS into its SRAM bin in the background. Run traffic is
  heavily skewed to a handful of bins, so post-warmup SRAM traffic ~= one
  RMW per distinct bin per eviction, not per packet. MUST-GET-RIGHT: (1)
  freeze/flush CSR drains all partials before the AXIL readback so the dump
  is a coherent snapshot; (2) saturation is preserved across the
  cache/SRAM split -- a pegged bin never wraps through eviction. The pre-si
  exact-match cross-check vs the Python-side counts verifies the cache
  (a lost increment through an eviction race = count mismatch in sim).
- Expected counts are COMPUTED from the descriptor programming by the host
  program: exact equality for deterministic classes (completions, beats,
  per-channel counts), bounded (>0, <= cap) for interleaving-dependent
  classes (perf/threshold/arb), exactly ZERO for disabled error classes --
  any nonzero expected-zero bin is a finding.
- First-event latch: full 128b packet + timestamp captured for the FIRST
  packet landing in any expected-zero bin, so a nonzero error bin on the
  board yields the offending packet, not just a count.
- Pre-si cross-check for free: the histogram block runs in the cocotb tests
  too, where its bins must match the MonbusSlave/parse() Python-side counts
  EXACTLY. Sim validates the histogram; the histogram carries that trust to
  silicon. (The Python coverage hook + aggregator remain the sim-side matrix
  source; the hardware histogram is its silicon twin.)
- Prefer the always-on perf meters (cheap buckets/beat/byte counters) over
  heavy monitor features for the rate-matching half; heavy packet classes
  are enabled selectively per run, not all at once (packet-congestion rule).
- The compressor is optional on the board build: only include it if the
  capture SRAM budget forces it, since its CAM is the known worst timing
  path on this part.
- If utilization or WNS gets tight, drop monitor scope before dropping
  clock: 60 MHz is acceptable (owner), but a build that only fits without
  the wr-side monitor is a scope decision for the owner, not a silent trim.

## Build shape (derived, to be validated against the owner)

- flows-stream-bridge derivative: stream_core 1ch + rd/wr slave wrappers
  (axi4_slave_rd/wr + their monitors) + monbus group -> dedicated SRAM
  (sdpram_slave_axil_* for the AXIL read side) + UART harness AXIL window.
- Send/xmit rate matching instrumented via the existing perf counters
  (always-on meters) on both producer and drain sides.

Known open engine issue, separate from monitors: stream_core multi_channel
8-channel configs hit a non-monitor engine wedge (probe-proven monitors idle;
failing set shifts with timing perturbation). Track before any multi-channel
board work; irrelevant to the 1-channel monitor environment above.
