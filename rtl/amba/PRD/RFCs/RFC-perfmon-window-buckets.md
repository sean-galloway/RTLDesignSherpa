# RFC: AXI Monitor — windowed cycle buckets, byte counters, latency histograms

**Status:** draft (pre-RTL)
**Scope:** `axi_monitor_base`, `axi_monitor_trans_mgr`, `axi_monitor_reporter`, `monitor_amba4_pkg`. Wrapper variants (`axi4_master_rd_mon`, `axi4_master_wr_mon`, `axi4_slave_rd_mon`, `axi4_slave_wr_mon`, AXIL parity, `_cg` variants) pick up the new ports.
**Driver:** `projects/NexysA7/stream_characterization/DMA_UTILIZATION_MEASUREMENT.md` Section 4. Goal is to retire the scattered trackers (`axi_bus_meter.sv`, harness-local valid/ready counters, opt-in `sram_chan_tracker`) and surface all bus-domain performance primitives through one monitor framework.

## 1 · What the monitor measures today

- 32-bit free-running timestamp (`axi_monitor_timer`)
- Per-transaction phase timestamps in `axi_monitor_trans_mgr`: `addr_timestamp`, `data_timestamp`, `resp_timestamp` → per-transaction `addr_latency`, `data_latency`, `resp_latency`, `total_latency` derivable
- `perf_completed_count`, `perf_error_count` (16-bit, output ports + PERF packets)
- Reserved PERF event codes for: ADDR/DATA/RESP/TOTAL_LATENCY, THROUGHPUT, BANDWIDTH_UTIL, QUEUE_DEPTH, BURST_EFFICIENCY, READ_WRITE_RATIO — **declared, not yet emitted**

## 2 · What's missing

- **Four cycle buckets** per channel (`productive` `valid && ready`, `backpressure` `valid && !ready`, `starvation` `!valid && ready`, `idle` `!valid && !ready`) — Section 3, 4
- **Beat / byte counters** — productive count + axsize accounting
- **Latency histograms** for the three phases — bucketed counts, not single-emission values
- **Window control** — start/end event select, free-running today
- **Per-channel buckets** via `axi_id` LSBs — currently only aggregate

## 3 · Event-code layout (16-slot constraint)

Existing `PktTypePerf` (one byte event_code = 16 slots) is mostly already declared; the new measurements would overflow it. Splitting into two packet types using existing reserved enum slots in `monitor_common_pkg.sv`:

```
PktTypePerf       = 4'h4   // existing — keep for "single value" perf events
PktTypePerfWin    = 4'hD   // NEW — window-aggregate (cycle buckets, byte counts)
PktTypePerfHist   = 4'hE   // NEW — histogram bucket counts
```

(`4'hD`/`4'hE` are currently unused in `monitor_common_pkg.sv`; `4'hF` is `PktTypeDebug`.)

### 3.1 `PktTypePerf` (existing — clean up the placeholders)

Keep all 16 slots as "one event = one value":

| code | name | meaning | data field |
|---:|---|---|---|
| 0x0 | `ADDR_LATENCY` | per-transaction addr-phase | 32b cycles |
| 0x1 | `DATA_LATENCY` | per-transaction data-phase | 32b cycles |
| 0x2 | `RESP_LATENCY` | per-transaction resp-phase | 32b cycles |
| 0x3 | `TOTAL_LATENCY` | per-transaction total | 32b cycles |
| 0x4 | `THROUGHPUT` | bytes-per-window | 64b bytes |
| 0x5 | `ERROR_RATE` | err/total ratio | 16b numerator + 16b denom |
| 0x6 | `ACTIVE_COUNT` | live outstanding | 8b |
| 0x7 | `COMPLETED_COUNT` | window cumulative | 32b |
| 0x8 | `ERROR_COUNT` | window cumulative | 32b |
| 0x9 | `BANDWIDTH_UTIL` | productive_cycles/window_cycles × 100 | 16b pct, 16b scale |
| 0xA | `QUEUE_DEPTH` | avg trans_mgr fill | 8b |
| 0xB | `BURST_EFFICIENCY` | bytes vs ideal | 16b pct, 16b scale |
| 0xC,0xD | reserved | | |
| 0xE | `READ_WRITE_RATIO` | for combined mons | 16b r, 16b w |
| 0xF | `USER_DEFINED` | escape hatch | 64b free |

### 3.2 `PktTypePerfWin` (NEW — window-aggregate)

One packet emitted at window-end per channel (or aggregate). One event_code per metric; multiple codes fit because each is `event_data`-sized:

| code | name | data field |
|---:|---|---|
| 0x0 | `WIN_END` | window total cycles |
| 0x1 | `PROD_CYCLES` | productive (`v && r`) cycles |
| 0x2 | `BP_CYCLES` | backpressure (`v && !r`) cycles |
| 0x3 | `STARV_CYCLES` | starvation (`!v && r`) cycles |
| 0x4 | `IDLE_CYCLES` | idle (`!v && !r`) cycles |
| 0x5 | `BEAT_COUNT` | productive beats (= prod_cycles for single-beat) |
| 0x6 | `BYTE_COUNT` | bytes (beats × `1<<axsize`, masked by `wstrb`) |
| 0x7 | `BURST_COUNT` | AW/AR handshake count |
| 0x8 | `WIN_START` | timestamp of window start (cycle counter snapshot) |
| 0x9 | `CHAN_PROD` | per-channel productive (for id-aware mons) |
| 0xA | `CHAN_STARV` | per-channel starvation |
| 0xB | `CHAN_BP` | per-channel backpressure |
| 0xC..F | reserved | |

Channel-id field in the standard packet header carries the channel for `CHAN_*` codes. The aggregate codes (0x1..0x8) ignore channel_id.

### 3.3 `PktTypePerfHist` (NEW — histogram)

`event_code[7:4]` selects which histogram, `event_code[3:0]` selects which bucket. Bucket boundaries are powers of 2 for cheap decode:

```
bucket  0 :  <    2 cycles
bucket  1 : <    4
bucket  2 : <    8
bucket  3 : <   16
bucket  4 : <   32
bucket  5 : <   64
bucket  6 : <  128
bucket  7 : <  256
bucket  8 : <  512
bucket  9 : < 1024
bucket 10 : < 2048
bucket 11 : < 4096
bucket 12 : < 8192
bucket 13 : <16384
bucket 14 : <32768
bucket 15 : ≥32768
```

Histogram select (upper nibble):
- `0x0`: addr-phase latency
- `0x1`: data-phase latency
- `0x2`: resp-phase latency

So a histogram emission is 16 packets (one per bucket), each carrying the bucket count in `event_data`. Or batched into 4 packets carrying 4 bucket counts each (16-bit per bucket, 4 buckets × 16b = 64b fits one packet); preferred. RFC: **batched, 4 packets per histogram**.

Channel-id field carries the channel for per-channel histograms.

## 4 · Window control

New CSR fields (in `axi_monitor_base` configuration block):

```sv
input  logic [2:0]   cfg_start_event_sel,   // see below
input  logic [2:0]   cfg_end_event_sel,
input  logic         cfg_start_trigger,     // pulse (for go-bit / engine triggers)
input  logic         cfg_end_trigger,
input  logic         cfg_window_force_close, // software override
output logic         window_active,
output logic [31:0]  window_cycles,         // running count while active
```

**Start events (3'b):**
- `000` software trigger (`cfg_start_trigger` pulse)
- `001` first AR/AW handshake since cfg_perf_enable went high
- `010` `cfg_perf_enable` rising edge
- `011` first productive beat (`v && r`)
- `100` external trigger pin (passthrough of `cfg_start_trigger`)
- others reserved

**End events (3'b):**
- `000` software trigger (`cfg_end_trigger`)
- `001` last RLAST/B since window opened
- `010` window_cycle counter hits `cfg_window_max_cycles` (auto-close)
- `011` `cfg_perf_enable` falling edge
- `100` external trigger
- others reserved

Window state machine: closed → arm-on-start → active → close-on-end → emit-packets → idle. While `active`, the four bucket counters run free. On close, the reporter emits the `WIN_END` packet first, then `PROD/BP/STARV/IDLE/BEAT/BYTE/BURST_COUNT` packets, then histograms.

## 5 · Hardware cost (per monitor instance)

- **Cycle buckets (4 × 32-bit accumulators):** 4 incrementers gated by the four `valid/ready` combos, 128 flops. ~30 LUTs.
- **Beat counter:** = productive_cycles; no extra cost.
- **Byte counter:** needs `1 << axsize` decode + add. 32-bit accumulator. ~50 LUTs.
- **Per-channel buckets:** multiply above by `1 << CHAN_WIDTH` (gated by per-id valid/ready). For 8 channels: ~240 LUTs + 1024 flops.
- **Latency histograms:** 3 histograms × 16 buckets × 16-bit counters = 768 flops + decode. ~200 LUTs.
- **Window control SM:** ~20 LUTs + 40 flops.
- **Output packet emission:** reuses existing reporter state machine.

**Total per monitor: ~500 LUTs + 2000 flops** for an 8-channel monitor with full instrumentation. Roughly equal to what `axi_bus_meter.sv` already costs (and we delete that), so net is approximately break-even.

## 6 · Implementation stages

Each stage is one commit, each lint-clean.

**Stage A — package + window control:**
- Add `PktTypePerfWin`, `PktTypePerfHist` to `monitor_common_pkg.sv`
- Add `PERFWIN_*`, `PERFHIST_*` enum codes to `monitor_amba4_pkg.sv`
- Add window-control CSR ports + window state machine to `axi_monitor_base.sv` (no counter logic yet — just the window machinery)
- Add `window_active`, `window_cycles` outputs to the four wrapper variants

**Stage B — four cycle buckets + beat/byte counters:**
- Aggregate counters in `axi_monitor_base.sv` (no per-channel breakdown yet)
- Emit `WIN_END/PROD/BP/STARV/IDLE/BEAT/BYTE/BURST_COUNT` packets via reporter
- New cfg bit: `cfg_emit_buckets`

**Stage C — per-channel buckets:**
- Gate counters by `axi_id[CHAN_WIDTH-1:0]`
- New parameter: `PER_CHANNEL_BUCKETS` (default 0, opt-in)
- Emit `CHAN_PROD/STARV/BP` packets

**Stage D — latency histograms:**
- Bucket-decode the existing `addr_latency`, `data_latency`, `resp_latency` per-transaction values into 3 × 16-bucket count arrays
- Emit `PerfHist` packets (4 batched per histogram)
- New cfg bit: `cfg_emit_histograms`

**Stage E — integration + scattered-tracker retirement:**
- Wire the new window-control + counters in the stream_char_harness monitor instances
- Update host-side log parser (`run_characterization.py`) to consume the new MonBus packets
- Delete `axi_bus_meter.sv`
- Mark `sram_chan_tracker.sv` as sim-debug-only (already gated by `ENHANCED_DEBUG`)

**Stage F — AXIL parity + sim regression:**
- Mirror the changes in `axil4_monitor_*` / wrappers
- Update existing AXI monitor sim tests to assert the new packet types
- Run TEST_LEVEL=FULL regression on stream_char to confirm no behavior change

**Stage G — `cfg_emit_transitions` (debug mode):**
- Per-cycle `valid` and `ready` edge events emitted as low-rate MonBus packets, gated by `cfg_emit_transitions` (off by default — high bandwidth)

## 7 · What we are explicitly NOT doing

- **Sliding-window analysis in hardware.** Software does that from the cumulative counters between window emissions.
- **Cross-bus correlation.** Each monitor reports its own bus. Software (or a future tiny correlator module) joins source-AR to dest-W using transaction IDs.
- **Engine-internal events as monitor codes.** The monitor takes `start_trigger`/`end_trigger` inputs; what those mean is the engine's responsibility. `descriptor_count_q` from the doc Section 4 lives in the engine (already in scheduler), not the monitor.

## 8 · Section-4 doc → RFC mapping (for the user's review)

| Section 4 primitive | Lives in |
|---|---|
| `start_cycle_q` | `window_active` SM (stage A) |
| `end_cycle_q` | implicit in WIN_END packet (stage A) |
| `window_active_q` | stage A output port |
| `productive/bp/starv/idle_cycles_q` | stage B counters |
| `descriptor_count_q` | engine (scheduler) — not monitor; comes via `start_trigger` if user wants it as a window event |
| `burst_count_q` | stage B counter |
| `beat_count_q` | stage B (= productive_cycles) |
| `bytes_count_q` | stage B counter |
| `descriptor_fetch_latency`, `first_beat_latency`, `last_beat_to_done_latency` | stage D histograms (built on existing trans_mgr timestamps) |
| `start_event_sel`, `end_event_sel` | stage A cfg ports |

All Section 4 primitives mapped to a stage. No primitive falls outside the monitor framework.

## 9 · Open questions

1. **AXI-Lite has no `axi_id`.** Per-channel buckets there must use a different discriminator. For now: AXIL monitors report aggregate only (`PER_CHANNEL_BUCKETS=0`). Acceptable?
2. **Window-active counter width.** 32-bit at 100 MHz = ~43 s before wrap. For long-running characterization, the WIN_END packet's `window_cycles` field would saturate. Auto-close at 2^31 cycles (≈ 21 s) and reopen? Or 48-bit counter (cheap)?
3. **Histogram bucket counter width.** 16-bit per bucket caps at 65 536 transactions per window. At ≈1000 trans / window for our workload, fine. For long windows or batch-test scenarios, want 24 or 32 bit?
4. **Reporter back-pressure.** WIN_END emission today is 1 packet; with stages B+C+D it's potentially 30+ packets at once. MonBus FIFO depth in the integrating block must be sized. Default FIFO depth bump?
