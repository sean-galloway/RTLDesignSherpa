<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# AXIL4 Master Read with Monitoring

**Module:** `axil4_master_rd_mon.sv`
**Location:** `rtl/amba/axil4/`
**Status:** ✅ Production Ready

---

## Overview

Combines **[axil4_master_rd](axil4_master_rd.md)** with the core **axi_monitor_filtered** for transaction monitoring. Simplified for AXI4-Lite (single-beat, no burst, fixed ID=0).

### Key Features

- ✅ All features of base **axil4_master_rd** module
- ✅ **Integrated Monitoring:** Uses shared axi_monitor_filtered (rtl/amba/shared/)
- ✅ **3-Level Filtering:** Packet type masks, error routing, event masking
- ✅ **Error Detection:** Protocol violations, timeouts, orphans
- ✅ **128-bit Monitor Bus:** Standardized packet format paired with 64-bit side-band timestamp
- ✅ **Reduced Complexity:** MAX_TRANSACTIONS=8 (vs 16-32 for AXI4)

---

## Additional Parameters (Beyond Base Module)

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `UNIT_ID` | int | 1 | 4-bit unit identifier (masters typically=1) |
| `AGENT_ID` | int | 10 | 8-bit agent identifier for this monitor |
| `MAX_TRANSACTIONS` | int | 8 | Max outstanding transactions (reduced for AXIL) |
| `ENABLE_FILTERING` | bit | 1 | Enable 3-level packet filtering |
| `ADD_PIPELINE_STAGE` | bit | 0 | Add register stage for timing closure |
| `USE_MONITOR` | bit | 1 | Synthesis-time monitor enable. 0 = omit monitor and tie outputs to safe non-blocking defaults; 1 = full monitor functionality. |
| `N_ADDR_RANGES` | int | 0 | Number of address-range comparators. 0 = checker omitted (zero area). >0 = N independent [low, high] ranges; hits emit PktTypeError + AXI_ERR_ADDR_RANGE on monbus. |

### Synthesis-Cone Parameters

Each detection cone can be compiled out to save area. These are forwarded to `axi_monitor_base`; by default the classic cones are on and the debug cone is off.

| Parameter | Type | Default | Effect when 0 |
|-----------|------|---------|---------------|
| `ENABLE_ERROR_LOGIC` | bit | 1 | Drop the error-detection cone |
| `ENABLE_TIMEOUT_LOGIC` | bit | 1 | Drop the timeout cone **and** the `axi_monitor_timeout` instance |
| `ENABLE_COMPL_LOGIC` | bit | 1 | Drop the completion cone |
| `ENABLE_THRESHOLD_LOGIC` | bit | 1 | Drop the threshold cone |
| `ENABLE_PERF_LOGIC` | bit | 1 | Drop the perfmon window + counters |
| `ENABLE_DEBUG_LOGIC` | bit | 0 | (off by default) drop the debug cone |

> The former `CAM_PIPELINE` / `TRANS_CAM_PIPELINE` parameters were removed — the transaction CAM is now always pipelined. Inside this wrapper `ENABLE_PERF_PACKETS` is tied to `1'b1` (perf packet path always instantiated, gated by `ENABLE_PERF_LOGIC`) and `ENABLE_DEBUG_MODULE` is tied to `1'b0`.

---

## Performance Monitoring

When performance monitoring is enabled, the wrapper forwards a **measurement-window state machine** plus a bank of R-channel (read-data) utilization counters to `axi_monitor_base`. All counters accumulate **only while a window is open** (`window_active = 1`) and hold their values between windows so the host can read a completed window's totals. The counters advance only while `cfg_perf_enable = 1`; `ENABLE_PERF_LOGIC = 0` drops the whole block at synthesis.

> ⚠️ Never enable completion (`cfg_compl_enable`) and performance (`cfg_perf_enable`) packets simultaneously — see `docs/AXI_Monitor_Configuration_Guide.md`.

### The Measurement Window

A window is opened by a **start event** and closed by an **end event**:

- `cfg_start_event_sel` / `cfg_end_event_sel` (3-bit) select the event source (e.g. `3'b010` selects the `cfg_perf_enable` edge).
- `cfg_start_trigger` / `cfg_end_trigger` pulses fire the window directly from an engine or CSR.
- `cfg_window_force_close` is a software override that closes the window immediately.

While the window is open, `window_active` is high and `window_cycles` [31:0] free-runs, counting every clock elapsed inside the window.

### Utilization Counters (R channel)

Every in-window cycle is classified by the R-channel valid/ready into exactly one of four buckets:

| Output | Width | Condition | Meaning |
|--------|:-----:|-----------|---------|
| `perf_prod_cycles`  | 32 | rvalid && rready   | productive beat transferred |
| `perf_bp_cycles`    | 32 | rvalid && !rready  | back-pressure (data offered, consumer not ready) |
| `perf_starv_cycles` | 32 | !rvalid && rready  | starvation (consumer ready, no valid data) |
| `perf_idle_cycles`  | 32 | !rvalid && !rready | idle |

The four buckets sum to `window_cycles`, so utilization = `perf_prod_cycles / window_cycles`.

### Throughput Counters

| Output | Width | Meaning |
|--------|:-----:|---------|
| `perf_beat_count`  | 32 | data beats transferred (= `perf_prod_cycles`, 1 beat/cycle) |
| `perf_byte_count`  | 64 | bytes transferred = beats × (1 << AxSIZE); AXIL is fixed at `AxSIZE=3'b010` (4 bytes) |
| `perf_burst_count` | 32 | AR (read-address) handshakes |

**AXI4-Lite note:** every transaction is a single data beat (ARLEN is implicitly 0), so `perf_burst_count` counts AR handshakes = transactions and `perf_beat_count` equals the transaction count. Average burst length (`perf_beat_count / perf_burst_count`) is therefore always 1.

---

## Monitor Backpressure (block_ready)

The monitor exposes a `block_ready` signal that goes low when its internal FIFO is saturated and cannot accept a new in-flight transaction. The wrapper ANDs `block_ready` into the upstream-facing `fub_axil_arready` so a saturated monitor stalls new transactions on the wire instead of dropping events.

- **Where the stall lands**: the upstream `fub_axil_arready` is forced low until the monitor drains.
- **When `USE_MONITOR=0`**: `block_ready` is internally tied high, so the wrapper imposes no stall and runs at full bandwidth.

This replaces a previous bug where `block_ready` was left unconnected and a full monitor FIFO would silently lose events.

---

## Address-Range Checker

The wrapper can be parameterized with `N_ADDR_RANGES > 0` to instantiate an N-comparator address-range checker that watches every accepted AR handshake and emits a `PktTypeError` monbus packet (event code `AXI_ERR_ADDR_RANGE = 8'h0D`) when an address falls inside any of the configured `[low, high]` inclusive ranges.

**Config inputs (active only when `N_ADDR_RANGES > 0`):**
- `cfg_addr_check_enable` — master on/off for the checker.
- `cfg_addr_range_enable[N-1:0]` — per-range enable bit.
- `cfg_addr_range_low[N-1:0][AXIL_ADDR_WIDTH-1:0]` — inclusive low bound for each range.
- `cfg_addr_range_high[N-1:0][AXIL_ADDR_WIDTH-1:0]` — inclusive high bound for each range.

**Event encoding** (within the standard 128-bit `monitor_packet_t`, event_data field):
- `packet_type` = `PktTypeError` (4'h0)
- `protocol`    = AXI (3'b000)
- `event_code`  = `AXI_ERR_ADDR_RANGE` (8'h0D)
- `event_data[63:60]` = `range_index` (4 bits; supports up to 16 ranges)
- `event_data[59:0]`  = full matched address (up to 60 bits, zero-padded if narrower)

**Exact match:** set `cfg_addr_range_low[i] == cfg_addr_range_high[i]`.

**Filtering:** the existing `cfg_axi_error_mask[13]` bit masks this event code; set it high to suppress range packets without disabling other errors. No new mask wiring needed.

**Per-range coalescing:** if a range hits again before its packet has been emitted, the latched address is overwritten (latest hit wins). One packet per cycle drains the pending mask via a lowest-index priority encoder. Distinct ranges never lose events; under sustained per-range bursts, only the latest address per range is reported per emission cycle.

---

## Additional Ports (Beyond Base Module)

### Monitor Configuration
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_monitor_enable` | Input | 1 | Enable monitoring |
| `cam_clear` | Input | 1 | Synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]) |
| `cfg_error_enable` | Input | 1 | Enable error packets |
| `cfg_timeout_enable` | Input | 1 | Enable timeout detection |
| `cfg_compl_enable` | Input | 1 | Enable transaction-completion packets |
| `cfg_threshold_enable` | Input | 1 | Enable threshold-crossed packets |
| `cfg_perf_enable` | Input | 1 | Enable performance packets |
| `cfg_debug_enable` | Input | 1 | Enable debug/trace packets (the 6th "debug cone" reporter sub-block) |
| `cfg_timeout_cycles` | Input | 16 | Timeout threshold (cycles) |
| `cfg_latency_threshold` | Input | 32 | Latency alert threshold |

> The debug cone is the 6th reporter sub-block (`axi_monitor_reporter_debug`), enabled by `cfg_debug_enable` and synthesized only when `ENABLE_DEBUG_LOGIC = 1`. The related `cfg_debug_level` (4b), `cfg_debug_mask` (16b), and `cfg_active_trans_threshold` (16b) inputs of `axi_monitor_base` are **not** exposed on this AXIL wrapper — they are tied to constants (`4'h0`, `16'h0`, `16'd4`) internally.

### Performance Monitoring Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_start_event_sel` | Input | 3 | Window **start** event source select |
| `cfg_end_event_sel` | Input | 3 | Window **end** event source select |
| `cfg_start_trigger` | Input | 1 | Pulse: open the measurement window |
| `cfg_end_trigger` | Input | 1 | Pulse: close the measurement window |
| `cfg_window_force_close` | Input | 1 | Software override: force the window closed |
| `window_active` | Output | 1 | High while a measurement window is open |
| `window_cycles` | Output | 32 | Cycles elapsed in the current window |
| `perf_prod_cycles` | Output | 32 | valid && ready cycles |
| `perf_bp_cycles` | Output | 32 | valid && !ready cycles (back-pressure) |
| `perf_starv_cycles` | Output | 32 | !valid && ready cycles (starvation) |
| `perf_idle_cycles` | Output | 32 | !valid && !ready cycles |
| `perf_beat_count` | Output | 32 | data beats transferred |
| `perf_byte_count` | Output | 64 | bytes transferred |
| `perf_burst_count` | Output | 32 | AR (address-phase) handshakes |

> When perfmon is unused, the integrating block ties `cfg_start_event_sel`/`cfg_end_event_sel` to `3'b111` and the remaining `cfg_*` perfmon inputs to 0. When `USE_MONITOR = 0` all perfmon outputs are tied to 0.

### Filtering Masks (7 masks total)
| Port | Description |
|------|-------------|
| `cfg_axi_pkt_mask` | Drop mask for packet types |
| `cfg_axi_err_select` | Error select mask |
| `cfg_axi_timeout_mask` | Timeout event mask |
| `cfg_axi_compl_mask` | Completion event mask |
| `cfg_axi_perf_mask` | Performance event mask |
| `cfg_axi_debug_mask` | Debug event mask |
| `cfg_axi_full_mask` | Full event mask |

### Monitor Bus Output
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `monbus_pkt_valid` | Output | 1 | Monitor packet valid |
| `monbus_pkt_ready` | Input | 1 | Downstream ready |
| `monbus_pkt_data` | Output | 128 | `monitor_packet_t` (128-bit format) |
| `monbus_timestamp` | Output | 64 | `monbus_timestamp_t` paired atomically with `monbus_pkt_data` |
| `i_mon_time` | Input | 64 | Free-running counter from `monbus_axil_group`, sampled at packet emission |

### Status
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `busy` | Output | 1 | Interface active |
| `active_transactions` | Output | 8 | Current outstanding count |
| `error_count` | Output | 16 | Cumulative error count |

---

## Usage Example

```systemverilog
axil4_master_rd_mon #(
    // Base parameters
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),

    // Monitor parameters
    .UNIT_ID(1),
    .AGENT_ID(10),
    .MAX_TRANSACTIONS(8),
    .ENABLE_FILTERING(1)
) u_axil_rd_mon (
    .aclk(axi_clk),
    .aresetn(axi_resetn),

    // AXIL interfaces (same as axil4_master_rd)
    .fub_axil_araddr(cpu_araddr),
    // ... other AR/R signals ...

    // Monitor configuration
    .cfg_monitor_enable(1'b1),
    .cfg_error_enable(1'b1),
    .cfg_timeout_enable(1'b1),
    .cfg_perf_enable(1'b0),      // Avoid congestion
    .cfg_timeout_cycles(16'd1000),
    .cfg_latency_threshold(32'd500),

    // Filtering masks
    .cfg_axi_pkt_mask(16'b1111_1111_0000_0011),
    // ... other masks ...

    // Monitor bus
    .monbus_pkt_valid(mon_valid),
    .monbus_pkt_ready(mon_ready),
    .monbus_pkt_data(mon_data)
);
```

---

## Timing Diagrams

### Scenario 1: Single-Beat Read Transaction

![Single Beat Read](../../assets/WAVES/axil4_master_rd_mon/single_beat_read_001.png)

**WaveJSON:** [single_beat_read_001.json](../../assets/WAVES/axil4_master_rd_mon/single_beat_read_001.json)

**Key Observations:**
- AR channel handshake: ARVALID asserted, ARREADY responds
- R channel response: Slave returns data with RRESP=OKAY
- Monitor generates completion packet when R phase completes
- Single-beat transaction: No burst length (implicit ARLEN=0)

### Scenario 2: Read Error (SLVERR)

![Read Error SLVERR](../../assets/WAVES/axil4_master_rd_mon/read_error_slverr_001.png)

**WaveJSON:** [read_error_slverr_001.json](../../assets/WAVES/axil4_master_rd_mon/read_error_slverr_001.json)

**Key Observations:**
- Invalid address triggers RRESP=SLVERR
- Monitor detects error response and generates ERROR packet
- Transaction completes despite error (data may be undefined)
- Error packet includes address and response code

### Scenario 3: Read with Backpressure

![Read Backpressure](../../assets/WAVES/axil4_master_rd_mon/read_backpressure_001.png)

**WaveJSON:** [read_backpressure_001.json](../../assets/WAVES/axil4_master_rd_mon/read_backpressure_001.json)

**Key Observations:**
- Master not ready: RREADY deasserted
- Slave holds RVALID until RREADY=1
- Monitor tracks extended latency
- Completion packet generated after handshake

---

## AXI4-Lite Simplifications

**vs Full AXI4 Monitoring:**
- **Fixed ID:** Always ID=0 (no out-of-order tracking)
- **Single-Beat:** No burst handling (ARLEN implicitly 0)
- **Reduced Tables:** MAX_TRANSACTIONS=8 (vs 16-32 for AXI4)
- **Same Infrastructure:** Uses axi_monitor_filtered like AXI4

---

## Related Documentation

### Base Module
- **[axil4_master_rd](axil4_master_rd.md)** - Functional module documentation

### Monitor Infrastructure
- **[AXI4 Master Read Mon](../axi4/axi4_master_rd_mon.md)** - Full AXI4 monitoring (detailed reference)
- **axi_monitor_filtered** - Core monitor engine (rtl/amba/shared/)
- **[Monitor Configuration Guide](../shared/axi_monitor_base.md)** - Configuration strategies

### Related Modules
- **[axil4_master_wr_mon](axil4_master_wr_mon.md)** - Master write with monitoring
- **[axil4_slave_rd_mon](axil4_slave_rd_mon.md)** - Slave read with monitoring

---

**Last Updated:** 2025-10-24

---

## Navigation

- **[← Back to AXIL4 Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
