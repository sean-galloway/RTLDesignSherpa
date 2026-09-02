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

# AXIL4 Slave Write with Monitoring

**Module:** `axil4_slave_wr_mon.sv`
**Location:** `rtl/amba/axil4/`
**Status:** Production Ready

---

## Overview

Combines **[axil4_slave_wr](../axil4/axil4_slave_wr.md)** with **axi_monitor_filtered** for slave-side write monitoring.

Key features:

- All features of **axil4_slave_wr**
- Slave-side write monitoring (AW, W, B channels)
- Backend write latency tracking
- 2-level filtering (packet-type masks, then per-event-code masks) and error detection

---

## Parameters

In addition to all [axil4_slave_wr](../axil4/axil4_slave_wr.md) parameters:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `UNIT_ID` | int | 2 | Unit ID (2 = slaves) |
| `AGENT_ID` | int | 21 | Agent ID (slave write agent) |
| `USE_MONITOR` | bit | — | Synthesis-time monitor enable |
| `ACTIVE_TRANS_THRESHOLD` | int | `MAX_TRANSACTIONS/2` | Threshold-packet trip point; replaces the former hardwired value |
| `ENABLE_FILTERING` | bit | 1 | Enable packet filtering: two active drop levels (packet-type masks, then per-event-code masks) |
| `ADD_PIPELINE_STAGE` | bit | 0 | Insert a register stage for timing closure. Costs a cycle of latency. |
| `ACLK_MHZ` | int | 100 | Clock frequency in MHz; builds the microsecond tick LUT in `counter_freq_invariant`. **Leave `ACLK_MHZ` at 100 on a 90 MHz part and every us-denominated timeout is wrong, silently** |
| `CFI_MIN_FREQ_MHZ` | int | `ACLK_MHZ` | Lowest frequency the tick LUT must cover (dynamic-frequency builds) |
| `CFI_MAX_FREQ_MHZ` | int | `ACLK_MHZ` | Highest frequency the tick LUT must cover |
| `USE_WDATA_ORDER_Q` | bit | 0 | Write-data ordering queue |
| `NUM_BANKS` | int | 1 | Transaction-table banking. **`NUM_BANKS` > 1 on a WRITE monitor requires `USE_WDATA_ORDER_Q=1`**, or `axi_monitor_trans_mgr` fails elaboration |
| `ADDR_FILTER_ENABLE` | bit | 0 | Synthesises the address-range report filter; the `cfg_addr_filter_*` ports arm it at runtime |
| `N_ADDR_RANGES` | int | — | Address-range comparator count |
| `ID_FILTER_ENABLE` | bit | 0 | Per-instance ID-slice filter, inherited from the shared monitor core. **Leave `ID_FILTER_ENABLE` at 0 on AXI4-Lite.** This wrapper hardwires `cmd_id`/`data_id`/`resp_id` to `1'b0` because AXI4-Lite has no ID signals, so enabling the filter with an `ID_MATCH_BASE` above 0 makes `id_owned(0)` false for every transaction and silently drops ALL monitoring rather than narrowing it |
| `ID_MATCH_BASE` | int | 0 | ID-slice filter base |
| `ID_MATCH_COUNT` | int | 0 | ID-slice filter count (0 = all IDs) |
| `SKID_DEPTH_AW` | int | 2 | AW channel skid-buffer depth, in entries. Legal range 2..8 inclusive; odd depths are legal |
| `SKID_DEPTH_W` | int | 2 | W channel skid-buffer depth, in entries. Legal range 2..8 inclusive; odd depths are legal |
| `SKID_DEPTH_B` | int | 2 | B channel skid-buffer depth, in entries. Legal range 2..8 inclusive; odd depths are legal |

Others same as **[axil4_master_rd_mon](axil4_master_rd_mon.md#additional-parameters)**.

Also includes the synthesis-cone parameters `ENABLE_ERROR_LOGIC`, `ENABLE_TIMEOUT_LOGIC`, `ENABLE_COMPL_LOGIC`, `ENABLE_THRESHOLD_LOGIC`, `ENABLE_PERF_LOGIC` (all default 1) and `ENABLE_DEBUG_LOGIC` (default 0), each dropping its detection cone when set to 0. `ENABLE_PERF_PACKETS` is tied `1'b1` and `ENABLE_DEBUG_MODULE` `1'b0` internally; the removed `CAM_PIPELINE` / `TRANS_CAM_PIPELINE` parameters no longer exist.

For complete parameter descriptions, see **[axil4_master_rd_mon](axil4_master_rd_mon.md#synthesis-cone-parameters)**.

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `AW` | `AXIL_ADDR_WIDTH` |
| `DW` | `AXIL_DATA_WIDTH` |

---

## Ports

Same as **[axil4_master_rd_mon](axil4_master_rd_mon.md)**, including the `cam_clear` control input (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]), the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control enables, and the performance-monitoring config/status ports (see [Performance Monitoring](#performance-monitoring)).

`cfg_freq_sel` (Input, 4) is also forwarded: the `counter_freq_invariant` LUT index that scales the 1 us timer tick, in which the microsecond timeouts are measured. With the default `CFI_MIN_FREQ_MHZ == CFI_MAX_FREQ_MHZ == ACLK_MHZ` every LUT entry is identical, so it has no effect until you give CFI a real MIN..MAX range.

---

## Functional Description

### Performance Monitoring

When performance monitoring is enabled, the wrapper forwards a **measurement-window state machine** plus a bank of W-channel (write-data) utilization counters to `axi_monitor_base`. All counters accumulate **only while a window is open** (`window_active = 1`) and hold their values between windows so the host can read a completed window's totals. `cfg_perf_enable` does NOT gate them: it selects the window start/end event (it is edge-detected for `cfg_start_event_sel` modes 010/011) and enables the perf PACKET class. The counters themselves advance whenever a window is open, enabled or not. `ENABLE_PERF_LOGIC = 0` does NOT drop them: the window FSM and its counters are unconditional `always_ff` blocks in `axi_monitor_base`, outside every generate. That parameter gates only `g_perf` in the reporter -- the legacy perf-packet cone and the two lifetime counters. `USE_MONITOR = 0` is what ties the perfmon outputs off.

> Avoid enabling completion (`cfg_compl_enable`) and performance (`cfg_perf_enable`) packets simultaneously under heavy traffic — the monitor bus sustains at most one packet per two cycles. Runtime-disabling either class is safe (terminal entries auto-retire; see [axi_monitor_reporter](../monitor/axi_monitor_reporter.md)); alternatively, `cfg_axi_pkt_mask` drops the packets while keeping marking and counting. See `docs/user-guides/AXI_Monitor_Configuration_Guide.md`.

#### The Measurement Window

A window is opened by a **start event** and closed by an **end event**:

- `cfg_start_event_sel` / `cfg_end_event_sel` (3-bit) select the event source (e.g. `3'b010` selects the `cfg_perf_enable` edge).
- `cfg_start_trigger` / `cfg_end_trigger` pulses fire the window directly from an engine or CSR.
- `cfg_window_force_close` is a software override that closes the window immediately.

While the window is open, `window_active` is high and `window_cycles` [31:0] free-runs, counting every clock elapsed inside the window.

#### Utilization Counters (W channel)

Every in-window cycle is classified by the W-channel valid/ready into exactly one of four buckets:

| Output | Width | Condition | Meaning |
|--------|:-----:|-----------|---------|
| `perf_prod_cycles`  | 32 | wvalid && wready   | productive beat transferred |
| `perf_bp_cycles`    | 32 | wvalid && !wready  | back-pressure (data offered, consumer not ready) |
| `perf_starv_cycles` | 32 | !wvalid && wready  | starvation (consumer ready, no valid data) |
| `perf_idle_cycles`  | 32 | !wvalid && !wready | idle |

The four buckets sum to `window_cycles`, so utilization = `perf_prod_cycles / window_cycles`.

#### Throughput Counters

| Output | Width | Meaning |
|--------|:-----:|---------|
| `perf_beat_count`  | 32 | data beats transferred (= `perf_prod_cycles`, 1 beat/cycle) |
| `perf_byte_count`  | 64 | bytes transferred = beats × (1 << AxSIZE); AXIL is fixed at `AxSIZE=3'b010` (4 bytes) |
| `perf_burst_count` | 32 | AW (write-address) handshakes |

**AXI4-Lite note:** every transaction is a single data beat (AWLEN is implicitly 0), so `perf_burst_count` counts AW handshakes = transactions and `perf_beat_count` equals the transaction count. Average burst length (`perf_beat_count / perf_burst_count`) is therefore always 1.

The perfmon config/status ports and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control inputs have the same directions/widths and semantics as the **[read-monitor port table](axil4_master_rd_mon.md#performance-monitoring-ports)** (only `perf_burst_count` counts AW handshakes here). As there, `cfg_debug_level`/`cfg_debug_mask`/`cfg_active_trans_threshold` are tied to constants internally and not exposed.

### Monitor Backpressure (block_ready)

`block_ready` is a flow-control net inside the wrapper, and it IS brought out: `debug_block_ready` is an output port of this module (the `_cg` wrapper ties it off, so use the base module when you need the tap). It goes low when the monitor's transaction-table occupancy reaches its blocking threshold (a function of `MAX_TRANSACTIONS`; the reporter FIFO depth `INTR_FIFO_DEPTH` has no path to it). The wrapper ANDs it into the upstream-facing `s_axil_awready` so a saturated monitor throttles new transactions at the handshake instead of dropping events.

- **Where the stall lands**: the upstream `s_axil_awready` is forced low until the monitor drains.
- **When `USE_MONITOR=0`**: `block_ready` is internally tied high, so the wrapper imposes no stall and runs at full bandwidth.
- **When `cfg_monitor_enable=0`**: the wrapper gate forces the upstream ready open, so a runtime-disabled monitor can never stall the datapath (the AXI4 monitors assert this as an in-RTL formal property,
  `ap_disabled_never_stalls`; this module has no `ifdef FORMAL` block of its
  own, so here the guarantee rests on the gate expression above, not a proof).

Recovery is guaranteed by the **saturation-recovery contract**: command-originated table entries are capped at `MAX_TRANSACTIONS - cmd_entry_reserve(MAX_TRANSACTIONS)` (reserve = 4 for tables of 16 or more, 0 below; the function lives in `monitor_common_pkg`), and `block_ready` re-asserts at occupancy `< MAX_TRANSACTIONS - (reserve - 1)` -- a threshold strictly ABOVE the command cap -- so a saturated table always drains back below the reopen point. Blocking throttles; it never deadlocks. Tables smaller than 16 keep full legacy allocation (small tables cannot spare slots) and trade the recovery guarantee for tracking capacity. The contract is verified by in-RTL formal properties (mutation-checked) and a 100-seed deliberately-undersized-table stream sweep; see [axi_monitor_base](../monitor/axi_monitor_base.md#flow-control-and-the-saturation-recovery-contract) for the canonical description.

Sizing note: a monitor on a bus shared by several channels/requesters must size `MAX_TRANSACTIONS` to cover `NUM_CHANNELS x per-channel outstanding` plus margin -- the per-channel limit alone makes the monitor throttle the shared master. Tables deeper than 64 also need Verilator's `--unroll-count` raised (default 64) in sim builds.

### Address-Range Checker

Identical to **[axil4_master_rd_mon](axil4_master_rd_mon.md#address-range-checker)** except the checker watches AW (write address) handshakes. The `cfg_addr_*` configuration inputs and monbus event encoding are the same. See the read monitor's Address-Range Checker section for full details.

### Packet filters

Two independent runtime filters cut monbus traffic without touching the
datapath. Both are inert until driven, which is the failure to watch for: the
build-time parameter only decides whether the logic is SYNTHESISED, and a
design that sets the parameter but leaves the `cfg_*` ports tied low filters
nothing and looks like the feature is broken.

**Address-range filter** — `ADDR_FILTER_ENABLE` (bit, default 0) builds it.

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_addr_filter_enable` | Input | 1 | High: suppress packets for transactions outside the window. Low: inert, whatever the parameter says |
| `cfg_addr_filter_low` | Input | `ADDR_WIDTH` | Window base, inclusive |
| `cfg_addr_filter_high` | Input | `ADDR_WIDTH` | Window limit, inclusive |

The verdict is latched per table entry at ALLOCATION, from the command
address, and held for that entry's life. Widening the window mid-flight does
not un-filter entries already admitted — which is what makes it safe to
reprogram live. Contrast the address-range CHECKER above, which re-evaluates
per command.

There is no runtime ID filter here. AXI-Lite has no transaction IDs, so this
wrapper ties `cfg_id_filter_enable` / `cfg_id_match_base` /
`cfg_id_match_count` off on the inner monitor rather than exposing them — a
filter keyed on a field the protocol lacks has nothing to match against.

---

## Waveforms

### Scenario 1: Slave Write Transaction

![Slave Write Basic](../../assets/WAVES/axil4_slave_wr_mon/slave_write_basic_001.png)

**WaveJSON:** [slave_write_basic_001.json](../../assets/WAVES/axil4_slave_wr_mon/slave_write_basic_001.json)

**Key Observations:**
- Slave perspective: Receive AW+W simultaneously
- Slave commits write to backend storage
- Slave generates B response with BRESP=OKAY
- Monitor tracks backend write latency

### Scenario 2: Slave Write Error (DECERR)

![Slave Write DECERR](../../assets/WAVES/axil4_slave_wr_mon/slave_write_decerr_001.png)

**WaveJSON:** [slave_write_decerr_001.json](../../assets/WAVES/axil4_slave_wr_mon/slave_write_decerr_001.json)

**Key Observations:**
- Invalid address detected by slave
- Write data received but not committed
- Slave returns BRESP=DECERR
- Monitor generates ERROR packet

### Scenario 3: Slave Write with Wait States

![Slave Write Wait](../../assets/WAVES/axil4_slave_wr_mon/slave_write_wait_001.png)

**WaveJSON:** [slave_write_wait_001.json](../../assets/WAVES/axil4_slave_wr_mon/slave_write_wait_001.json)

**Key Observations:**
- Slave not ready: AWREADY/WREADY deasserted
- Master holds AW+W until slave accepts
- Backend write processing delay
- Monitor tracks full write latency including wait states

---

## Usage Example

```systemverilog
axil4_slave_wr_mon #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .UNIT_ID(2),
    .AGENT_ID(21),
    .MAX_TRANSACTIONS(8)
) u_axil_slave_wr_mon (
    // Slave AXIL write interfaces
    // Monitor configuration and bus
);
```

---

## Related Modules

- **[axil4_slave_wr](../axil4/axil4_slave_wr.md)** - Base functional module
- **[axil4_slave_rd_mon](axil4_slave_rd_mon.md)** - Read monitor counterpart
- **[AXI4 Slave Write Mon](../axi4/axi4_slave_wr_mon.md)** - Full AXI4 reference

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to AXIL4 Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
