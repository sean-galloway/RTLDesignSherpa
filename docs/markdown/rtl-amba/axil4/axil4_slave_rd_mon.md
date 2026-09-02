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

# AXIL4 Slave Read with Monitoring

**Module:** `axil4_slave_rd_mon.sv`
**Location:** `rtl/amba/axil4/`
**Status:** Production Ready

---

## Overview

Combines **[axil4_slave_rd](../axil4/axil4_slave_rd.md)** with **axi_monitor_filtered** for slave-side read monitoring.

### Key Features

- All features of **axil4_slave_rd**
- Slave-side monitoring (backend latency tracking)
- 2-level filtering (packet-type masks, then per-event-code masks) and error detection
- Simplified for AXI4-Lite (MAX_TRANSACTIONS=8)

---

## Parameters

Identical to **[axil4_master_rd_mon](axil4_master_rd_mon.md#additional-parameters)** including `N_ADDR_RANGES`, but typically:
- `UNIT_ID = 2` (slaves use different unit ID)
- `AGENT_ID = 20` (slave agent IDs)
- `USE_MONITOR` (synthesis-time monitor enable)
- `ACTIVE_TRANS_THRESHOLD` (default `MAX_TRANSACTIONS/2`): threshold-packet trip point, replaces the former hardwired value
- `ENABLE_FILTERING` (default 1) and `ADD_PIPELINE_STAGE` (default 0)
- `ACLK_MHZ` (default 100) and `CFI_MIN_FREQ_MHZ` / `CFI_MAX_FREQ_MHZ` (default `ACLK_MHZ`) -- the microsecond tick LUT. **Leave `ACLK_MHZ` at 100 on a 90 MHz part and every us-denominated timeout is wrong, silently**
- `USE_WDATA_ORDER_Q` (default 0) and `NUM_BANKS` (default 1) -- **`NUM_BANKS` > 1 on a WRITE monitor requires `USE_WDATA_ORDER_Q=1`**, or `axi_monitor_trans_mgr` fails elaboration
- `ADDR_FILTER_ENABLE` (default 0) -- synthesises the address-range report filter; the `cfg_addr_filter_*` ports arm it at runtime
- `ID_FILTER_ENABLE` (default 0), `ID_MATCH_BASE` (default 0) and `ID_MATCH_COUNT` (default 0 = all IDs) -- the per-instance ID-slice filter, inherited from the shared monitor core. **Leave `ID_FILTER_ENABLE` at 0 on AXI4-Lite.** This wrapper hardwires `cmd_id`/`data_id`/`resp_id` to `1'b0` because AXI4-Lite has no ID signals, so enabling the filter with an `ID_MATCH_BASE` above 0 makes `id_owned(0)` false for every transaction and silently drops ALL monitoring rather than narrowing it
- `SKID_DEPTH_AR` (default 2), `SKID_DEPTH_R` (default 4) -- skid-buffer depth per channel. Legal range 2..8 inclusive; odd depths are legal

Also includes the synthesis-cone parameters `ENABLE_ERROR_LOGIC`, `ENABLE_TIMEOUT_LOGIC`, `ENABLE_COMPL_LOGIC`, `ENABLE_THRESHOLD_LOGIC`, `ENABLE_PERF_LOGIC` (all default 1) and `ENABLE_DEBUG_LOGIC` (default 0), each dropping its detection cone when set to 0. `ENABLE_PERF_PACKETS` is tied `1'b1` and `ENABLE_DEBUG_MODULE` `1'b0` internally; the removed `CAM_PIPELINE` / `TRANS_CAM_PIPELINE` parameters no longer exist.

For complete parameter descriptions including `N_ADDR_RANGES` and the synthesis-cone parameters, see **[axil4_master_rd_mon](axil4_master_rd_mon.md#synthesis-cone-parameters)**.

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

When performance monitoring is enabled, the wrapper forwards a **measurement-window state machine** plus a bank of R-channel (read-data) utilization counters to `axi_monitor_base`. All counters accumulate **only while a window is open** (`window_active = 1`) and hold their values between windows so the host can read a completed window's totals. `cfg_perf_enable` does NOT gate them: it selects the window start/end event (it is edge-detected for `cfg_start_event_sel` modes 010/011) and enables the perf PACKET class. The counters themselves advance whenever a window is open, enabled or not. `ENABLE_PERF_LOGIC = 0` does NOT drop them: the window FSM and its counters are unconditional `always_ff` blocks in `axi_monitor_base`, outside every generate. That parameter gates only `g_perf` in the reporter -- the legacy perf-packet cone and the two lifetime counters. `USE_MONITOR = 0` is what ties the perfmon outputs off.

> Avoid enabling completion (`cfg_compl_enable`) and performance (`cfg_perf_enable`) packets simultaneously under heavy traffic — the monitor bus sustains at most one packet per two cycles. Runtime-disabling either class is safe (terminal entries auto-retire; see [axi_monitor_reporter](../monitor/axi_monitor_reporter.md)); alternatively, `cfg_axi_pkt_mask` drops the packets while keeping marking and counting. See `docs/user-guides/AXI_Monitor_Configuration_Guide.md`.

#### The Measurement Window

A window is opened by a **start event** and closed by an **end event**:

- `cfg_start_event_sel` / `cfg_end_event_sel` (3-bit) select the event source (e.g. `3'b010` selects the `cfg_perf_enable` edge).
- `cfg_start_trigger` / `cfg_end_trigger` pulses fire the window directly from an engine or CSR.
- `cfg_window_force_close` is a software override that closes the window immediately.

While the window is open, `window_active` is high and `window_cycles` [31:0] free-runs, counting every clock elapsed inside the window.

#### Utilization Counters (R channel)

Every in-window cycle is classified by the R-channel valid/ready into exactly one of four buckets:

| Output | Width | Condition | Meaning |
|--------|:-----:|-----------|---------|
| `perf_prod_cycles`  | 32 | rvalid && rready   | productive beat transferred |
| `perf_bp_cycles`    | 32 | rvalid && !rready  | back-pressure (data offered, consumer not ready) |
| `perf_starv_cycles` | 32 | !rvalid && rready  | starvation (consumer ready, no valid data) |
| `perf_idle_cycles`  | 32 | !rvalid && !rready | idle |

The four buckets sum to `window_cycles`, so utilization = `perf_prod_cycles / window_cycles`.

#### Throughput Counters

| Output | Width | Meaning |
|--------|:-----:|---------|
| `perf_beat_count`  | 32 | data beats transferred (= `perf_prod_cycles`, 1 beat/cycle) |
| `perf_byte_count`  | 64 | bytes transferred = beats × (1 << AxSIZE); AXIL is fixed at `AxSIZE=3'b010` (4 bytes) |
| `perf_burst_count` | 32 | AR (read-address) handshakes |

**AXI4-Lite note:** every transaction is a single data beat (ARLEN is implicitly 0), so `perf_burst_count` counts AR handshakes = transactions and `perf_beat_count` equals the transaction count. Average burst length (`perf_beat_count / perf_burst_count`) is therefore always 1.

The perfmon config/status ports and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control inputs have the same directions/widths and semantics as the **[read-monitor port table](axil4_master_rd_mon.md#performance-monitoring-ports)**. As there, `cfg_debug_level`/`cfg_debug_mask`/`cfg_active_trans_threshold` are tied to constants internally and not exposed.

### Monitor Backpressure (block_ready)

`block_ready` is a flow-control net inside the wrapper, and it IS brought out: `debug_block_ready` is an output port of this module (the `_cg` wrapper ties it off, so use the base module when you need the tap). It goes low when the monitor's transaction-table occupancy reaches its blocking threshold (a function of `MAX_TRANSACTIONS`; the reporter FIFO depth `INTR_FIFO_DEPTH` has no path to it). The wrapper ANDs it into the upstream-facing `s_axil_arready` so a saturated monitor throttles new transactions at the handshake instead of dropping events.

- **Where the stall lands**: the upstream `s_axil_arready` is forced low until the monitor drains.
- **When `USE_MONITOR=0`**: `block_ready` is internally tied high, so the wrapper imposes no stall and runs at full bandwidth.
- **When `cfg_monitor_enable=0`**: the wrapper gate forces the upstream ready open, so a runtime-disabled monitor can never stall the datapath (the AXI4 monitors assert this as an in-RTL formal property,
  `ap_disabled_never_stalls`; this module has no `ifdef FORMAL` block of its
  own, so here the guarantee rests on the gate expression above, not a proof).

Recovery is guaranteed by the **saturation-recovery contract**: command-originated table entries are capped at `MAX_TRANSACTIONS - cmd_entry_reserve(MAX_TRANSACTIONS)` (reserve = 4 for tables of 16 or more, 0 below; the function lives in `monitor_common_pkg`), and `block_ready` re-asserts at occupancy `< MAX_TRANSACTIONS - (reserve - 1)` -- a threshold strictly ABOVE the command cap -- so a saturated table always drains back below the reopen point. Blocking throttles; it never deadlocks. Tables smaller than 16 keep full legacy allocation (small tables cannot spare slots) and trade the recovery guarantee for tracking capacity. The contract is verified by in-RTL formal properties (mutation-checked) and a 100-seed deliberately-undersized-table stream sweep; see [axi_monitor_base](../monitor/axi_monitor_base.md#flow-control-and-the-saturation-recovery-contract) for the canonical description.

Sizing note: a monitor on a bus shared by several channels/requesters must size `MAX_TRANSACTIONS` to cover `NUM_CHANNELS x per-channel outstanding` plus margin -- the per-channel limit alone makes the monitor throttle the shared master. Tables deeper than 64 also need Verilator's `--unroll-count` raised (default 64) in sim builds.

### Address-Range Checker

Identical to **[axil4_master_rd_mon](axil4_master_rd_mon.md#address-range-checker)** — monitors AR (read address) handshakes and emits address-range violation packets. See the master read monitor's section for full details.

### Packet filters

Two independent runtime filters cut monbus traffic without touching the
datapath. Both are inert until driven, which is the failure to watch for: the
build-time parameter only decides whether the logic is SYNTHESISED, and a
design that sets the parameter but leaves the `cfg_*` ports tied low filters
nothing and looks like the feature is broken.

**Address-range filter** — `ADDR_FILTER_ENABLE` (bit, default 0) builds it.

| Port | Width | Description |
|---|---|---|
| `cfg_addr_filter_enable` | 1 | High: suppress packets for transactions outside the window. Low: inert, whatever the parameter says |
| `cfg_addr_filter_low` | `ADDR_WIDTH` | Window base, inclusive |
| `cfg_addr_filter_high` | `ADDR_WIDTH` | Window limit, inclusive |

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

### Scenario 1: Slave Read Transaction

![Slave Read Basic](../../assets/WAVES/axil4_slave_rd_mon/slave_read_basic_001.png)

**WaveJSON:** [slave_read_basic_001.json](../../assets/WAVES/axil4_slave_rd_mon/slave_read_basic_001.json)

**Key Observations:**
- Slave perspective: Receive AR request from master
- Slave generates R response with data
- Monitor tracks backend read latency (AR → R delay)
- Completion packet indicates successful read

### Scenario 2: Slave Read Error (DECERR)

![Slave Read DECERR](../../assets/WAVES/axil4_slave_rd_mon/slave_read_decerr_001.png)

**WaveJSON:** [slave_read_decerr_001.json](../../assets/WAVES/axil4_slave_rd_mon/slave_read_decerr_001.json)

**Key Observations:**
- Invalid address detected by slave address decoder
- Slave returns RRESP=DECERR (decode error)
- Monitor generates ERROR packet
- Data value is don't-care when error occurs

### Scenario 3: Slave Read with Wait States

![Slave Read Wait](../../assets/WAVES/axil4_slave_rd_mon/slave_read_wait_001.png)

**WaveJSON:** [slave_read_wait_001.json](../../assets/WAVES/axil4_slave_rd_mon/slave_read_wait_001.json)

**Key Observations:**
- Slave not ready: ARREADY deasserted (wait states)
- Master holds ARVALID until slave accepts
- Backend read takes multiple cycles
- Monitor tracks full transaction latency

---

## Usage Examples
```systemverilog
axil4_slave_rd_mon #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .UNIT_ID(2),    // Slave unit ID
    .AGENT_ID(20),  // Slave agent ID
    .MAX_TRANSACTIONS(8)
) u_axil_slave_rd_mon (
    // Slave AXIL interfaces (s_axil_*, fub_*)
    // Monitor configuration and bus
);
```

---

## Timing Characteristics

### Buffer Depths and Latency

| Parameter | Default | Channel |
|-----------|---------|---------|
| `SKID_DEPTH_AR` | 2 entries | Skid depth on the AR channel |
| `SKID_DEPTH_R` | 4 entries | Skid depth on the R channel |

Each channel traverses one `gaxi_skid_buffer`. That module registers both
`rd_valid` and the storage array, so the **1-cycle input-to-output latency
applies on every transfer, including the unstalled case** -- there is no
combinational bypass from the upstream payload to the downstream one. Full
throughput (one transfer per cycle) is still sustained once the pipeline is
primed; the depth sets how much backpressure can be absorbed before it
propagates upstream, not the steady-state rate.

Legal depth range is 2..8 inclusive, odd values included.

---

## Design Notes

**Monitor cost is not incremental.** The transaction table is
`bus_transaction_t` x `MAX_TRANSACTIONS`, and the reporter keeps a second full
copy (`r_trans_table_local`), so a monitored interface is a multiple of the
unmonitored one rather than a few percent on top. `MAX_TRANSACTIONS` is the
knob and the cost is linear in it.

**`perf_byte_count` scales with the bus width.** `cmd_size` is derived as
`$clog2(AXIL_DATA_WIDTH/8)`. It was hardwired to `3'b010` (4 bytes) until
2026-09-02, which halved every byte count on a 64-bit Lite bus without failing
anything. `val/amba/test_axil_perf_byte_count.py` pins it at both legal widths.

**Do not enable completion and performance packets together under load.** The
monitor bus sustains at most one packet per two cycles. Use `cfg_axi_pkt_mask`
to drop a class while keeping its marking and counting.

**The ID filter is inert and must stay that way.** AXI4-Lite has no IDs, so
this wrapper ties the monitor's ID inputs to zero; enabling `ID_FILTER_ENABLE`
with an `ID_MATCH_BASE` above 0 makes `id_owned(0)` false for every
transaction and drops ALL monitoring rather than narrowing it.

---

## Related Modules

- **[axil4_slave_rd](../axil4/axil4_slave_rd.md)** - Base functional module
- **[axil4_slave_wr_mon](axil4_slave_wr_mon.md)** - Write monitor counterpart
- **[AXI4 Slave Read Mon](../axi4/axi4_slave_rd_mon.md)** - Full AXI4 reference

---

**Last Updated:** 2026-07-19

## Testing

`val/amba/test_axil4_slave_rd_mon.py` drives this module with the AXI4-Lite BFMs from `TBClasses/axil4`. It collects 3 parameter cases at the default `REG_LEVEL`. Run it with:

```bash
source env_python
pytest val/amba/test_axil4_slave_rd_mon.py -v
```

---

---

## Navigation

- **[← Back to AXIL4 Index](../axil4/README.md)**
- **[← Back to rtl-amba Index](../index.md)**
