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

# AXI4-Lite Master Write with Lite Monitor

**Module:** `axil4_master_wr_monlite.sv`
**Location:** `rtl/amba/axil4/`
**Status:** Production Ready (amba/monitor-lite TASK-001, 2026-09-26)

---

## Overview

`axil4_master_wr_monlite` is `axil4_master_wr` with `axi_monitor_lite` watching its master-side
write channels. It is the lite-monitor sibling of [`axil4_master_wr_mon`](axil4_master_wr_mon.md): same core,
same taps, same 128-bit `monitor_packet_t` on the same monbus with the same
`UNIT_ID`/`AGENT_ID`, so the monbus arbiter, the AXI-Lite group, the tally and
the host tooling cannot tell the two apart. The difference is what it costs
and what it can be asked for: about a fifth of the monitor LUTs (677 against
3,249 per read monitor in the same bridge fixture, see
[axi_monitor_lite](../monitor/axi_monitor_lite.md)), and only the four packet
classes the lite emits: error, timeout, completion and active-count threshold.

### What is not here

Compared with `axil4_master_wr_mon`: no performance window or counters, no debug packets,
no address-range checker, no ID or address filters, no per-event masks, no
latency threshold, and no `block_ready`. The lite never stalls the port: an
event it cannot deliver is dropped and counted (`dropped_count`, reported as an
`EVENT_DROPPED` packet), and a command that finds no free table entry is
counted (`refused_count`) and left untracked, so its beats report as orphans.

### Key Features

- Every `axil4_master_wr` parameter and port, declared verbatim and passed through by name
- `axi_monitor_lite` on the m_-side taps; `USE_MONITOR=0` omits it and ties its outputs
- Nine config inputs: the enables, the microsecond timeout, the tick LUT index and the packet-type mask
- Five status outputs, two of them (`dropped_count`, `refused_count`) unique to the lite

---

## Parameters

### Monitor Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `USE_MONITOR` | bit | `1'b1` | 0 = omit the monitor, tie its outputs |
| `UNIT_ID` | logic [7:0] | `8'h01` | Unit id in every packet |
| `AGENT_ID` | logic [15:0] | `16'h000B` | Agent id in every packet |
| `MAX_TRANSACTIONS` | int | `8` | table entries; a command finding none is counted, not tracked |
| `ACTIVE_TRANS_THRESHOLD` | int | `MAX_TRANSACTIONS / 2` | Table occupancy that fires a threshold packet (rising edge) |
| `OUT_DEPTH` | int | `4` | monbus output queue, a power of two |
| `ACLK_MHZ` | int | `100` | Clock in MHz; keeps the 1 us tick exact |
| `CFI_MIN_FREQ_MHZ` | int | `ACLK_MHZ` | Frequency-invariant tick LUT lower bound (`cfg_freq_sel` indexes it) |
| `CFI_MAX_FREQ_MHZ` | int | `ACLK_MHZ` | Frequency-invariant tick LUT upper bound |

### Core Parameters (passed through to `axil4_master_wr`)

| Parameter | Type | Default | Description |
|---|---|---|---|
| `N_ADDR_RANGES` | int | `0` | address-range checker windows; 0 = not built |
| `ADDR_RANGE_IS_ERROR` | logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] | `'0` | per range: 1 = miss is an error, 0 = hit is a match |
| `AXIL_ADDR_WIDTH` | int | `32` | as on `axil4_master_wr` |
| `AXIL_DATA_WIDTH` | int | `32` | as on `axil4_master_wr` |
| `SKID_DEPTH_AW` | int | `2` | as on `axil4_master_wr` |
| `SKID_DEPTH_W` | int | `2` | as on `axil4_master_wr` |
| `SKID_DEPTH_B` | int | `2` | as on `axil4_master_wr` |
| `AW` | int | `AXIL_ADDR_WIDTH` | as on `axil4_master_wr` |
| `DW` | int | `AXIL_DATA_WIDTH` | as on `axil4_master_wr` |
| `AWSize` | int | `AW+3` | addr + prot |
| `WSize` | int | `DW+(DW/8)` | data + strb |
| `BSize` | int | `2` | resp only |

---

## Ports

### Monitor Control, Bus and Status

| Port | Direction | Type | Description |
|---|---|---|---|
| `cam_clear` | input | `logic` | sync clear of the monitor's table (named as on the _mon wrapper: pin-compatible) |
| `cfg_monitor_enable` | input | `logic` | 0 = monitor inert, table held clear |
| `cfg_error_enable` | input | `logic` |  |
| `cfg_timeout_enable` | input | `logic` |  |
| `cfg_compl_enable` | input | `logic` |  |
| `cfg_threshold_enable` | input | `logic` |  |
| `cfg_timeout_cycles` | input | `logic [15:0]` | MICROSECONDS of no progress; 0 = never |
| `cfg_freq_sel` | input | `logic [3:0]` | counter_freq_invariant LUT index |
| `cfg_axi_pkt_mask` | input | `logic [15:0]` | drop mask by packet type |
| `i_mon_time` | input | `monitor_common_pkg::monbus_timestamp_t` |  |
| `monbus_valid` | output | `logic` |  |
| `monbus_ready` | input | `logic` |  |
| `monbus_packet` | output | `monitor_common_pkg::monitor_packet_t` |  |
| `monbus_timestamp` | output | `monitor_common_pkg::monbus_timestamp_t` |  |
| `active_transactions` | output | `logic [7:0]` | entries in the table |
| `error_count` | output | `logic [15:0]` | error + timeout packets emitted |
| `transaction_count` | output | `logic [31:0]` | completion packets emitted |
| `dropped_count` | output | `logic [15:0]` | events lost to monbus backpressure since the last report |
| `refused_count` | output | `logic [15:0]` | commands that found no free table entry |

### Core Ports (as on `axil4_master_wr`)

| Port | Direction | Type | Description |
|---|---|---|---|
| `aclk` | input | `logic` |  |
| `aresetn` | input | `logic` |  |
| `fub_axil_awaddr` | input | `logic [AW-1:0]` |  |
| `fub_axil_awprot` | input | `logic [2:0]` |  |
| `fub_axil_awvalid` | input | `logic` |  |
| `fub_axil_awready` | output | `logic` |  |
| `fub_axil_wdata` | input | `logic [DW-1:0]` |  |
| `fub_axil_wstrb` | input | `logic [DW/8-1:0]` |  |
| `fub_axil_wvalid` | input | `logic` |  |
| `fub_axil_wready` | output | `logic` |  |
| `fub_axil_bresp` | output | `logic [1:0]` |  |
| `fub_axil_bvalid` | output | `logic` |  |
| `fub_axil_bready` | input | `logic` |  |
| `m_axil_awaddr` | output | `logic [AW-1:0]` |  |
| `m_axil_awprot` | output | `logic [2:0]` |  |
| `m_axil_awvalid` | output | `logic` |  |
| `m_axil_awready` | input | `logic` |  |
| `m_axil_wdata` | output | `logic [DW-1:0]` |  |
| `m_axil_wstrb` | output | `logic [DW/8-1:0]` |  |
| `m_axil_wvalid` | output | `logic` |  |
| `m_axil_wready` | input | `logic` |  |
| `m_axil_bresp` | input | `logic [1:0]` |  |
| `m_axil_bvalid` | input | `logic` |  |
| `m_axil_bready` | output | `logic` |  |
| `busy` | output | `logic` |  |
| `cfg_latency_threshold` | input | `logic [31:0]` | completion latency (cycles) above this -> Threshold/LATENCY |
| `cfg_addr_check_enable` | input | `logic` |  |
| `cfg_addr_match_enable` | input | `logic` | hit in a match range -> AddrMatch packet |
| `cfg_addr_range_enable` | input | `logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]` |  |
| `cfg_addr_range_low` | input | `logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0]` |  |
| `cfg_addr_range_high` | input | `logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0]` |  |

---

## Functional Description

The core is instantiated untouched; unlike `axil4_master_wr_mon` there is no gating of the
command handshake, because the lite has no admission stall. The monitor taps
the m_-side command, data and response channels through three valids gated
by `cfg_monitor_enable`, which also holds the table clear while low.
`cfg_timeout_cycles` is a microsecond count of no progress on an entry, passed
at full width; 0 means never. The active-count threshold is the parameter
`ACTIVE_TRANS_THRESHOLD`, as on the `_mon` wrapper.

The lite's own behaviour -- per-ID linked-list attribution, stamps instead of
counters, the registered event stage, the 4-entry output queue and
drop-and-count -- is on the [axi_monitor_lite](../monitor/axi_monitor_lite.md) page.

---

## Timing Characteristics

The datapath timing is `axil4_master_wr`'s. The monitor adds no gating to any handshake
and no path into the datapath; its own paths are two short cycles (attribution,
then packet formatting) and met 10 ns on an Artix-7 100T -1 with margin inside
`bridge_1x2_rd_lite_mon`.

---

## Usage Examples

```systemverilog
axil4_master_wr_monlite #(
    .N_ADDR_RANGES         (0),
    .ADDR_RANGE_IS_ERROR   ('0),
    .AXIL_ADDR_WIDTH       (32),
    .AXIL_DATA_WIDTH       (32),
    .UNIT_ID              (8'h02),
    .AGENT_ID             (16'h0014),
    .MAX_TRANSACTIONS     (8)
) u_axil4_master_wr_monlite (
    .aclk                 (aclk),
    .aresetn              (aresetn),
    // ... the axil4_master_wr ports, by name ...
    .cam_clear            (1'b0),
    .cfg_monitor_enable   (1'b1),
    .cfg_error_enable     (1'b1),
    .cfg_timeout_enable   (1'b1),
    .cfg_compl_enable     (1'b0),
    .cfg_threshold_enable (1'b0),
    .cfg_timeout_cycles   (16'd1000),
    .cfg_freq_sel         (4'd0),
    .cfg_axi_pkt_mask     (16'h0000),
    .i_mon_time           (mon_time),
    .monbus_valid         (monbus_valid),
    .monbus_ready         (monbus_ready),
    .monbus_packet        (monbus_packet),
    .monbus_timestamp     (monbus_timestamp),
    .active_transactions  (),
    .error_count          (),
    .transaction_count    (),
    .dropped_count        (dropped_count),
    .refused_count        (refused_count)
);
```

In a generated bridge, `mon_preset = "lite"` selects this wrapper for every
monitored port.

---

## Design Notes

- `cam_clear` keeps the `_mon` wrapper's name so the two are pin-compatible on
  the monitor side; the lite has a table, not a CAM.
- `MAX_TRANSACTIONS` defaults to 8 here against 16 on `axil4_master_wr_mon`: size it to the
  port's real outstanding depth, since refused commands surface as orphans.
- Consumers that relied on `block_ready` to bound the table get drop-and-count
  instead; the count is always reported, the identity of the lost events is not.

---

## Related Modules

- [`axil4_master_wr_mon`](axil4_master_wr_mon.md) -- the full-monitor sibling
- [`axil4_master_wr`](axil4_master_wr.md) -- the core this wraps
- [axi_monitor_lite](../monitor/axi_monitor_lite.md) -- the monitor itself

---

## Testing

`val/amba/monitor-lite/test_axil4_master_wr_monlite.py` exercises this module: the same TB and
scenarios as `val/amba/test_axil4_master_wr_mon.py`, with the DUT swapped.

```bash
source env_python
make -C val/amba/monitor-lite run-axil4_master_wr_monlite-gate
```

---

**Last Updated:** 2026-09-26

---

## Navigation

- **[← Back to Monitor Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
