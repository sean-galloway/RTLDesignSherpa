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

# AXI Monitor Lite Wrappers

**Module:** `axi4_master_rd_monlite.sv` / `axi4_master_wr_monlite.sv` / `axi4_slave_rd_monlite.sv` / `axi4_slave_wr_monlite.sv` / `axi5_master_rd_monlite.sv` / `axi5_master_wr_monlite.sv` / `axi5_slave_rd_monlite.sv` / `axi5_slave_wr_monlite.sv` / `axil4_master_rd_monlite.sv` / `axil4_master_wr_monlite.sv` / `axil4_slave_rd_monlite.sv` / `axil4_slave_wr_monlite.sv` / `axil5_master_rd_monlite.sv` / `axil5_master_wr_monlite.sv` / `axil5_slave_rd_monlite.sv` / `axil5_slave_wr_monlite.sv` / `axi4ace_master_rd_monlite.sv` / `axi4ace_master_wr_monlite.sv` / `axi4ace_slave_rd_monlite.sv` / `axi4ace_slave_wr_monlite.sv` / `axi4ace_snoop_slave_monlite.sv` / `axi4ace_snoop_master_monlite.sv` / `axi4_master_rd_monlite_cg.sv` / `axi4_master_wr_monlite_cg.sv` / `axi4_slave_rd_monlite_cg.sv` / `axi4_slave_wr_monlite_cg.sv` / `axi5_master_rd_monlite_cg.sv` / `axi5_master_wr_monlite_cg.sv` / `axi5_slave_rd_monlite_cg.sv` / `axi5_slave_wr_monlite_cg.sv` / `axil4_master_rd_monlite_cg.sv` / `axil4_master_wr_monlite_cg.sv` / `axil4_slave_rd_monlite_cg.sv` / `axil4_slave_wr_monlite_cg.sv` / `axil5_master_rd_monlite_cg.sv` / `axil5_master_wr_monlite_cg.sv` / `axil5_slave_rd_monlite_cg.sv` / `axil5_slave_wr_monlite_cg.sv`
**Location:** `rtl/amba/axi4/`, `rtl/amba/axi5/`, `rtl/amba/axil4/`, `rtl/amba/axil5/`, `rtl/amba/ace/`
**Category:** Protocol wrappers with the lite monitor
**Status:** Production Ready (rtl/amba/monitors TASK-001, 2026-09-26)

**Plane:** protocol plane (lite monitor wrappers)

---

## Overview

Forty-eight wrappers, one page. Each `<core>_monlite` is the core wrapper
(`axi4_master_rd`, `axil5_slave_wr`, `axi4ace_snoop_slave`, and so on) with
the appropriate lite monitor watching its bus-side channels; each
`<core>_monlite_cg` is that lite wrapper behind one `amba_clock_gate_ctrl`.
They are the lite-monitor siblings of the `_mon` and `_mon_cg` wrappers: same
core, same taps, same 128-bit `monitor_packet_t` on the same monbus with the
same `UNIT_ID`/`AGENT_ID`, so the monbus arbiter, the AXI-Lite group, the tally
and the host tooling cannot tell the two apart. The difference is what they
cost and what they can be asked for: about a fifth of the monitor LUTs (677
against 3,249 per read monitor in the same bridge fixture) and the packet
classes the lite emits -- error, timeout, completion, threshold (active-count
and latency), address-range match and miss, and the drop report.

Every core parameter and port is declared verbatim and passed through by name;
only the monitor section differs from `<core>`. The files are generated from
the core module headers and the lite tap wiring, which is why one page
describes them all: the monitor section below is identical within each family,
and the per-wrapper facts fit in three tables.

| Family | Role | Channel | Lite wrapper | Clock-gated lite wrapper | Wraps | Full-monitor siblings |
|---|---|---|---|---|---|---|
| AXI4 | master | read | `axi4_master_rd_monlite` | `axi4_master_rd_monlite_cg` | `axi4_master_rd` | [`axi4_master_rd_mon`](../axi4/axi4_master_rd_mon.md), [`axi4_master_rd_mon_cg`](../axi4/axi4_master_rd_mon_cg.md) |
| AXI4 | master | write | `axi4_master_wr_monlite` | `axi4_master_wr_monlite_cg` | `axi4_master_wr` | [`axi4_master_wr_mon`](../axi4/axi4_master_wr_mon.md), [`axi4_master_wr_mon_cg`](../axi4/axi4_master_wr_mon_cg.md) |
| AXI4 | slave | read | `axi4_slave_rd_monlite` | `axi4_slave_rd_monlite_cg` | `axi4_slave_rd` | [`axi4_slave_rd_mon`](../axi4/axi4_slave_rd_mon.md), [`axi4_slave_rd_mon_cg`](../axi4/axi4_slave_rd_mon_cg.md) |
| AXI4 | slave | write | `axi4_slave_wr_monlite` | `axi4_slave_wr_monlite_cg` | `axi4_slave_wr` | [`axi4_slave_wr_mon`](../axi4/axi4_slave_wr_mon.md), [`axi4_slave_wr_mon_cg`](../axi4/axi4_slave_wr_mon_cg.md) |
| AXI5 | master | read | `axi5_master_rd_monlite` | `axi5_master_rd_monlite_cg` | `axi5_master_rd` | [`axi5_master_rd_mon`](../axi5/axi5_master_rd_mon.md), [`axi5_master_rd_mon_cg`](../axi5/axi5_master_rd_mon_cg.md) |
| AXI5 | master | write | `axi5_master_wr_monlite` | `axi5_master_wr_monlite_cg` | `axi5_master_wr` | [`axi5_master_wr_mon`](../axi5/axi5_master_wr_mon.md), [`axi5_master_wr_mon_cg`](../axi5/axi5_master_wr_mon_cg.md) |
| AXI5 | slave | read | `axi5_slave_rd_monlite` | `axi5_slave_rd_monlite_cg` | `axi5_slave_rd` | [`axi5_slave_rd_mon`](../axi5/axi5_slave_rd_mon.md), [`axi5_slave_rd_mon_cg`](../axi5/axi5_slave_rd_mon_cg.md) |
| AXI5 | slave | write | `axi5_slave_wr_monlite` | `axi5_slave_wr_monlite_cg` | `axi5_slave_wr` | [`axi5_slave_wr_mon`](../axi5/axi5_slave_wr_mon.md), [`axi5_slave_wr_mon_cg`](../axi5/axi5_slave_wr_mon_cg.md) |
| AXI4-Lite | master | read | `axil4_master_rd_monlite` | `axil4_master_rd_monlite_cg` | `axil4_master_rd` | [`axil4_master_rd_mon`](../axil4/axil4_master_rd_mon.md), [`axil4_master_rd_mon_cg`](../axil4/axil4_master_rd_mon_cg.md) |
| AXI4-Lite | master | write | `axil4_master_wr_monlite` | `axil4_master_wr_monlite_cg` | `axil4_master_wr` | [`axil4_master_wr_mon`](../axil4/axil4_master_wr_mon.md), [`axil4_master_wr_mon_cg`](../axil4/axil4_master_wr_mon_cg.md) |
| AXI4-Lite | slave | read | `axil4_slave_rd_monlite` | `axil4_slave_rd_monlite_cg` | `axil4_slave_rd` | [`axil4_slave_rd_mon`](../axil4/axil4_slave_rd_mon.md), [`axil4_slave_rd_mon_cg`](../axil4/axil4_slave_rd_mon_cg.md) |
| AXI4-Lite | slave | write | `axil4_slave_wr_monlite` | `axil4_slave_wr_monlite_cg` | `axil4_slave_wr` | [`axil4_slave_wr_mon`](../axil4/axil4_slave_wr_mon.md), [`axil4_slave_wr_mon_cg`](../axil4/axil4_slave_wr_mon_cg.md) |
| AXI5-Lite | master | read | `axil5_master_rd_monlite` | `axil5_master_rd_monlite_cg` | `axil5_master_rd` | [`axil5_master_rd_mon`](../axil5/axil5_master_rd_mon.md), [`axil5_master_rd_mon_cg`](../axil5/axil5_master_rd_mon_cg.md) |
| AXI5-Lite | master | write | `axil5_master_wr_monlite` | `axil5_master_wr_monlite_cg` | `axil5_master_wr` | [`axil5_master_wr_mon`](../axil5/axil5_master_wr_mon.md), [`axil5_master_wr_mon_cg`](../axil5/axil5_master_wr_mon_cg.md) |
| AXI5-Lite | slave | read | `axil5_slave_rd_monlite` | `axil5_slave_rd_monlite_cg` | `axil5_slave_rd` | [`axil5_slave_rd_mon`](../axil5/axil5_slave_rd_mon.md), [`axil5_slave_rd_mon_cg`](../axil5/axil5_slave_rd_mon_cg.md) |
| AXI5-Lite | slave | write | `axil5_slave_wr_monlite` | `axil5_slave_wr_monlite_cg` | `axil5_slave_wr` | [`axil5_slave_wr_mon`](../axil5/axil5_slave_wr_mon.md), [`axil5_slave_wr_mon_cg`](../axil5/axil5_slave_wr_mon_cg.md) |

: Table 1: The thirty-two wrappers

### The eight AXIS wrappers (2026-09-27)

The stream families never had a `_mon` sibling to twin: the AXI monitor cores
are transaction trackers and a stream has no transaction. These wrap
[`axis_monitor_lite`](axis_monitor_lite.md), the stream monitor built for
them (rtl/amba/monitors TASK-003). The monitor TAPS the endpoint's FUB-side
port (every monitor taps the FUB side, for timing) and drives nothing.

| Family | Role | Lite wrapper | Clock-gated lite wrapper | Wraps | Tapped port |
|---|---|---|---|---|---|
| AXI4-Stream | master | `axis4_master_monlite` | `axis4_master_monlite_cg` | `axis4_master` | `fub_axis_*` (upstream of the skid) |
| AXI4-Stream | slave | `axis4_slave_monlite` | `axis4_slave_monlite_cg` | `axis4_slave` | `fub_axis_*` (downstream of the skid) |
| AXI5-Stream | master | `axis5_master_monlite` | `axis5_master_monlite_cg` | `axis5_master` | `fub_axis_*` (upstream of the skid) |
| AXI5-Stream | slave | `axis5_slave_monlite` | `axis5_slave_monlite_cg` | `axis5_slave` | `fub_axis_*` (downstream of the skid) |

: Table 2: The eight AXIS wrappers

### The eight ACE wrappers (2026-10-05)

The ACE family adds AXI Coherency Extensions to the AXI4 movers (`AxSNOOP`, `AxDOMAIN[1:0]`, `AxBAR[1:0]`, the 4-bit `RRESP`, auto-pulsed `RACK`/`WACK` on the masters and forwarded `RACK`/`WACK` on the slaves) and adds three snoop channels (AC/CR/CD) for cache-to-CCU traffic. Front-side ACE wrappers reuse [`axi_monitor_lite`](axi_monitor_lite.md) exactly as the AXI4 wrappers do; the read wrappers hand the monitor `RRESP[1:0]` only, so IsShared and PassDirty (`RRESP[3:2]`) never count as an error response. Snoop-side wrappers use the new [`axi4ace_snoop_monitor_lite`](axi4ace_snoop_monitor_lite.md) because snoop channels have no transaction ID: CR and CDLAST are attributed to the oldest outstanding AC.

| Family | Role | Channel | Lite wrapper | Wraps | Monitor core | Tapped port |
|---|---|---|---|---|---|---|
| ACE | master | read | `axi4ace_master_rd_monlite` | `axi4ace_master_rd` | `axi_monitor_lite` | `fub_axi_*` read channels |
| ACE | master | write | `axi4ace_master_wr_monlite` | `axi4ace_master_wr` | `axi_monitor_lite` | `fub_axi_*` write channels |
| ACE | slave | read | `axi4ace_slave_rd_monlite` | `axi4ace_slave_rd` | `axi_monitor_lite` | `fub_axi_*` read channels |
| ACE | slave | write | `axi4ace_slave_wr_monlite` | `axi4ace_slave_wr` | `axi_monitor_lite` | `fub_axi_*` write channels |
| ACE | snoop | slave (cache side) | `axi4ace_snoop_slave_monlite` | `axi4ace_snoop_slave` | `axi4ace_snoop_monitor_lite` | `fub_ac*` / `fub_cr*` / `fub_cd*` |
| ACE | snoop | master (CCU side) | `axi4ace_snoop_master_monlite` | `axi4ace_snoop_master` | `axi4ace_snoop_monitor_lite` | `fub_ac*` / `fub_cr*` / `fub_cd*` |

: Table 3: The eight ACE wrappers

### The two CXS wrappers (2026-10-15)

CXS (Arm IHI 0079) is credited, not valid/ready, so neither the AXI cores nor
`axis_monitor_lite` fit. These wrap [`cxs_monitor_lite`](cxs_monitor_lite.md)
(amba TASK-044). The monitor taps the endpoint's FUB handshake and its
registered status outputs (`link_state`, credits, `credit_starved`, the
sticky error flags), never the link pins. There are no `_cg` variants:
clock gating is an FPGA-only concern here.

| Family | Role | Lite wrapper | Wraps | Tapped |
|---|---|---|---|---|
| CXS | transmitter | `cxs_master_monlite` | `cxs_master` | `fub_cxs_*` (upstream of the skid) + core status |
| CXS | receiver | `cxs_slave_monlite` | `cxs_slave` | `fub_cxs_*` (downstream of the receive FIFO) + core status |

: Table 4: The two CXS wrappers

There are no `_cg` ACE wrappers in this release. The front-side ACE wrappers carry the same monitor port list as the AXI4 wrappers (with the core's ACE fields passed through). The snoop-side wrappers expose the smaller control set of `axi4ace_snoop_monitor_lite`: `clear`, `cfg_monitor_enable`, `cfg_error_enable`, `cfg_timeout_enable`, `cfg_compl_enable`, `cfg_timeout_cycles`, `cfg_freq_sel`, `i_mon_time`, plus the monbus and status outputs.

The AXIS wrappers' monitor section is the AXIS core's, not the AXI one's: parameters
`USE_MONITOR`, `UNIT_ID`, `AGENT_ID`, `OUT_DEPTH`, `ACLK_MHZ`,
`CFI_MIN/MAX_FREQ_MHZ` (no table, so no `MAX_TRANSACTIONS`,
`ACTIVE_TRANS_THRESHOLD` or address ranges); control pins `cam_clear`,
`cfg_monitor_enable`, the six class enables (`error`, `timeout`, `compl`,
`credit`, `channel`, `stream`), `cfg_strb_check_enable`,
`cfg_timeout_cycles` (microseconds, 0 = never), `cfg_freq_sel`,
`cfg_axis_pkt_mask`, `cfg_stall_threshold` (cycles, 0 = off), `i_mon_time`;
status `in_packet`, `packet_count`, `error_count`, `dropped_count`. The `_cg`
twins take the family's own gating logic verbatim (AXIS4: `user_valid` /
`axi_valid` terms; AXIS5: the registered wakeup term including `twakeup`) and
add the monitor's activity -- a queued packet or an open packet holds the clock
-- with the upstream READY and `monbus_valid` masked by `!cg_gating`. The
AXIS5 `_cg` wrappers keep the `fub_axis_` / `m_axis_` / `s_axis_` names of
their `_monlite`, not `axis5_master_cg`'s `axis5_` spelling, so each pair is
pin-compatible with itself.

Which port is tapped matters for what a stall looks like. Every wrapper taps
its FUB side. On a master that is upstream of the skid, so a slow consumer is
invisible at the tap until the skid (default depth 4) is full; a single beat
never stalls it. On a slave the FUB side is downstream of the skid, so a slow
backend stalls the tap directly. The wrapper tests fill the skid before
expecting a stall on a master wrapper.

### What is not here

Compared with the `_mon` wrappers: no performance window or counters, no debug
packets, no ID or address filters, no per-event masks, and no `block_ready`.
The lite never stalls the port: an event it cannot deliver is dropped and
counted (`dropped_count`, reported as an `EVENT_DROPPED` packet), and a
command that finds no free table entry is counted (`refused_count`) and left
untracked, so its beats report as orphans. Consumers that need the perf
window keep a meter beside the lite (STREAM's `axi_bus_meter`, RAPIDS'
descriptor-port meter), not inside it.

The ACE snoop-side wrappers additionally do not carry the full AXI monitor's
transaction table: `axi4ace_snoop_monitor_lite` tracks snoops in AC-issue order
because snoop channels have no ID, and it emits only error, timeout, and
completion packets.

---

## Monitor Parameters (every wrapper)

| Parameter | Type | Default | Description |
|---|---|---|---|
| `USE_MONITOR` | bit | `1'b1` | 0 = omit the monitor, tie its outputs |
| `UNIT_ID` | logic [7:0] | `8'h01` | Unit id in every packet |
| `AGENT_ID` | logic [15:0] | `16'h000A` | Agent id in every packet |
| `MAX_TRANSACTIONS` | int | `8` | table entries; a command finding none is counted, not tracked |
| `ACTIVE_TRANS_THRESHOLD` | int | `MAX_TRANSACTIONS / 2` | Table occupancy that fires a threshold packet (rising edge) |
| `OUT_DEPTH` | int | `4` | monbus output queue (`gaxi_fifo_sync`), any depth the lite allows (>= 2; >= 1 on the AXIS/CXS lites). `16` on `axi4_master_rd_monlite` / `axi4_master_wr_monlite` (2026-10-08, amba BUG-039): 16 rides out the ~8-cycle observer-egress stall measured at ~1.1 events/cycle, the same margin the interface observers already run their AXIS taps at |
| `N_ADDR_RANGES` | int | `0` | address-range checker windows; 0 = not built |
| `ADDR_RANGE_IS_ERROR` | logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] | `'0` | per range: 1 = miss is an error, 0 = hit is a match |
| `ACLK_MHZ` | int | `100` | Clock in MHz; keeps the 1 us tick exact |
| `CFI_MIN_FREQ_MHZ` | int | `ACLK_MHZ` | Frequency-invariant tick LUT lower bound (`cfg_freq_sel` indexes it) |
| `CFI_MAX_FREQ_MHZ` | int | `ACLK_MHZ` | Frequency-invariant tick LUT upper bound |

All of `<core>`'s own parameters follow, unchanged.

---

## Monitor Ports (every wrapper)

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
| `cfg_latency_threshold` | input | `logic [31:0]` | completion latency (cycles) above this -> Threshold/LATENCY |
| `cfg_addr_check_enable` | input | `logic` |  |
| `cfg_addr_match_enable` | input | `logic` | hit in a match range -> AddrMatch packet |
| `cfg_addr_range_enable` | input | `logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]` |  |
| `cfg_addr_range_low` | input | `logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0]` |  |
| `cfg_addr_range_high` | input | `logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0]` |  |
| `i_mon_time` | input | `ocelus_common_pkg::monbus_timestamp_t` |  |
| `monbus_valid` | output | `logic` |  |
| `monbus_ready` | input | `logic` |  |
| `monbus_packet` | output | `ocelus_common_pkg::monitor_packet_t` |  |
| `monbus_timestamp` | output | `ocelus_common_pkg::monbus_timestamp_t` |  |
| `active_transactions` | output | `logic [7:0]` | entries in the table |
| `error_count` | output | `logic [15:0]` | error + timeout packets emitted |
| `transaction_count` | output | `logic [31:0]` | completion packets emitted |
| `dropped_count` | output | `logic [15:0]` | events lost to monbus backpressure since the last report |
| `refused_count` | output | `logic [15:0]` | commands that found no free table entry |

All of `<core>`'s own ports follow, unchanged. On the AXI-Lite families the
fabric side is `fub_axil_*`, matching the `_mon` wrappers, so the two are
pin-compatible on both sides.

---

## Clock-Gated Wrappers

`<core>_monlite_cg` adds one parameter and four pins to the lite wrapper, and
is built exactly as `<core>_mon_cg` is built around `<core>_mon`: the activity
term, the request-side ready masks and the monitor-bus liveness terms are the
`_mon_cg` ones verbatim.

| Parameter | Type | Default | Description |
|---|---|---|---|
| `CG_IDLE_COUNT_WIDTH` | int | `4` | Width of the idle countdown, sizing `cfg_cg_idle_count` |

| Port | Direction | Width | Description |
|---|---|---|---|
| `cfg_cg_enable` | input | 1 | Enable clock gating |
| `cfg_cg_idle_count` | input | `CG_IDLE_COUNT_WIDTH` | Idle cycles before the clock stops |
| `cg_gating` | output | 1 | Gated clock is stopped |
| `cg_idle` | output | 1 | No activity observed |

Activity is derived from VALID signals and outstanding work only, never from a
peer's READY, so a consumer that parks its response-ready high while idle does
not defeat gating. While `cg_gating` is high the request-side readys are held
at 0, so nothing is accepted with the clock stopped:

| Wrapper | Request-side readys held at 0 while `cg_gating` |
|---|---|
| `axi4_master_rd_monlite_cg` | `fub_axi_arready`, `m_axi_rready` |
| `axi4_master_wr_monlite_cg` | `fub_axi_awready`, `fub_axi_wready`, `m_axi_bready` |
| `axi4_slave_rd_monlite_cg` | `s_axi_arready`, `fub_axi_rready` |
| `axi4_slave_wr_monlite_cg` | `s_axi_awready`, `s_axi_wready`, `fub_axi_bready` |
| `axi5_master_rd_monlite_cg` | `fub_axi_arready`, `m_axi_rready` |
| `axi5_master_wr_monlite_cg` | `fub_axi_awready`, `fub_axi_wready`, `m_axi_bready` |
| `axi5_slave_rd_monlite_cg` | `s_axi_arready`, `fub_axi_rready` |
| `axi5_slave_wr_monlite_cg` | `s_axi_awready`, `s_axi_wready`, `fub_axi_bready` |
| `axil4_master_rd_monlite_cg` | `fub_axil_arready`, `m_axil_rready` |
| `axil4_master_wr_monlite_cg` | `fub_axil_awready`, `fub_axil_wready`, `m_axil_bready` |
| `axil4_slave_rd_monlite_cg` | `s_axil_arready`, `fub_axil_rready` |
| `axil4_slave_wr_monlite_cg` | `s_axil_awready`, `s_axil_wready`, `fub_axil_bready` |
| `axil5_master_rd_monlite_cg` | `fub_axil_arready`, `m_axil_rready` |
| `axil5_master_wr_monlite_cg` | `fub_axil_awready`, `fub_axil_wready`, `m_axil_bready` |
| `axil5_slave_rd_monlite_cg` | `s_axil_arready`, `fub_axil_rready` |
| `axil5_slave_wr_monlite_cg` | `s_axil_awready`, `s_axil_wready`, `fub_axil_bready` |

: Table 2: Ready masks per clock-gated wrapper

A packet parked on the monitor bus and any occupied table entry hold the block
awake so the lite can retire the handshake, and the external `monbus_valid` is
masked by `!cg_gating` so the consumer never sees a valid a stopped lite could
not retire. The lite's output queue holds a parked packet across the wait.

---

## Functional Description

The core is instantiated untouched; unlike `_mon` there is no gating of the
command handshake, because the lite has no admission stall. The monitor taps
the bus-side command, data and response channels (`m_*` on a master wrapper,
`s_*` on a slave wrapper) through three valids gated by `cfg_monitor_enable`,
which also holds the table clear while low. `cfg_timeout_cycles` is a
microsecond count of no progress on an entry, passed at full width; 0 means
never. `cfg_latency_threshold` turns a clean completion whose latency exceeds
it into a `Threshold/LATENCY` packet. With `N_ADDR_RANGES > 0` the address
checker is built inside the lite: a range flagged in `ADDR_RANGE_IS_ERROR` is
an allowlist whose miss is an error, an unflagged range is a watchpoint whose
hit is an `AddrMatch` packet (gated by `cfg_addr_match_enable`).

`cam_clear` is legal only while the monitor is idle -- no outstanding
transactions, nothing queued (see the
[architecture page](monitor_system_architecture.md), Configuration cautions).

**IDs.** The command and response IDs are the bus's own (AxID, BID/RID), so
the lite pairs each response with the oldest outstanding command of that ID.
On the AXI5-Lite wrappers they were tied to 0 until amba #104, and every
response was paired with the oldest command outstanding whichever it
answered; a Subordinate may reorder responses across IDs (IHI 0022L B2.1.5).
W carries no ID on AXI4 or AXI5-Lite and the write wrappers tie `data_id` to
0: the lite attributes W in AW order (A5.5) from its own AW-order queue, which
also covers W that arrives ahead of its AW (A2.6).

The lite's own behaviour -- per-ID linked-list attribution, stamps instead of
counters, the registered event stage, the output queue and drop-and-count -- is
on the [axi_monitor_lite](axi_monitor_lite.md) page.

---

## Usage Example

```systemverilog
axi4_master_rd_monlite #(
    .AXI_ID_WIDTH         (8),
    .AXI_ADDR_WIDTH       (32),
    .AXI_DATA_WIDTH       (32),
    .UNIT_ID              (8'h02),
    .AGENT_ID             (16'h0014),
    .MAX_TRANSACTIONS     (8)
) u_rd_monlite (
    .aclk                 (aclk),
    .aresetn              (aresetn),
    // ... the axi4_master_rd ports, by name ...
    .cam_clear            (1'b0),
    .cfg_monitor_enable   (1'b1),
    .cfg_error_enable     (1'b1),
    .cfg_timeout_enable   (1'b1),
    .cfg_compl_enable     (1'b0),
    .cfg_threshold_enable (1'b0),
    .cfg_timeout_cycles   (16'd1000),
    .cfg_freq_sel         (4'd0),
    .cfg_axi_pkt_mask     (16'h0000),
    .cfg_latency_threshold(32'd0),
    .cfg_addr_check_enable(1'b0),
    .cfg_addr_match_enable(1'b0),
    .cfg_addr_range_enable('0),
    .cfg_addr_range_low   ('0),
    .cfg_addr_range_high  ('0),
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

In a generated bridge every monitored port is a `_monlite` wrapper. STREAM's
core and scheduler array and RAPIDS' scheduler group array instantiate them
directly.

---

## Design Notes

- `cam_clear` keeps the `_mon` wrapper's name so the two are pin-compatible on
  the monitor side; the lite has a table, not a CAM.
- `MAX_TRANSACTIONS` defaults to 8 here against 16 on `_mon`: size it to the
  port's real outstanding depth, since refused commands surface as orphans.
- Consumers that relied on `block_ready` to bound the table get drop-and-count
  instead; the count is always reported, the identity of the lost events is not.
- Filelists: `rtl/amba/filelists/<wrapper>.f`, each the core's closure plus
  `axi_monitor_lite.f` (or `axi4ace_snoop_monitor_lite.f` for the two snoop-side
  ACE wrappers), and `amba_clock_gate_ctrl.f` for the `_cg` variants; nothing
  from the full monitor family.

---

## Related Modules

- [axi_monitor_lite](axi_monitor_lite.md) -- the monitor itself
- [axi_monitor_addr_check](axi_monitor_addr_check.md) -- the address checker built in behind `N_ADDR_RANGES`
- [monitor_system_architecture](monitor_system_architecture.md) -- packet classes, monbus, configuration cautions

---

## Testing

`val/amba/monitor-lite/` holds one test per wrapper (`test_<wrapper>.py`, the
same TB and scenarios as the `_mon` / `_mon_cg` tests with the DUT swapped),
the lite's own TB (`test_axi_monitor_lite.py`), the ACE snoop monitor's own
TB (`test_axi4ace_snoop_monitor_lite.py`), and `test_monlite_cg_gating.py`,
the six-phase BFM-driven structural gating test over all sixteen clock-gated
wrappers at two idle counts and two shared delay profiles.

Two `val/amba` suites cover the wrappers as a family. `test_axi_mon_block_ready.py`
saturates each AXI wrapper's table and checks that every admitted command is
completed, refused or still live, and (since amba #105) that the table is
empty once the bus is idle. `test_axil5_mon_reorder.py` puts every AXI5-Lite
`_mon`/`_mon_cg`/`_monlite`/`_monlite_cg` wrapper behind a Subordinate that
returns responses in reverse order across distinct IDs (and, on the write
wrappers, holds AWREADY so W leads AW). Each completion must name its own
(address, ID), in the bus's response order, and the table must drain (amba #104).

```bash
source env_python
make -C val/amba/monitor-lite run-all-full-parallel
```

---

**Last Updated:** 2026-10-12

---

The eight AXIS wrappers reuse the core's exact-packet suite
(`AxisMonitorLiteTB`) end to end through the endpoint: framework AXIS master
BFM on the upstream port, slave BFM downstream, MonbusSlave on the bus, every
phase asserting class, code and payload and that nothing else came out. The
one pin-driven phase (TVALID withdrawn) is skipped through a wrapper, since a
skid buffer's output cannot be made to violate the rule; the `_cg` wrappers add
a gating phase (idle gates, a packet wakes the clock and is reported exactly,
idle re-gates). `val/amba/monitor-lite/test_axis{4,5}_{master,slave}_monlite[_cg].py`:
9 cells each at FULL; with the core's 12, 84/84 from a clean build, 2026-09-27.

## References

The Ocelus is an original design of this repository. The papers and standards below are related work for comparison, not sources of the design; protocol specifications define the rules the monitor observes.

- Arm. *AMBA AXI Protocol Specification*, ARM IHI 0022, Issue L, Aug. 2025. [developer.arm.com/documentation/ihi0022/l](https://developer.arm.com/documentation/ihi0022/l). -- AXI4/AXI5 channels, §A2.3.1 handshake, §A5.1 transaction identifiers.
- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022H.c, Jan. 2021. [developer.arm.com/documentation/ihi0022/h](https://developer.arm.com/documentation/ihi0022/h). -- Part B ch. B1 (AXI4-Lite), Part D §D3.6-§D3.8 (ACE snoop channels) for the Lite and ACE wrappers.
- Tamir, Y., Frazier, G.L. "High-Performance Multi-Queue Buffers for VLSI Communication Switches." *Proc. 15th Annual Int. Symp. Computer Architecture (ISCA 1988)*, pp. 343-354, May 1988. DOI: [10.1109/ISCA.1988.5245](https://doi.org/10.1109/ISCA.1988.5245). -- related to the per-ID linked lists inside the lite core.
- Ciordas, C., Basten, T., Rădulescu, A., Goossens, K., van Meerbergen, J. "An Event-Based Monitoring Service for Networks on Chip." *ACM Trans. Design Automation of Electronic Systems*, 10(4):702-723, Oct. 2005. DOI: [10.1145/1109118.1109126](https://doi.org/10.1145/1109118.1109126). -- related work: one hardware probe per observed port, emitting events.
- Indexed in `rtl/amba/references/README.md` (local PDF: `LinkedListMultiQueueBuffer__Tamir1988.pdf`)

## Navigation

- **[← Back to Monitor Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
