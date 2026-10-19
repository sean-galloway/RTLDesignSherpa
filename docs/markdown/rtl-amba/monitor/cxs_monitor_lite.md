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

# CXS Monitor Lite

**Module:** `cxs_monitor_lite.sv`
**Location:** `rtl/amba/ocelus/`
**Wrappers:** `cxs_master_monlite`, `cxs_slave_monlite` (`rtl/amba/cxs/`)
**Status:** New (2026-10-15)

**Plane:** protocol plane (lite CXS monitor)

---

## Overview

`cxs_monitor_lite` is the Ocelus monitor for a CXS link (Arm IHI 0079, Issues A-D). It works in the lite discipline of [`axis_monitor_lite`](axis_monitor_lite.md):

- Events are decided and registered, and up to two are queued per cycle.
- The output queue is 4 deep: two interleaved `gaxi_fifo_sync` banks (unreset storage, mux read), so two entries can be queued per cycle at any depth.
- Events the bus cannot take are dropped and counted, and the count is reported as Error/EVENT_DROPPED.
- Timeouts are in microseconds, independent of the clock frequency.

A separate core is needed because CXS is not a valid/ready stream. Flits move on credits, packets are delimited inside flits by CXSCNTL, and a four-phase ACTIVEREQ/ACTIVEACK handshake brings the link up and down. Every packet is tagged `PROTOCOL_CXS` (4'h6), with event codes from [`ocelus_cxs_pkg`](../includes/monitor_cxs_pkg.md).

The block is a **tap**: every port is an input and it drives nothing. Following the house rule for monitors, it never sits on the external link pins. It watches two things:

- the endpoint's **FUB handshake** (`fub_cxs_valid/ready` with the flit's CXSCNTL and stream fields), for packets, streams and backpressure;
- the endpoint's **registered status outputs** (`link_state`, `credits` / `credits_outstanding`, `credit_starved`, `protocol_error`, `parity_error`), for everything that exists only on the link.

---

## Events

Priority when several fire in one cycle runs from the top of the table down. Each timeout and Credit event reports once per episode.

| Class | Code | When | event_data |
|---|---|---|---|
| Error | `CXS_ERR_PROTOCOL` (0) | `protocol_error` rose | {credits[16], 14'b0, link_state[2], flits[32]} |
| Error | `CXS_ERR_PARITY` (1) | `parity_error` rose | as PROTOCOL |
| Error | `CXS_ERR_ENDERROR` (2) | a flit ended packets with ENDERROR | {enderrs[8], ends[8], 16'b0, packets[32]} |
| Timeout | `CXS_TIMEOUT_CREDIT` (0) | `credit_starved` for `cfg_timeout_cnt` us | {starve_cycles[32], age_us[16], cfg[16]} |
| Timeout | `CXS_TIMEOUT_LINK` (1) | ACTIVATE or DEACTIVATE for `cfg_timeout_cnt` us | {credits[16], 14'b0, link_state[2], age_us[16], cfg[16]} |
| Timeout | `CXS_TIMEOUT_PACKET` (2) | a packet open with no flit for `cfg_timeout_cnt` us | {flits_in_packet[32], age_us[16], cfg[16]} |
| Completion | `CXS_COMPL_PACKET_END` (0) | a flit that ends one or more packets (CXS-Lite: every flit) | {prcltype[8], srcid[8], tgtid[8], ends[8], packets[32]} |
| Credit | `CXS_CREDIT_STARVED` (0) | `credit_starved` for `cfg_stall_threshold` cycles | {cycles[32], threshold[32]} |
| Credit | `CXS_CREDIT_BACKPRESSURE` (1) | FUB valid without ready for `cfg_stall_threshold` cycles | {cycles[32], threshold[32]} |
| Channel | `CXS_CHAN_STREAM_CHANGE` (0) | CXSPRCLTYPE/SRCID/TGTID differ from the previous flit (2.5.2) | {prev_stream[24], 8'b0, stream[24], 8'b0} |
| Stream | `CXS_STREAM_LINK_ACTIVATE` / `LINK_UP` / `LINK_DEACTIVATE` / `LINK_DOWN` (0-3) | the link entered ACTIVATE / RUN / DEACTIVATE / STOP | {credits[16], 14'b0, prev_link_state[2], flits[32]} |
| Error | `CXS_ERR_EVENT_DROPPED` (0xE) | the drop count, sent into an empty queue | count[16] |

`packets` is the running total of packets ended, including this flit. `channel_id` carries {prcltype[2:0], tgtid[5:0]} on the flit events. A stream is the triple {CXSPRCLTYPE, CXSSRCID, CXSTGTID}, each field zero-extended to 8 bits.

`credit_starved` comes from the endpoint and means something different on each side:

- **Transmitter:** a flit is waiting in RUN with no credit to send it.
- **Receiver:** the link is in RUN, no credit is outstanding, and none can be granted because the FIFO is full of flits the FUB has not taken. In that case the consumer is the bottleneck.

---

## Parameters

| Parameter | Default | Description |
|---|---|---|
| UNIT_ID / AGENT_ID | 8'h0A / 16'h00C0 | Packet identity |
| CXS_DATA_WIDTH, CXS_MAX_PKT_PER_FLIT, CXS_START_ALIGN | 256, 2, 16 | The tapped interface; sizes the CXSCNTL decode (`cxs_pkg`) |
| CXS_SRCID_WIDTH, CXS_TGTID_WIDTH, CXS_MAX_CREDIT | 0, 0, 15 | Port widths of the stream fields and the credit count |
| OUT_DEPTH | 4 | Output queue entries, any depth >= 1 (two interleaved `gaxi_fifo_sync` banks) |
| CFI_* | 5..220 MHz, 16 entries | Microsecond tick (`counter_freq_invariant`) |

## Ports

| Port | Dir | Description |
|---|---|---|
| aclk, aresetn, clear | in | `clear` is synchronous: it forgets open packets and episodes and zeroes the counters. Legal only while idle |
| i_mon_time | in | Side-band time, copied to `monbus_timestamp` |
| fub_valid, fub_ready, fub_cntl, fub_prcltype, fub_srcid, fub_tgtid | in | The FUB handshake |
| link_state, credits, credit_starved, protocol_error, parity_error | in | The endpoint's registered status |
| cfg_freq_sel, cfg_timeout_cnt | in | Microsecond tick select; timeout in us (16'hFFFF = never) |
| cfg_{error,timeout,compl,credit,channel,stream}_enable | in | Class enables |
| cfg_stall_threshold | in | Credit-event threshold in cycles; 0 = Credit events off |
| cfg_cxs_pkt_mask | in | bit[packet_type] = 1 drops that class |
| monbus_valid/ready/packet/timestamp | out/in | Ocelus bus |
| busy, packet_count, flit_count, error_count, dropped_count | out | Status |

---

## Wrappers

`cxs_master_monlite` and `cxs_slave_monlite` declare every parameter and port of their endpoint verbatim (generated from it) and pass them through unchanged. They add the Ocelus parameters (`USE_MONITOR`, `UNIT_ID`, `AGENT_ID`, `OUT_DEPTH`, `ACLK_MHZ`, `CFI_*`) and the lite control set: `cam_clear`, `cfg_monitor_enable` (0 holds the monitor clear), the class enables, `cfg_timeout_cycles` (microseconds, **0 = never**), `cfg_freq_sel`, `cfg_cxs_pkt_mask`, `cfg_stall_threshold` and `i_mon_time`. They have no `_cg` variants, because clock gating is an FPGA-only concern here. See [the wrappers page](axi_monitor_lite_wrappers.md) (Table 4).

## Design Notes

- **Drops in normal traffic are legal, and counted.** One flit can raise PACKET_END, ENDERROR and STREAM_CHANGE in the same cycle. Back-to-back flits that end packets produce events as fast as the monbus can drain them, so a full-rate link with every class enabled will drop events. The lite contract counts every drop and reports it, so delivered + reported always equals issued. Mask Completion (`cfg_cxs_pkt_mask`) when only errors and link events are wanted.
- **Errors are edges of sticky flags.** The endpoint's `protocol_error` and `parity_error` are sticky, so each is reported once, when it rises. Reset or a rebuild re-arms them.
- **No formal proof yet.** `axis_monitor_lite` has an sv2v-flattened SymbiYosys harness; this block has simulation coverage only, including the seven mutations below.

## Testing

`val/amba/monitor-lite/test_cxs_{master,slave}_monlite.py` drive the endpoint traffic and its flit scoreboard (`CXSMasterTB` / `CXSSlaveTB`) with a `MonbusSlave` on the Ocelus bus (`bin/TBClasses/cxs/cxs_monlite_tb.py`). They run the same configuration grid as the endpoint tests, Issues A-D and CXS-Lite.

- **Exact:** PACKET_END, ENDERROR and STREAM_CHANGE are predicted flit by flit from the packetizer's output. Delivered packets must be an in-order subsequence of the prediction with exact payloads, and delivered + reported dropped must equal issued.
- **Link events:** the sequence must be ACTIVATE, UP, DEACTIVATE, DOWN repeated, with as many ACTIVATEs as the wire-level CXSMonitor counted.
- **Bounded:** Credit events must fire exactly at the threshold. Each of the three timeouts must fire, with age at least the configured microseconds. The LINK timeout must fire exactly once, naming ACTIVATE.
- **Also covered:** the type mask, a held monbus (drop accounting), `clear`, and PROTOCOL / PARITY errors, provoked last and reported exactly once each.

Seven mutations of the core were caught: a wrong PACKET_END payload field, LINK_UP and DEACTIVATE codes swapped, the drop count never reported, the LINK timeout re-firing, the STARVED threshold off by one, STREAM_CHANGE suppressed, and PROTOCOL reported on the level instead of the edge.

## References

- Arm. *AMBA CXS Protocol Specification*, ARM IHI 0079D, Sep. 2025 (and Issues A-C). [developer.arm.com/documentation/ihi0079/d](https://developer.arm.com/documentation/ihi0079/d/): 2.1.2 credits, 2.5.2 flit streams, 4.3 CXSCNTL, chapter 5 link activation. Citation only.

---

## Navigation

- **[Back to Monitor Index](../_book_monitor_index.md)**
- **[CXS Modules](../cxs/README.md)**
