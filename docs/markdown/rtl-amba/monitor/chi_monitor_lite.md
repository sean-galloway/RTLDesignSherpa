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

# CHI Monitor Lite

**Module:** `chi_monitor_lite.sv`
**Location:** `rtl/amba/ocelus/`
**Wrappers:** `chi_rnf_port_monlite`, `chi_hnf_port_monlite` (`rtl/amba/chi/`)
**Status:** New (2026-10-30)

**Plane:** protocol plane (lite CHI monitor)

---

## Overview

`chi_monitor_lite` is the Ocelus monitor for one CHI port (Arm IHI 0050 Issue H). It works in the lite discipline of [`axis_monitor_lite`](axis_monitor_lite.md) and [`cxs_monitor_lite`](cxs_monitor_lite.md):

- Events are decided and registered, and up to two are queued per cycle.
- The output queue is 4 deep: two interleaved `gaxi_fifo_sync` banks (unreset storage, mux read), so two entries can be queued per cycle at any depth.
- Events the bus cannot take are dropped and counted, and the count is reported as Error/EVENT_DROPPED.
- Timeouts are in microseconds, independent of the clock frequency.

A separate core is needed because a CHI port is neither a stream nor a command/response bus. It is a pair of credited links carrying transactions: a request is answered by a completion and read data, a write is pulled by a DBID and sends write data, a CompAck closes it, and the home can snoop the requester at any time. The CXS lite knows credits and packets; the AXI lite knows commands and responses; this block knows the CHI transaction shapes (B2.3, B2.7.3) and nothing more. Every packet is tagged `PROTOCOL_CHI` (4'h7), with event codes from `ocelus_chi_pkg` (`rtl/amba/includes/ocelus_chi_pkg.sv`).

The block is a **tap**: every port is an input and it drives nothing. Following the house rule for monitors, it never sits on the link pins. It watches two things:

- the port's six **FUB handshakes**, presented by message direction rather than by pin so one block serves both ports: `req` (requester to completer), `cpl_rsp` / `cpl_dat` (toward the requester), `rq_rsp` / `rq_dat` (from the requester: CompAck, write data, snoop responses) and `snp` (toward the requester). The wrapper maps `fub_tx*` and `fub_rx*` onto these; `IS_REQUESTER` says which three are the port's receive channels, for backpressure;
- the port's **registered status outputs** (`tx_link_state`, `rx_link_state`, `credit_starved`, `protocol_error`), for everything that exists only on the link.

### Why it is small

The recipe is `axi_monitor_lite`'s: stamps, not counters, and no per-slot state machine.

- One allocation port, the request handshake, into a table of `MAX_TRANSACTIONS` slots. A slot holds the request's TxnID and opcode, the DBID the completer later hands out, four debts (a completion, a CompAck, read data packets, write data packets) and two stamps (cycles for latency, microseconds for timeout).
- A response or read data toward the requester finds its slot by TxnID; a CompAck or write data from the requester finds it by DBID (B2.4.3: those messages carry the DBID as their TxnID). Each is one equality compare per slot.
- Remaining data packets are a 3-bit decrement, sized from the request's Size and `DATA_WIDTH` (`chi_pkg::data_packets`).
- A slot retires when nothing is owed. ONE retire is picked per cycle (lowest free slot); a second done slot waits a cycle, so nothing is lost. A RetryAck retires its slot the same cycle, ahead of the pick.
- Timeouts are a scan pointer visiting one slot per cycle; a slot reports once.
- Snoops have their own `MAX_SNOOPS` table keyed by the snoop's TxnID, retired by SnpResp or the last SnpRespData packet.

There is no CAM, no scan for a match, and no FSM on any path.

---

## Events

Priority when several fire in one cycle runs from the top of the table down. Each timeout and Credit event reports once per episode (per slot, for the transaction and snoop timeouts). `occ` is the number of request slots in use; `txns` the running total of requests retired, including this one.

| Class | Code | When | channel_id | event_data |
|---|---|---|---|---|
| Error | `CHI_ERR_PROTOCOL` (0) | the port's sticky `protocol_error` rose | 0 | {occ[16], 6'b0, tx_link[2], 6'b0, rx_link[2], txns[32]} |
| Error | `CHI_ERR_RESP_ERR` (1) | a completion or read data for a tracked request carried RespErr DERR or NDERR | TxnID | {opcode[8], 6'b0, resperr[2], 4'b0, txnid[12], txns[32]} |
| Error | `CHI_ERR_ORPHAN_RSP` (2) | Comp / CompDBIDResp / DBIDResp / DBIDRespOrd / RespSepData / CompPersist / CompStashDone / RetryAck with a TxnID matching no open slot | TxnID | {opcode[8], 12'b0, txnid[12], occ[16], 16'b0} |
| Error | `CHI_ERR_ORPHAN_DAT` (3) | CompData / DataSepResp with a TxnID matching no slot | TxnID | as ORPHAN_RSP |
| Error | `CHI_ERR_ORPHAN_ACK` (4) | CompAck or write data whose TxnID matches no slot's DBID | TxnID | as ORPHAN_RSP |
| Error | `CHI_ERR_ORPHAN_SNP_RSP` (5) | SnpResp / SnpRespData* matching no snoop slot | TxnID | as ORPHAN_RSP |
| Error | `CHI_ERR_TABLE_FULL` (6) | a request arrived with no free slot (it is not tracked) | TxnID | {opcode[8], 12'b0, txnid[12], occ[16], 16'b0} |
| Error | `CHI_ERR_SNP_TABLE_FULL` (7) | a snoop arrived with no free snoop slot | TxnID | {20'b0, txnid[12], occ[16], 16'b0} |
| Timeout | `CHI_TIMEOUT_TXN` (0) | a slot older than `cfg_timeout_cnt` us | TxnID | {opcode[8], 4'b0, txnid[12], 8'b0, age_us[16], cfg[16]} |
| Timeout | `CHI_TIMEOUT_SNP` (1) | a snoop slot older than `cfg_timeout_cnt` us | TxnID | {12'b0, txnid[12], 8'b0, age_us[16], cfg[16]} |
| Timeout | `CHI_TIMEOUT_CREDIT` (2) | `credit_starved` for `cfg_timeout_cnt` us | 0 | {starve_cycles[32], age_us[16], cfg[16]} |
| Timeout | `CHI_TIMEOUT_LINK` (3) | a direction sat in ACTIVATE or DEACTIVATE for `cfg_timeout_cnt` us | 0 | {occ[16], 5'b0, is_tx[1], tx_link[2], 6'b0, rx_link[2], age_us[16], cfg[16]} |
| Completion | `CHI_COMPL_TXN` (0) | a request retired with nothing owed | TxnID | {latency_cycles[16], opcode[8], 4'b0, txnid[12], occ[8], txns[16]} |
| Completion | `CHI_COMPL_RETRY` (1) | a RetryAck retired its request | TxnID | {16'b0, 4'b0, pcrdtype[4], 4'b0, txnid[12], occ[8], txns[16]} |
| Completion | `CHI_COMPL_SNP` (2) | a snoop answered | TxnID | {latency_cycles[16], 12'b0, txnid[12], 8'b0, snoops[16]} |
| Credit | `CHI_CREDIT_STARVED` (0) | `credit_starved` for `cfg_stall_threshold` cycles | 0 | {cycles[32], threshold[32]} |
| Credit | `CHI_CREDIT_BACKPRESSURE` (1) | a receive FUB channel valid without ready for `cfg_stall_threshold` cycles | 0 | {cycles[32], threshold[32]} |
| Channel | `CHI_CHAN_PCRD_GRANT` (0) | a PCrdGrant toward the requester | 0 | {28'b0, pcrdtype[4], txns[32]} |
| Channel | `CHI_CHAN_PCRD_RETURN` (1) | a PCrdReturn request (not allocated) | TxnID | {20'b0, txnid[12], txns[32]} |
| Channel | `CHI_CHAN_READ_RECEIPT` (2) | a ReadReceipt (never an orphan: it may land after the data retired the slot) | TxnID | {20'b0, txnid[12], txns[32]} |
| Stream | `CHI_STREAM_TX_ACTIVATE` / `TX_UP` / `TX_DEACTIVATE` / `TX_DOWN` (0-3) | the TX link entered ACTIVATE / RUN / DEACTIVATE / STOP | 0 | {occ[16], 6'b0, prev_tx[2], 6'b0, prev_rx[2], 6'b0, tx_link[2], 6'b0, rx_link[2], txns[16]} |
| Stream | `CHI_STREAM_RX_ACTIVATE` / `RX_UP` / `RX_DEACTIVATE` / `RX_DOWN` (4-7) | the RX link entered ACTIVATE / RUN / DEACTIVATE / STOP | 0 | as TX |
| Error | `CHI_ERR_EVENT_DROPPED` (0xE) | the drop count, sent into an empty queue | 0 | count[16] |

What a slot owes (B2.3, B2.7.3), set from the opcode at allocation (`chi_pkg::owes_dbid`, `owes_wdata`, `is_read_opcode`, `is_copyback`):

- a completion: Comp, CompDBIDResp, RespSepData, CompPersist, CompStashDone, or the last CompData packet. A RetryAck retires the slot instead;
- for a write, atomic or DVMOp opcode, a DBID response (CompDBIDResp, DBIDResp, DBIDRespOrd), then `data_packets(Size)` packets of write data, which WriteDataCancel forgives. The Zero writes owe no data. A CopyBack write answered by a plain Comp (B2.3.2.3 alt 1a) owes no data but then owes a CompAck whatever ExpCompAck said;
- for a read opcode, `data_packets(Size)` packets of CompData or DataSepResp. A Comp on MakeReadUnique forgives them;
- a CompAck when the request set ExpCompAck (NonCopyBackWriteDataCompAck counts as one).

The DBID the CompAck and write data carry as their TxnID (B2.4.3) is captured from every completion, DBID response and CompData, latest wins. PrefetchTgt gets no response and is not tracked. A TxnID is matched only while a TxnID-addressed response is still owed: B2.5 lets the requester reuse it once those are in, even with write data or a CompAck outstanding, and the reused TxnID then lands on the new slot while the old one waits on its DBID. Persist, StashDone, TagMatch and CompCMO carry no tracked debt and are ignored, never orphaned.

Two events of one class in the same cycle (RespErr on RSP and DAT, orphans on both requester channels, two snoops retiring together) share one candidate: one packet is delivered and the other is counted as lost in `dropped_count`, so delivered plus reported dropped still equals issued.

`credit_starved` is the port's: a flit waiting in RUN with no credit on some TX channel. Backpressure is the FUB side not taking what the port's receive FIFOs hold; on an RN-F port that is RSP, DAT and SNP, on an HN-F port REQ, RSP and DAT.

---

## Parameters

| Parameter | Default | Description |
|---|---|---|
| UNIT_ID / AGENT_ID | 8'h0B / 16'h00D0 | Packet identity (the HN-F wrapper uses 8'h0C / 16'h00D1) |
| IS_REQUESTER | 1 | 1 on an RN-F port (its TX is the request channel), 0 on an HN-F port. Selects the backpressure channels only |
| NODEID_WIDTH, ADDR_WIDTH, DATA_WIDTH, MECID_WIDTH | 7, 44, 128, 0 | The tapped interface; set the field offsets (`chi_pkg`) and the packets per line |
| REQ_W, RSP_W, SNP_W, DAT_W | 137, 71, 94, 240 | The port's flit widths; the wrapper passes its own |
| MAX_TRANSACTIONS, MAX_SNOOPS | 8, 4 | Request and snoop slots. A request beyond the table raises TABLE_FULL and is not tracked |
| TS_WIDTH, AGE_WIDTH | 16, 16 | Cycle stamp (latency) and microsecond stamp (timeout; `cfg_timeout_cnt` is 16 bits, so at most 16) |
| OUT_DEPTH | 4 | Output queue entries, any depth >= 1 (two interleaved `gaxi_fifo_sync` banks) |
| CFI_* | 5..220 MHz, 16 entries | Microsecond tick (`counter_freq_invariant`) |

## Ports

| Port | Dir | Description |
|---|---|---|
| aclk, aresetn, clear | in | `clear` is synchronous: it forgets every slot and episode and zeroes the counters. Legal only while idle |
| i_mon_time | in | Side-band time, copied to `monbus_timestamp` |
| req_{valid,ready,flit} | in | Requests, requester to completer |
| cpl_rsp_*, cpl_dat_* | in | Responses and read data toward the requester |
| rq_rsp_*, rq_dat_* | in | CompAck / snoop responses and write / snoop data from the requester |
| snp_* | in | Snoops toward the requester |
| tx_link_state, rx_link_state, credit_starved, protocol_error | in | The port's registered status |
| cfg_freq_sel, cfg_timeout_cnt | in | Microsecond tick select; timeout in us (16'hFFFF = never) |
| cfg_{error,timeout,compl,credit,channel,stream}_enable | in | Class enables |
| cfg_stall_threshold | in | Credit-event threshold in cycles; 0 = Credit events off |
| cfg_chi_pkt_mask | in | bit[packet_type] = 1 drops that class |
| monbus_valid/ready/packet/timestamp | out/in | Ocelus bus |
| busy, active_count, txn_count, snoop_count, error_count, dropped_count | out | Status |

---

## Wrappers

`chi_rnf_port_monlite` and `chi_hnf_port_monlite` declare every parameter and port of their port verbatim (generated from it) and pass them through unchanged. They add the Ocelus parameters (`USE_MONITOR`, `UNIT_ID`, `AGENT_ID`, `MAX_TRANSACTIONS`, `MAX_SNOOPS`, `OUT_DEPTH`, `ACLK_MHZ`, `CFI_*`) and the lite control set: `cam_clear`, `cfg_monitor_enable` (0 holds the monitor clear and gates the tap), the class enables, `cfg_timeout_cycles` (microseconds, **0 = never**), `cfg_freq_sel`, `cfg_chi_pkt_mask`, `cfg_stall_threshold` and `i_mon_time`. The RN-F wrapper taps `fub_txreq` as `req`, `fub_rxrsp` / `fub_rxdat` as `cpl_*`, `fub_txrsp` / `fub_txdat` as `rq_*` and `fub_rxsnp` as `snp`; the HN-F wrapper the mirror. There are no `_cg` variants. See [the wrappers page](axi_monitor_lite_wrappers.md) (Table 5).

## Design Notes

- **Tracking never depends on the enables.** Slots allocate, update and retire whether or not any class is enabled or masked, so toggling `cfg_compl_enable` cannot leak a slot. Only the packets are gated.
- **A full table is lossy and honest.** A request with no free slot raises TABLE_FULL and is not tracked; its completion will then arrive as ORPHAN_RSP or ORPHAN_DAT. Size `MAX_TRANSACTIONS` to the requester's outstanding limit.
- **DBID reuse is the completer's contract.** Two slots cannot hold the same live DBID, because the completer does not reuse one until the write data and CompAck it names have arrived.
- **Errors are edges of a sticky flag.** `protocol_error` is reported once, when it rises; reset or `clear` re-arms it.
- **Drops in normal traffic are legal, and counted.** One cycle can retire a request, answer a snoop and receive a PCrdGrant; a full-rate port with every class enabled will drop events. Delivered plus reported always equals issued. Mask Completion (`cfg_chi_pkt_mask`) when only errors and link events are wanted.
- **Cost (yosys generic `synth`, flattened, default parameters; `bin/yosys_to_nand_equiv.py`).** Measured 2026-10-30 on the same flow for all three:

| Block | Flops | Cells | NAND2 equivalent |
|---|---|---|---|
| `chi_monitor_lite` (8 slots, 4 snoops, DATA_WIDTH 128) | 1,912 | 13,925 | 49,135 |
| `cxs_monitor_lite` (defaults) | 850 | 5,685 | 20,133 |
| `chi_rnf_port` (bare, MAX_LCREDIT 15: the flit storage) | 7,974 | 23,346 | 118,479 |

  Half the monitor's flops are the two slot tables (eight request slots at about 78 bits each, four snoop slots at 49) and the registered event stage; the two 22-way payload picks are the largest combinational block. The monitor adds about 40 percent to a default RN-F port. `MAX_TRANSACTIONS` and `MAX_SNOOPS` scale the tables linearly; the picks do not grow with them.
- **Not modelled.** MultiReq requests (Size is NumReq there), stash DataPull (CompData keyed by the snoop response's DBID, then a CompAck) and snoops from more than one home to the same port (snoop slots are keyed by TxnID alone; SnpDVMOp's two flits share a slot by that key). Each shows up as orphan errors or a stuck snoop slot rather than silently.
- **TABLE_FULL is lossy.** An untracked request's responses all arrive as orphans. Size `MAX_TRANSACTIONS` to the requester's outstanding limit; `AGE_WIDTH` is at most 16 (the packet carries a 16-bit age).
- **No formal proof yet.** Simulation coverage only; see Testing.

## Testing

`val/amba/monitor-lite/test_chi_{rnf,hnf}_port_monlite.py` drive the port with the RDS-DV CHI BFMs (`CHIHomeNode` on the RN-F port, `CHIRequestNode` on the HN-F port, a `CHIMonitor` beside each) and a `MonbusSlave` on the Ocelus bus. The TB (`bin/TBClasses/chi/chi_monlite_tb.py` over the port TBs, with `chi_monlite_common.py` and a spec-level reference model in `chi_monlite_model.py` built from the framework's flit and opcode classes, not from `chi_pkg`) predicts every event from the FUB handshakes it samples and matches delivered packets against that prediction with exact payloads; packets are decoded with `TBClasses.monbus` (`CHIErrorCode` and friends, parity-tested against `ocelus_chi_pkg.sv` by `bin/TBClasses/monbus/tests/test_monbus_chi.py`). Same configuration grid as the port tests plus table sizes 2, 3, 4 and 8, snoop tables 2 and 3, queue depths 2 and 7, and a `USE_MONITOR=0` cell: GATE 3 cells, FUNC 8, FULL 13 per wrapper.

- **Exact:** Completion/TXN per retired request (opcode, TxnID, latency windowed against the sampled handshakes, the running count in order and equal to `txn_count`) over plain, ExpCompAck, RespSepData/DataSepResp, DBIDResp+Comp, RetryAck/PCrdGrant/re-send and ordered-read flows; Completion/SNP for SnpResp and multi-packet SnpRespData; the Stream sequence for both link directions through bring-up, hold, idle deactivation, remote activation and snoop wake-up; every orphan class, TABLE_FULL with `active_count` sampled at the limit, SNP_TABLE_FULL, RESP_ERR (DERR/NDERR) and PROTOCOL (a BFM credit pool bumped so it sends an ungranted flit).
- **Bounded:** Credit events exactly at the threshold with `{cycles, threshold}`; all four timeouts at 1 us with age at least the configured value.
- **Also covered:** the type mask per class, `cfg_monitor_enable=0`, `cam_clear`, a held monbus (EVENT_DROPPED with the count, delivered plus reported equals issued), `USE_MONITOR=0` (monbus low, counters zero, traffic unaffected). The verdict carries counts and fails on any required count of zero.

Three mutations of the core were caught (the CompAck clear of `need_ack` removed, the read-data decrement removed, the latency stamp replaced by the raw cycle counter). Not stimulated by the current BFMs: a plain Comp on a CopyBack write, the Zero writes, SnpDVMOp's shared slot and two snoops retiring in one cycle.

## References

- Arm. *AMBA CHI Architecture Specification*, ARM IHI 0050H, 2025. [developer.arm.com/documentation/ihi0050/h](https://developer.arm.com/documentation/ihi0050/h/): B2.3 transaction flows, B2.4.3 DBID, B2.7.3 completion, B13 link layer, B14 link activation. Citation only.

---

## Navigation

- **[Back to Monitor Index](../_book_monitor_index.md)**
- **[CHI Modules](../chi/README.md)**
