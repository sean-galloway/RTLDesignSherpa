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

# CHI (Coherent Hub Interface) Link-Layer Modules

**Location:** `rtl/amba/chi/` (package in `rtl/amba/includes/chi_pkg.sv`)
**Specification:** Arm *AMBA 5 CHI Architecture Specification*, ARM IHI 0050, Issue H
**Status:** New (2026-10-29); the GATE/FUNC/FULL runners are being written

---

## Overview

CHI is the coherent interconnect protocol behind Arm's CMN meshes. This directory implements its **link layer** (chapters B13 and B14): the part that moves flits between two components. Every flit travels on one of four channels, **REQ**, **RSP**, **SNP** or **DAT**, as one wide word per cycle with three sideband wires: `FLITPEND`, `FLITV` and `LCRDV`.

Like CXS, and unlike AXI, **there is no READY.** A receiver hands out L-Credits on `LCRDV`, one per cycle, each a promise of one flit of buffer (B14.2.1.1). The transmitter spends one credit per flit it sends on `FLITV`, and a credit received in cycle t is usable from t+1. `FLITPEND` must be high the cycle before `FLITV` (B14.4) and may be raised speculatively. When a link direction goes down, every credit the transmitter still holds goes back as an **LCrdReturn**: a Link flit with Opcode 0 and TxnID 0 (B13.11), which is the all-zero word and is never delivered to the Protocol layer.

A CHI **port is a pair of links** (B13.2), one per direction, and each direction carries several channels. Credits are per channel, but link activation is per direction: one `LINKACTIVEREQ` / `LINKACTIVEACK` pair gates every TX channel, another every RX channel (B14.5), and `TXSACTIVE` / `RXSACTIVE` say whether the Protocol layer above has anything in flight (B14.7). Which channels a node transmits and receives is fixed by its type (Table B13.1):

| Port | Node | Transmits | Receives | Link prefix |
|---|---|---|---|---|
| `chi_rnf_port` | RN-F (a core, cluster or coherent DMA) | REQ, RSP, DAT | RSP, DAT, SNP | `m_chi_` (faces the home) |
| `chi_hnf_port` | HN-F (a home agent) facing one RN-F | RSP, DAT, SNP | REQ, RSP, DAT | `s_chi_` (faces the requester) |

### Scope

- **Link layer only, Issue H.** Credits, FLITPEND, the two LINKACTIVE pairs, LCrdReturn, SACTIVE. The link layer reads two flit fields, the Opcode (zero means a Link flit) and the TxnID (zero in an LCrdReturn); everything else is payload.
- **The Protocol layer lives on the FUB side** (B2 to B12: transactions, coherence, snoop filters, DBIDs, CompAck). The port does not know when a transaction completes, which is why `fub_sactive` is an input.
- **Not here:** Resource Planes and replicated channels (B13.2), parity and the `Check` property (`DATA_CHECK` and `POISON` only size the DAT flit, nothing is generated or checked), clock-gated `_cg` and `_monlite` variants, and any node type other than RN-F and HN-F.

## Module Categories

| Module | Role | Page |
|---|---|---|
| `chi_pkg` (`rtl/amba/includes/`) | Flit widths, the Opcode / TxnID offsets, link-state encodings, `config_error()` | this page |
| `chi_tx_channel` | One credited transmit channel: FUB valid/ready in, FLITPEND / FLITV / FLIT out against LCRDV | this page |
| `chi_rx_channel` | One credited receive channel: the receive FIFO is the credit pool; LCrdReturns are absorbed | this page |
| `chi_link_tx` | TXLINKACTIVEREQ controller for one direction; the run / deactivate state every TX channel follows | this page |
| `chi_link_rx` | RXLINKACTIVEACK controller for one direction; synchronizes REQ, grants only in RUN | this page |
| `chi_rnf_port` | RN-F port: 3 TX + 3 RX channels, both controllers, SACTIVE | [chi_rnf_port.md](chi_rnf_port.md) |
| `chi_hnf_port` | HN-F port: the mirror image | [chi_hnf_port.md](chi_hnf_port.md) |

Each module has its own filelist in `rtl/amba/filelists/chi_*.f`; the port filelists list the shared primitives (`gaxi_skid_buffer`, `gaxi_fifo_sync`, `counter_bin`, `fifo_control`, `glitch_free_n_dff_arn`) once so nothing is declared twice.

## Properties and Parameters

Both ports take the same property set, named as the RDS-DV `CHIConfig` names it, so a DUT built from these parameters and a BFM built from that config agree on every bit.

| Spec property | Parameter | Legal values | Default |
|---|---|---|---|
| NodeID_Width (B16.1.12) | `NODEID_WIDTH` | 7..16 | 7 |
| Req_Addr_Width (B16.1.11) | `ADDR_WIDTH` | 44..52 | 44 |
| Data_Width (B16.1.13) | `DATA_WIDTH` | 128 / 256 / 512 | 128 |
| Req_RSVDC_Width / Dat_RSVDC_Width | `REQ_RSVDC_WIDTH` / `DAT_RSVDC_WIDTH` | 0, 4, 8, 12, 16, 24, 32 | 0 |
| MPAM_Support | `MPAM_WIDTH` | 0 / 12 / 15 | 0 |
| PBHA_Support | `PBHA_WIDTH` | 0 / 4 | 0 |
| MECID_Width | `MECID_WIDTH` | 0 / 16 | 0 |
| StreamID (RME-CDA) | `STREAMID_WIDTH` | 0 / 16 (shares the REQ slot with MECID) | 0 |
| SecSID1 (RME-CDA) | `SECSID1_WIDTH` | 0 / 1 | 0 |
| Data_Check / Data_Poison | `DATA_CHECK` / `POISON` | 0 / 1 (DAT flit grows by DW/8 or DW/64) | 0 |
| L-Credits per channel (B14.2.1.1) | `MAX_LCREDIT` | 1..15, the same bound on every channel | 15 |
| LINKACTIVE pair present | `LINK_CTRL` | 1 = handshake, 0 = always RUN, pins tied | 1 |
| (implementation) | `SKID_DEPTH` | TX skid buffer slots, 2..8 | 4 |
| (implementation) | `RX_FIFO_DEPTH` | receive FIFO per RX channel = its credit pool, >= 1 | `MAX_LCREDIT` |
| (implementation) | `LINKACTIVE_SYNC_STAGES` | synchronizer flops on RXLINKACTIVEREQ: 0 (known synchronous) or >= 2 | 2 |

### Configuration checks

`chi_pkg::config_error()` returns 0 for a legal property set, else the number of the first rule broken. Each port calls it from an elaboration-time `param_check` and stops with `$fatal` naming the rule. The numbers are those of the framework's `CHIConfig.CONFIG_RULES`, so a rule number means the same thing on both sides. Rule 1 (the issue is H) is not a parameter here, this RTL is Issue H; rule 13 (node type) is the module you instantiate.

| Rule | Requirement |
|---|---|
| 2 | `NODEID_WIDTH` is 7 to 16 |
| 3 | `ADDR_WIDTH` is 44 to 52 |
| 4 | `DATA_WIDTH` is 128, 256 or 512 |
| 5 | `REQ_RSVDC_WIDTH` is 0, 4, 8, 12, 16, 24 or 32 |
| 6 | `DAT_RSVDC_WIDTH` is 0, 4, 8, 12, 16, 24 or 32 |
| 7 | `MPAM_WIDTH` is 0, 12 or 15 |
| 8 | `PBHA_WIDTH` is 0 or 4 |
| 9 | `MECID_WIDTH` is 0 or 16 |
| 10 | `STREAMID_WIDTH` is 0 or 16 |
| 11 | `SECSID1_WIDTH` is 0 or 1 |
| 12 | `MAX_LCREDIT` is 1 to 15 |

The same `param_check` also rejects `RX_FIFO_DEPTH < 1`, `LINKACTIVE_SYNC_STAGES == 1` and `SKID_DEPTH` outside 2..8.

## Flit Widths and the Fields the Link Layer Reads

`chi_pkg` computes the four flit widths from Tables B13.6 to B13.9, with N = `NODEID_WIDTH` - 7, RAW = `ADDR_WIDTH`, DW = `DATA_WIDTH`, Y = the RSVDC width, M / PB / E / R / S the MPAM, PBHA, MECID, StreamID and SecSID1 widths, DC = DW/8 with `DATA_CHECK`, P = DW/64 with `POISON`:

| Channel | Function | Width | At the defaults |
|---|---|---|---|
| REQ | `req_flit_w()` | 93 + RAW + Y + M + PB + S + max(E, R) + 3N | 137 |
| RSP | `rsp_flit_w()` | 71 + 2N | 71 |
| SNP | `snp_flit_w()` | 53 + (RAW - 3) + M + E + 2N | 94 |
| DAT | `dat_flit_w()` | 240 / 389 / 687 (DW 128 / 256 / 512) + Y + DC + P + E + 3N | 240 |

The ports expose these as the derived parameters `REQ_W`, `RSP_W`, `SNP_W` and `DAT_W`.

Fields are packed in table order from bit 0 upward. The link layer reads two of them, at these LSB positions (n = `NODEID_WIDTH`):

| Channel | Layout from bit 0 | TxnID LSB | Opcode LSB | Opcode width |
|---|---|---|---|---|
| REQ | QoS 4, TgtID n, SrcID n, TxnID 12, ReturnNID n, StashNIDValid 1, ReturnTxnID 12, Opcode 7 | 4 + 2n | 29 + 3n | 7 |
| RSP | QoS 4, TgtID n, SrcID n, TxnID 12, Opcode 5 | 4 + 2n | 16 + 2n | 5 |
| SNP | QoS 4, SrcID n, TxnID 12, FwdNID n, FwdTxnID 12, Opcode 5 | 4 + n | 28 + 2n | 5 |
| DAT | QoS 4, TgtID n, SrcID n, TxnID 12, HomeNID n, Opcode 4 | 4 + 2n | 16 + 3n | 4 |

`chi_pkg` also names the node types (`CHI_NODE_RN_F` .. `CHI_NODE_SN_F`), the link states as `{LINKACTIVEREQ, LINKACTIVEACK}` pairs (`CHI_LINK_STOP` 00, `CHI_LINK_ACTIVATE` 10, `CHI_LINK_RUN` 11, `CHI_LINK_DEACTIVATE` 01, Table B14.1), `CHI_MAX_LCREDIT` = 15 and `CHI_TXNID_W` = 12.

## The FUB Flit Convention

Each FUB channel is one valid/ready port carrying **one packed flit word**: `fub_tx<ch>_valid` / `fub_tx<ch>_ready` / `fub_tx<ch>_flit[W-1:0]` into a TX channel, `fub_rx<ch>_valid` / `_ready` / `_flit` out of an RX channel. The word is the wire flit exactly, bit 0 first in table order, so `fub_txreq_flit` is `REQFLIT[REQ_W-1:0]`. The port never unpacks it. Build the word with the RDS-DV flit classes (`CHIReqFlit`, `CHIRspFlit`, `CHISnpFlit`, `CHIDatFlit`; `pack()` is the wire word, `from_word()` the inverse) from a `CHIConfig` carrying the same widths as the DUT. A word built from different widths puts the Opcode somewhere else, and the receive channel then mistakes a protocol flit for an LCrdReturn or the reverse.

## Link Control

The link state of a direction is simply its `{REQ, ACK}` pair; there is no separate state machine (Table B14.1). Only the transmitter starts a state change, and the four-phase rule holds: REQ rises only with ACK low and falls only with ACK high.

| {REQ, ACK} | State | Flits | Credits |
|---|---|---|---|
| 00 | STOP | none | all held by the receiver |
| 10 | ACTIVATE | none | may already be granted (Table B14.2 race); the transmitter counts them |
| 11 | RUN | yes | granted, spent |
| 01 | DEACTIVATE | LCrdReturns only | the transmitter returns every credit; ACK falls only when all are home |

The two directions of a port are cross-coupled (B14.6): when the receive direction leaves STOP the transmit direction raises its REQ by itself, and when the receive direction enters DEACTIVATE the transmit direction drops its REQ. B14.6.3.4 orders the port's two outputs: TXREQ rises only after RXACK has fallen and falls only after RXACK has risen; RXACK rises only after TXREQ has risen and falls only after TXREQ has fallen.

With `LINK_CTRL = 0` the direction is always RUN, `TXLINKACTIVEREQ` and `RXLINKACTIVEACK` are tied low, and the `*_link_state` status reads 11 (RUN): the pins say nothing, the status says what the channels see.

## Building Blocks

### chi_tx_channel

One transmit channel. A `gaxi_skid_buffer` sits between the FUB port and the link and drains one flit per cycle whenever a credit is held and the direction is in RUN.

| Parameter | Default | Description |
|---|---|---|
| FLIT_W | 137 | The channel's flit width |
| MAX_LCREDIT | 15 | Credits the receiver may grant, 1..15 |
| SKID_DEPTH | 4 | Skid buffer slots, 2..8 |
| CRW | clog2(MAX_LCREDIT + 1) | Credit counter width (derived) |

| Port | Dir | Description |
|---|---|---|
| aclk, aresetn | In | Clock, active-low asynchronous reset |
| i_run, i_deact | In | Direction state from `chi_link_tx` (RUN; DEACTIVATE) |
| fub_valid / fub_ready / fub_flit[FLIT_W] | In / Out / In | Flit in (ready = skid not full) |
| o_flitpend | Out | `FLITPEND`: a flit could go next cycle |
| o_flitv, o_flit[FLIT_W] | Out | `FLITV`, `FLIT`; the flit is all-zero for an LCrdReturn |
| i_lcrdv | In | `LCRDV`: one credit |
| o_credits[CRW] | Out | Credits held |
| o_all_returned | Out | No credit held |
| o_busy | Out | `fub_valid` or a flit in the skid |
| o_credit_starved | Out | A flit waits in RUN with no credit |
| o_protocol_error | Out | Sticky: a grant beyond `MAX_LCREDIT` (the credit is dropped) |

`r_credits` updates by `+LCRDV - FLITV` each cycle and FLITV is decoded from `r_credits`, never from `i_lcrdv`, so a grant in cycle t is spendable in t+1 and no output depends combinationally on an input. `o_flitpend` is the next-cycle condition itself, `(i_run && skid not empty) || (i_deact && a credit held)`, computed from flops; `r_pend` registers it and a flit in a cycle requires `r_pend`, so FLITPEND is always high the cycle before FLITV (B14.4). In DEACTIVATE every held credit, including a late grant, goes back as an LCrdReturn, one per cycle.

### chi_rx_channel

One receive channel. The receive FIFO **is** the credit pool: a credit is granted only when a slot can back it, so the receiver never refuses a flit (B14.2.1.1).

| Parameter | Default | Description |
|---|---|---|
| FLIT_W | 137 | The channel's flit width |
| OPCODE_LSB / OPCODE_W | 50 / 7 | Where the Opcode sits (`chi_pkg::*_opcode_lsb`, `*_OPCODE_W`); the defaults are REQ at NodeID 7 |
| TXNID_LSB / TXNID_W | 18 / 12 | Where the TxnID sits |
| MAX_LCREDIT | 15 | Credits outstanding at most, 1..15 |
| RX_FIFO_DEPTH | MAX_LCREDIT | The credit pool; the FIFO is built at least 2 deep (`gaxi_fifo_sync` cannot be 1 deep) while the grant counts against `RX_FIFO_DEPTH`, so a one-credit receiver is legal |
| CRW | clog2(MAX_LCREDIT + 1) | Counter width (derived) |

| Port | Dir | Description |
|---|---|---|
| aclk, aresetn | In | Clock, reset |
| i_grant_ok | In | Credits may be granted (RUN, from `chi_link_rx`) |
| i_flitpend, i_flitv, i_flit[FLIT_W] | In | The channel; flits are accepted in every link state |
| o_lcrdv | Out | `LCRDV`, registered |
| fub_valid / fub_ready / fub_flit[FLIT_W] | Out / In / Out | Flit out (FIFO not empty / consumer ready) |
| o_outstanding[CRW] | Out | Credits granted and not yet spent or returned |
| o_all_returned | Out | `o_outstanding` is 0 and no grant is on the wire |
| o_busy | Out | A flit is buffered |
| o_protocol_error | Out | Sticky: `FLITV` without `FLITPEND` the cycle before, a flit with no credit outstanding, an LCrdReturn with a non-zero TxnID |

Each cycle the block works out the state after the clock edge, before any new grant:

```
out_next = r_out + LCRDV(now) - FLITV(protocol) - FLITV(LCrdReturn)
occ_next = fifo_count + push - pop
grant    = i_grant_ok && !underflow && out_next < MAX_LCREDIT && occ_next + out_next < RX_FIFO_DEPTH
```

`r_lcrdv <= grant`, so a credit consumed at cycle t is reissued at t+1 at the earliest. A flit arriving with `r_out == 0` is an underflow even if a grant is on the wire that cycle ("an L-Credit cannot be used in the same cycle as being received"); it is flagged and not counted. An LCrdReturn (Opcode 0) returns a credit and is not pushed.

### chi_link_tx

The TXLINKACTIVEREQ controller for one direction. The state is the `{REQ, ACK}` pair; ACK is sampled into a flop and treated as synchronous.

| Parameter | Default | Description |
|---|---|---|
| LINK_CTRL | 1 | 0 = always RUN, REQ tied low, state reads 11 |

| Port | Dir | Description |
|---|---|---|
| cfg_link_enable | In | 0 = do not keep the link up: drop when idle, never hold. Queued flits and a remote activation still raise it |
| cfg_link_hold | In | 1 = keep the link in RUN with nothing to send (needs `cfg_link_enable`) |
| cfg_idle_cycles[7:0] | In | Idle RUN cycles before deactivating; 0 = never on idleness alone |
| cfg_rx_enable | In | The receive side's enable: no raise without it, since this port could never acknowledge the activation its REQ would provoke |
| i_want | In | Any TX channel has a flit queued |
| i_rx_req, i_rx_ack | In | The receive direction's synchronized REQ and this port's ACK |
| o_req / i_ack | Out / In | `TXLINKACTIVEREQ` / `TXLINKACTIVEACK` |
| o_run, o_deact | Out | RUN (REQ and sampled ACK); DEACTIVATE (REQ low, sampled ACK high) |
| o_state[1:0] | Out | `{REQ, ACK sampled}` |

| From | To | When |
|---|---|---|
| STOP | ACTIVATE | `cfg_rx_enable`, `i_rx_ack` low, and one of: a flit queued, `cfg_link_hold && cfg_link_enable`, the receive direction has left STOP |
| RUN | DEACTIVATE | `i_rx_ack` high and either the receive direction is in DEACTIVATE, or nothing is queued, no hold, and `cfg_link_enable` is low or `cfg_idle_cycles` idle RUN cycles have passed (the idle counter resets on any queued flit and saturates at 255) |

### chi_link_rx

The RXLINKACTIVEACK controller for one direction. `RXLINKACTIVEREQ` comes from the other component and crosses through `glitch_free_n_dff_arn` (`LINKACTIVE_SYNC_STAGES` flops; 0 for a known-synchronous system).

| Parameter | Default | Description |
|---|---|---|
| LINK_CTRL | 1 | 0 = ACK tied low, credits granted whenever `cfg_rx_enable` |
| LINKACTIVE_SYNC_STAGES | 2 | Synchronizer flops on REQ, 0 or >= 2 |

| Port | Dir | Description |
|---|---|---|
| cfg_rx_enable | In | 0 = never acknowledge an activation. It gates the activation only: once in RUN, credits flow until the link deactivates (B14.2.1.1) |
| i_all_returned | In | Every RX channel has its credits home |
| i_tx_req | In | The `TXLINKACTIVEREQ` this port drives (B14.6.3.4 ordering) |
| i_req / o_ack | In / Out | `RXLINKACTIVEREQ` / `RXLINKACTIVEACK` |
| o_req_s | Out | REQ in this clock domain, for `chi_link_tx` |
| o_grant_ok | Out | Channels may grant: synchronized REQ and ACK both high (RUN) |
| o_state[1:0] | Out | `{REQ synchronized, ACK}` |

ACK rises when the synchronized REQ is high, `cfg_rx_enable` is set and `TXLINKACTIVEREQ` is already high (ACTIVATE to RUN); granting stops the moment REQ falls, flits still in flight are accepted, and ACK falls only when every channel reports its credits home and `TXLINKACTIVEREQ` is low (DEACTIVATE to STOP). `TXLINKACTIVEACK` is sampled once, in `chi_link_tx`: the pair is synchronous unless a clock-domain bridge sits between the components, and that bridge owns the synchronization.

## Verification

The BFMs are the `chi` family of the RDS-DV framework (`CocoTBFramework.components.chi`): `CHIHomeNode` (`create_chi_home`) plays the home and drives the RN-F port's link side with prefix `m_chi_`; `CHIRequestNode` (`create_chi_requester`) plays the requester and drives the HN-F port's link side with prefix `s_chi_`; a `CHIMonitor` (`create_chi_monitor`) on the same pins is a third party that judges the DUT, not the BFM driving it. The FUB side of every channel is a valid/ready flit port driven and drained by the framework GAXI BFMs. The TB classes live in `bin/TBClasses/chi/` (`chi_tb_common.py` rebuilds the `CHIConfig` from the RTL parameters the runner exports, so the BFMs bind exactly the flit widths the DUT was built with).

| Test | DUT | Purpose |
|---|---|---|
| `val/amba/test_chi_rnf_port.py` | `chi_rnf_port` | The TB plays a minimal RN-F Protocol layer at flit level: reads, writes with DBID rendezvous, snoop answers, `fub_sactive` |
| `val/amba/test_chi_hnf_port.py` | `chi_hnf_port` | The TB plays a minimal home: serves requests, issues snoops; the requester BFM drives the link |

Both share `val/amba/chi_test_common.py`. `REG_LEVEL` picks the configuration grid: GATE is one default-width point; FUNC adds the other data widths, a one-credit receiver, an interface without link control and the widest legal flit with every optional bus; FULL adds the synchronizer, skid and FIFO corners. `TEST_LEVEL` sets the operations per phase. The phases each make one counted claim: streaming, credit starvation (stall with flits queued, never send without a credit), gappy credits with slow ACK, back-to-back offering, idle pool fill (every pool equals the partner's), hold, idle deactivation with every credit returned, a snoop waking a stopped link, remote activation bringing the other direction up, and link churn under traffic.

```bash
source env_python
cd val/amba
make clean-all && make 'run-chi_*-func-parallel'
```

## References

- Arm. *AMBA 5 CHI Architecture Specification*, ARM IHI 0050 Issue H. [developer.arm.com/documentation/ihi0050](https://developer.arm.com/documentation/ihi0050/latest/). B13.2 link pairs, Table B13.1 channels per node, Tables B13.6 to B13.9 flit fields, B13.11 Link flits, B14.2.1.1 L-Credits, B14.4 FLITPEND, B14.5 link activation (Tables B14.1, B14.2), B14.6 the two directions and B14.6.3.4 output ordering, B14.7 SACTIVE. Citation only; the PDF is not redistributed here.

---

## Navigation

- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
