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

# CHI RN-F Port

**Module:** `chi_rnf_port.sv`
**Location:** `rtl/amba/chi/`
**Status:** New (2026-10-29)

---

## Overview

`chi_rnf_port` is the link layer of a CHI Request Node (RN-F): the requester side of one link pair, the CHI counterpart of `cxs_master` and `cxs_slave` in one block. It transmits on REQ, RSP and DAT and receives on RSP, DAT and SNP (Table B13.1). The Protocol layer above it, a core, a cluster or a DMA with a coherent cache, issues requests on `fub_txreq`, answers snoops and sends CompAck and write data on `fub_txrsp` and `fub_txdat`, and receives completions and snoops on `fub_rxrsp`, `fub_rxdat` and `fub_rxsnp`, each a valid/ready port carrying one packed flit word. The link side faces the interconnect (an HN-F) with prefix `m_chi_`. The property set, flit widths and FUB flit convention are on the family page, [CHI Modules](README.md).

### Key Features

- Three `chi_tx_channel` and three `chi_rx_channel` instances, each with its own L-Credit pool of up to `MAX_LCREDIT`; a grant is usable the cycle after it arrives (B14.2.1.1)
- `FLITPEND` exactly one cycle before every `FLITV` (B14.4); LCrdReturns absorbed on receive and generated on deactivation (B13.11)
- One LINKACTIVE pair per direction (`chi_link_tx`, `chi_link_rx`), cross-coupled so a remote activation brings the transmit direction up by itself (B14.6) and the four outputs keep the B14.6.3.4 order
- Deactivation on idleness (`cfg_idle_cycles`), on `cfg_link_enable` low, or because the receive direction deactivated; ACK dropped only once every credit is home
- `TXSACTIVE` from `fub_sactive` and queued flits; `RXSACTIVE` passed through
- Flits opaque beyond the Opcode and TxnID; the illegal property set stops elaboration with its `config_error` rule number
- Sticky `protocol_error` over every channel; `credit_starved` and per-channel credit counts for a monitor

---

## Parameters

The `CHI` property parameters are described in [CHI Modules: Properties and Parameters](README.md#properties-and-parameters).

| Parameter | Type | Default | Description |
|---|---|---|---|
| NODEID_WIDTH | int | 7 | NodeID_Width, 7..16 |
| ADDR_WIDTH | int | 44 | Req_Addr_Width, 44..52 |
| DATA_WIDTH | int | 128 | Data_Width, 128 / 256 / 512 |
| REQ_RSVDC_WIDTH / DAT_RSVDC_WIDTH | int | 0 | 0, 4, 8, 12, 16, 24, 32 |
| MPAM_WIDTH / PBHA_WIDTH / MECID_WIDTH / STREAMID_WIDTH / SECSID1_WIDTH | int | 0 | 0/12/15, 0/4, 0/16, 0/16, 0/1 |
| DATA_CHECK / POISON | bit | 0 | Size the DAT flit by DW/8 / DW/64; nothing is computed or checked |
| MAX_LCREDIT | int | 15 | Credits per channel, 1..15, the same bound on every channel |
| LINK_CTRL | bit | 1 | 1 = LINKACTIVE handshake; 0 = always RUN, `m_chi_txlinkactivereq` and `m_chi_rxlinkactiveack` tied low |
| SKID_DEPTH | int | 4 | TX skid buffer slots, 2..8 |
| RX_FIFO_DEPTH | int | MAX_LCREDIT | Receive FIFO per RX channel, i.e. its credit pool, >= 1; floored at 2 inside the channel |
| LINKACTIVE_SYNC_STAGES | int | 2 | Synchronizer flops on `m_chi_rxlinkactivereq`; 0 for a known-synchronous system, never 1 |

### Derived Values (do not override)

| Name | Derivation | Meaning |
|---|---|---|
| REQ_W / RSP_W / SNP_W / DAT_W | `chi_pkg::req_flit_w()` etc. | Flit widths (137 / 71 / 94 / 240 at the defaults) |
| CRW | clog2(MAX_LCREDIT + 1) | Credit counter width |

---

## Ports

### Clock, Reset and Configuration

| Port | Width | Direction | Description |
|---|---|---|---|
| aclk / aresetn | 1 | Input | Clock, active-low asynchronous reset |
| cfg_link_enable | 1 | Input | 0 = do not keep the TX link up: it drops when idle and is never held; queued flits and a remote activation still raise it |
| cfg_link_hold | 1 | Input | 1 = keep the TX link in RUN with nothing to send (with `cfg_link_enable`) |
| cfg_idle_cycles | 8 | Input | Idle RUN cycles before deactivating; 0 = never on idleness alone |
| cfg_rx_enable | 1 | Input | 0 = keep the whole port in STOP: no activation acknowledged or started |
| fub_sactive | 1 | Input | Protocol layer: transactions in progress (B14.7.2) |
| fub_rxsactive | 1 | Output | `RXSACTIVE` passed through (B14.7.3) |

### FUB Side: Transmit Channels (valid/ready flits in)

| Port | Width | Direction | Description |
|---|---|---|---|
| fub_txreq_valid / fub_txreq_ready / fub_txreq_flit | 1 / 1 / REQ_W | In / Out / In | REQ flit word (ready = skid not full) |
| fub_txrsp_valid / fub_txrsp_ready / fub_txrsp_flit | 1 / 1 / RSP_W | In / Out / In | RSP flit word |
| fub_txdat_valid / fub_txdat_ready / fub_txdat_flit | 1 / 1 / DAT_W | In / Out / In | DAT flit word |

### FUB Side: Receive Channels (valid/ready flits out)

| Port | Width | Direction | Description |
|---|---|---|---|
| fub_rxrsp_valid / fub_rxrsp_ready / fub_rxrsp_flit | 1 / 1 / RSP_W | Out / In / Out | RSP flit word (FIFO not empty / consumer ready) |
| fub_rxdat_valid / fub_rxdat_ready / fub_rxdat_flit | 1 / 1 / DAT_W | Out / In / Out | DAT flit word |
| fub_rxsnp_valid / fub_rxsnp_ready / fub_rxsnp_flit | 1 / 1 / SNP_W | Out / In / Out | SNP flit word; LCrdReturns never appear here |

### CHI Link: Activity and LINKACTIVE Pairs (B14.5, B14.7)

| Port | Width | Direction | Description |
|---|---|---|---|
| m_chi_txsactive | 1 | Output | `TXSACTIVE` (combinational from `fub_sactive` and the TX queues, held one more cycle) |
| m_chi_rxsactive | 1 | Input | `RXSACTIVE`, passed to `fub_rxsactive` |
| m_chi_txlinkactivereq / m_chi_txlinkactiveack | 1 | Out / In | Transmit direction pair; ACK is sampled into a flop |
| m_chi_rxlinkactivereq / m_chi_rxlinkactiveack | 1 | In / Out | Receive direction pair; REQ is synchronized |

### CHI Link: Transmit Channels

| Port | Width | Direction | Description |
|---|---|---|---|
| m_chi_txreqflitpend / m_chi_txreqflitv / m_chi_txreqflit / m_chi_txreqlcrdv | 1 / 1 / REQ_W / 1 | Out / Out / Out / In | TXREQ: `FLITPEND`, `FLITV`, `FLIT` (zero while not valid or for an LCrdReturn), `LCRDV` |
| m_chi_txrsp* | as above, RSP_W | | TXRSP |
| m_chi_txdat* | as above, DAT_W | | TXDAT |

### CHI Link: Receive Channels

| Port | Width | Direction | Description |
|---|---|---|---|
| m_chi_rxrspflitpend / m_chi_rxrspflitv / m_chi_rxrspflit / m_chi_rxrsplcrdv | 1 / 1 / RSP_W / 1 | In / In / In / Out | RXRSP; `LCRDV` is a flop |
| m_chi_rxdat* | as above, DAT_W | | RXDAT |
| m_chi_rxsnp* | as above, SNP_W | | RXSNP |

### Status

| Port | Width | Direction | Description |
|---|---|---|---|
| busy | 1 | Output | Any TX flit queued, any RX flit buffered, or either link not in STOP |
| tx_link_state | 2 | Output | `{TXLINKACTIVEREQ, TXLINKACTIVEACK sampled}`: 00 STOP, 10 ACTIVATE, 11 RUN, 01 DEACTIVATE |
| rx_link_state | 2 | Output | `{RXLINKACTIVEREQ synchronized, RXLINKACTIVEACK}` |
| txreq_credits / txrsp_credits / txdat_credits | CRW | Output | Credits held per TX channel |
| rxrsp_outstanding / rxdat_outstanding / rxsnp_outstanding | CRW | Output | Credits granted and not home per RX channel |
| credit_starved | 1 | Output | A flit waits in RUN with no credit on some TX channel |
| protocol_error | 1 | Output | Sticky OR of every channel's protocol error |

---

## Functional Description

### Block diagram

![chi_rnf_port block diagram](../../assets/rtl-amba/graphviz/chi_rnf_port.png)

Each TX channel is one column dropping from the FUB bar through its skid buffer and credit logic to the link; each RX channel climbs its own column from the link through the LCrdReturn decode into its FIFO, which is the credit pool, and out to the FUB. The two link controllers sit beside the columns and broadcast the direction state to every channel of their direction.

### Credits

Per TX channel, `r_credits` updates by `+LCRDV - FLITV` each cycle; a flit goes when the skid holds one, the direction is in RUN and `r_credits` is nonzero. `r_credits` is a register, so a grant cannot be spent in the cycle it arrives. A grant that would exceed `MAX_LCREDIT` is dropped and flagged. Per RX channel, `o_lcrdv` is a flop driven by `occupancy + outstanding < RX_FIFO_DEPTH` and `outstanding < MAX_LCREDIT`, evaluated for the state after this edge, so a slot freed by a FUB pop at cycle t backs a grant at t+1. Credits are granted only in RUN; flits are accepted in any state, which covers the ACTIVATE and DEACTIVATE races of Table B14.2.

### FLITPEND

`FLITPEND` is the next-cycle condition itself, computed from flops: a flit queued while in RUN, or a credit to return while in DEACTIVATE. It is registered into `r_pend`, and `FLITV` in a cycle requires `r_pend`, so every flit was announced the cycle before. A pend not followed by a flit (the credit never came, the direction changed) is permitted (B14.4). On receive, `FLITV` without `FLITPEND` the cycle before is a protocol error.

### Link control

| Direction | From | To | When |
|---|---|---|---|
| TX | STOP | ACTIVATE | `cfg_rx_enable` and `RXLINKACTIVEACK` low, and one of: a TX flit queued, `cfg_link_hold && cfg_link_enable`, the RX direction has left STOP (B14.6.1) |
| TX | ACTIVATE | RUN | `TXLINKACTIVEACK` sampled high |
| TX | RUN | DEACTIVATE | `RXLINKACTIVEACK` high, and either the RX direction is in DEACTIVATE, or nothing is queued, no hold, and `cfg_link_enable` is low or `cfg_idle_cycles` idle cycles have passed |
| TX | DEACTIVATE | STOP | the home drops ACK after every credit is home; meanwhile each channel returns one credit per cycle as an LCrdReturn |
| RX | ACTIVATE | RUN | synchronized REQ high, `cfg_rx_enable`, and `TXLINKACTIVEREQ` already high |
| RX | RUN | DEACTIVATE | REQ falls: granting stops at once, in-flight flits still accepted |
| RX | DEACTIVATE | STOP | every RX channel reports its credits home and `TXLINKACTIVEREQ` is low |

So `cfg_rx_enable = 0` holds the port in STOP (an activation it could not acknowledge is never started either), and `cfg_link_enable = 0` only stops the TX link being kept up. With `LINK_CTRL = 0` both directions are permanently RUN, the LINKACTIVE pins stay low, and the status reads 11 (RUN).

### SACTIVE

`TXSACTIVE` is high while `fub_sactive` is high or any TX channel holds a flit, and for one cycle after (`r_sactive`). The Protocol layer must hold `fub_sactive` from before its first request until its last completing flit is sent or received (B14.7.2); the link layer cannot know that on its own. `RXSACTIVE` is wired to `fub_rxsactive` so the Protocol layer can respond "in a timely manner" (B14.7.3).

### Status

`busy` is the clock-gating term: any flit queued or buffered, or a link away from STOP. `protocol_error` is the sticky OR of the six channels: a grant beyond the bound on a TX channel; on an RX channel a flit without `FLITPEND`, a flit with no credit outstanding, or an LCrdReturn with a non-zero TxnID.

---

## Timing Characteristics

- FUB to link: a flit accepted at cycle t sits in the skid at t+1, `FLITPEND` is raised at t+1 and `FLITV` at t+2 at the earliest.
- `LCRDV` at cycle t: usable at t+1; `FLITV` at t+1 if `FLITPEND` was already up.
- `TXLINKACTIVEACK` rising at t: RUN at t+1 (registered sample), `FLITPEND` at t+1, first flit at t+2.
- Link to FUB: the FIFO is in mux-read mode, so a flit received at t is offered at t+1. A slot freed at t supports a grant driven at t+1.
- Remote activation: REQ seen after `LINKACTIVE_SYNC_STAGES` cycles, `TXLINKACTIVEREQ` one cycle later, `RXLINKACTIVEACK` the cycle after that, first grant one more cycle on.
- Back-to-back flits at one per cycle need `MAX_LCREDIT` and the partner's pool at least as large as the credit round trip.

---

## Usage Example

```systemverilog
chi_rnf_port #(
    .NODEID_WIDTH  (7),
    .ADDR_WIDTH    (44),
    .DATA_WIDTH    (256),
    .MAX_LCREDIT   (8),
    .LINK_CTRL     (1'b1),
    .SKID_DEPTH    (4),
    .RX_FIFO_DEPTH (8)
) u_rn_port (
    .aclk (aclk), .aresetn (aresetn),
    .cfg_link_enable (1'b1), .cfg_link_hold (1'b0), .cfg_idle_cycles (8'd64),
    .cfg_rx_enable (1'b1),
    .fub_sactive (txn_in_progress), .fub_rxsactive (home_active),
    // Protocol layer: one packed flit word per channel, bit 0 first
    .fub_txreq_valid (req_v), .fub_txreq_ready (req_r), .fub_txreq_flit (req_word),
    .fub_txrsp_valid (rsp_v), .fub_txrsp_ready (rsp_r), .fub_txrsp_flit (rsp_word),
    .fub_txdat_valid (dat_v), .fub_txdat_ready (dat_r), .fub_txdat_flit (dat_word),
    .fub_rxrsp_valid (rrsp_v), .fub_rxrsp_ready (rrsp_r), .fub_rxrsp_flit (rrsp_word),
    .fub_rxdat_valid (rdat_v), .fub_rxdat_ready (rdat_r), .fub_rxdat_flit (rdat_word),
    .fub_rxsnp_valid (snp_v),  .fub_rxsnp_ready (snp_r),  .fub_rxsnp_flit (snp_word),
    // CHI link to the home: wire m_chi_* straight to the interconnect pins
    .m_chi_txsactive (TXSACTIVE), .m_chi_rxsactive (RXSACTIVE),
    .m_chi_txlinkactivereq (TXLINKACTIVEREQ), .m_chi_txlinkactiveack (TXLINKACTIVEACK),
    .m_chi_rxlinkactivereq (RXLINKACTIVEREQ), .m_chi_rxlinkactiveack (RXLINKACTIVEACK),
    .m_chi_txreqflitpend (TXREQFLITPEND), .m_chi_txreqflitv (TXREQFLITV),
    .m_chi_txreqflit (TXREQFLIT), .m_chi_txreqlcrdv (TXREQLCRDV),
    .m_chi_txrspflitpend (TXRSPFLITPEND), .m_chi_txrspflitv (TXRSPFLITV),
    .m_chi_txrspflit (TXRSPFLIT), .m_chi_txrsplcrdv (TXRSPLCRDV),
    .m_chi_txdatflitpend (TXDATFLITPEND), .m_chi_txdatflitv (TXDATFLITV),
    .m_chi_txdatflit (TXDATFLIT), .m_chi_txdatlcrdv (TXDATLCRDV),
    .m_chi_rxrspflitpend (RXRSPFLITPEND), .m_chi_rxrspflitv (RXRSPFLITV),
    .m_chi_rxrspflit (RXRSPFLIT), .m_chi_rxrsplcrdv (RXRSPLCRDV),
    .m_chi_rxdatflitpend (RXDATFLITPEND), .m_chi_rxdatflitv (RXDATFLITV),
    .m_chi_rxdatflit (RXDATFLIT), .m_chi_rxdatlcrdv (RXDATLCRDV),
    .m_chi_rxsnpflitpend (RXSNPFLITPEND), .m_chi_rxsnpflitv (RXSNPFLITV),
    .m_chi_rxsnpflit (RXSNPFLIT), .m_chi_rxsnplcrdv (RXSNPLCRDV),
    // status, left to a monitor
    .busy (), .tx_link_state (), .rx_link_state (),
    .txreq_credits (), .txrsp_credits (), .txdat_credits (),
    .rxrsp_outstanding (), .rxdat_outstanding (), .rxsnp_outstanding (),
    .credit_starved (), .protocol_error (rn_proto_err)
);
```

---

## Related Modules

- **[CHI HN-F Port](chi_hnf_port.md)**: the other end of the link pair
- **[CHI Modules](README.md)**: `chi_pkg`, `chi_tx_channel`, `chi_rx_channel`, `chi_link_tx`, `chi_link_rx`
- **[CXS Master](../cxs/cxs_master.md)** / **[CXS Slave](../cxs/cxs_slave.md)**: the single-link credited endpoints this family extends
- `gaxi_skid_buffer`, `gaxi_fifo_sync`, `glitch_free_n_dff_arn`

---

## Testing

`val/amba/test_chi_rnf_port.py` (TB `bin/TBClasses/chi/chi_rnf_port_tb.py`) drives the FUB side with GAXI BFMs and the link side with the framework `CHIHomeNode` on `m_chi_`, serving from its own memory, with a `CHIMonitor` on the same pins. The TB plays a minimal RN-F Protocol layer at flit level: ReadNoSnp and WriteNoSnpFull with unique TxnIDs, CompData reassembled by DataID against a reference memory, write data on the DBID, SnpResp_I to a home snoop, `fub_sactive` while anything is in flight. Phases: fast, starve, gappy, back-to-back, pool fill, and with `LINK_CTRL` hold, idle deactivation, snoop wake, remote activation, reactivation and churn.

```bash
source env_python
cd val/amba && make clean-all && make run-chi_rnf_port-func-parallel
```

## References

- Arm. *AMBA 5 CHI Architecture Specification*, ARM IHI 0050 Issue H. [developer.arm.com/documentation/ihi0050](https://developer.arm.com/documentation/ihi0050/latest/): B13.2 link pairs, Table B13.1 RN-F channels, B13.11 Link flits, B14.2.1.1 L-Credits, B14.4 FLITPEND, B14.5 and Tables B14.1 / B14.2 link activation, B14.6.1 and B14.6.3.4 the two directions, B14.7.2 TXSACTIVE, B14.7.3 RXSACTIVE. Citation only.

---

## Navigation

- **[Back to CHI Index](README.md)**
- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
