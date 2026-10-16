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

# CXS Master

**Module:** `cxs_master.sv`
**Location:** `rtl/amba/cxs/`
**Status:** New (2026-10-15)

---

## Overview

`cxs_master` is a CXS transmitter endpoint, the CXS counterpart of `axis4_master`. Flits arrive on a valid/ready FUB port, wait in a skid buffer, and leave on the credited CXS link one per cycle while the transmitter holds a credit and the link is in RUN. One parameter set covers every issue of IHI 0079 (see [CXS Modules](README.md)).

### Key Features

- Credit counter for up to `CXS_MAX_CREDIT` credits; a grant is usable the cycle after it arrives (2.1.2)
- Link activation and deactivation (`Explicit_Credit_Return`): raises `CXSACTIVEREQ` on demand, returns every credit on `CXSCRDRTN` before STOP, never deactivates mid-packet
- Deactivation on idleness (`cfg_idle_cycles`), on `CXSDEACTHINT`, or on `cfg_link_enable` low
- `Odd_Byte_Parity` check-signal generation, with receiver check signals verified every cycle
- All optional signals: `CXSCNTL`, `CXSLAST`, `CXSPRCLTYPE`, `CXSSRCID`, `CXSTGTID`, `CXSUSER`
- No output depends combinationally on an input
- Sticky `protocol_error` and `parity_error` status

---

## Parameters

The `CXS_*` property parameters are described in [CXS Modules: Properties and Parameters](README.md#properties-and-parameters). An illegal combination for `CXS_ISSUE` stops elaboration with the rule number.

| Parameter | Type | Default | Description |
|---|---|---|---|
| CXS_ISSUE | int | 4 (D) | Spec issue the property set is checked against |
| CXS_DATA_WIDTH | int | 256 | `CXSDATAFLITWIDTH` |
| CXS_MAX_PKT_PER_FLIT | int | 2 | `CXSMAXPKTPERFLIT`; 1 = CXS-Lite (no `CXSCNTL`) |
| CXS_START_ALIGN | int | 16 | `CXS_START_ALIGNMENT` in bytes |
| CXS_HAS_LAST / CXS_HAS_PRCLTYPE | bit | 0 | `CXS_LAST` / `CXS_PROTOCOL_TYPE` |
| CXS_SRCID_WIDTH / CXS_TGTID_WIDTH / CXS_USER_WIDTH | int | 0 | Issue D sideband widths, 0 = absent |
| CXS_MAX_CREDIT | int | 15 | Credits this transmitter can track |
| CXS_CREDIT_BEYOND_SPEC | bit | 0 | Lift the 63-credit cap (rule 12) for a whole-SRAM pool; both ends must agree |
| CXS_STREAM_PRCL_BITS / CXS_STREAM_SRCID_BITS / CXS_STREAM_TGTID_BITS | int | 0 | Per-stream packet framing key (see [Streams and Interleaving](README.md#streams-and-interleaving)); 0/0/0 = one stream |
| CXS_LINK_CTRL | bit | 1 | 1 = `Explicit_Credit_Return` |
| CXS_CHECK | bit | 0 | 1 = `Odd_Byte_Parity` |
| SKID_DEPTH | int | 4 | FUB skid buffer depth, 2..8 |

### Derived Values (do not override)

| Name | Derivation | Meaning |
|---|---|---|
| CNTL_W | `cxs_pkg::cntl_width(N, DW, CXS_START_ALIGN)` | `CXSCNTLWIDTH`, 0 for CXS-Lite |
| CNTL_PW / SRCID_PW / TGTID_PW / USER_PW | max(width, 1) | Port widths of optional signals |
| DATACHK_W | DW/8 | `CXSDATACHK` width |
| CNTLCHK_W / USERCHK_W | max(ceil(width/8), 1) | `CXSCNTLCHK` / `CXSUSERCHK` widths |
| CRW | clog2(CXS_MAX_CREDIT + 1) | Credit counter width |

---

## Ports

### Clock, Reset and Configuration

| Port | Width | Direction | Description |
|---|---|---|---|
| aclk | 1 | Input | Clock |
| aresetn | 1 | Input | Active-low asynchronous reset |
| cfg_link_enable | 1 | Input | 0 = take the link down when idle and never raise it |
| cfg_link_hold | 1 | Input | 1 = keep the link in RUN with nothing to send |
| cfg_idle_cycles | 8 | Input | Idle RUN cycles before deactivating; 0 = never on idleness alone |

### FUB Interface (valid/ready, input side)

| Port | Width | Direction | Description |
|---|---|---|---|
| fub_cxs_valid / fub_cxs_ready | 1 | In / Out | Flit handshake (ready = skid not full) |
| fub_cxs_data | DW | Input | Flit data; byte n is `data[8n+7:8n]` |
| fub_cxs_cntl | CNTL_PW | Input | `CXSCNTL`, passed through unchanged |
| fub_cxs_last | 1 | Input | `CXSLAST` |
| fub_cxs_prcltype | 3 | Input | `CXSPRCLTYPE` |
| fub_cxs_srcid / fub_cxs_tgtid / fub_cxs_user | *_PW | Input | Issue D sidebands |

### CXS Transmitter Interface

| Port | Width | Direction | Description |
|---|---|---|---|
| m_cxs_valid | 1 | Output | `CXSVALID`: a flit this cycle (spends a credit) |
| m_cxs_data, m_cxs_cntl, m_cxs_last, m_cxs_prcltype, m_cxs_srcid, m_cxs_tgtid, m_cxs_user | as FUB | Output | Flit payload; zero while `CXSVALID` is low |
| m_cxs_crdgnt | 1 | Input | `CXSCRDGNT`: one credit per cycle |
| m_cxs_crdrtn | 1 | Output | `CXSCRDRTN`: a credit returned (only while `CXSACTIVEREQ` is low) |
| m_cxs_activereq | 1 | Output | `CXSACTIVEREQ` |
| m_cxs_activeack | 1 | Input | `CXSACTIVEACK`, sampled into a flop |
| m_cxs_deacthint | 1 | Input | `CXSDEACTHINT`, sampled into a flop |

### Check Signals (CXS_CHECK = 1)

| Port | Width | Direction | Description |
|---|---|---|---|
| m_cxs_validchk | 1 | Output | `~CXSVALID` |
| m_cxs_datachk | DATACHK_W | Output | Odd parity, bit n covers `data[8n+7:8n]` |
| m_cxs_cntlchk | CNTLCHK_W | Output | Odd parity over `CXSCNTL`, short top byte |
| m_cxs_lastchk / m_cxs_prcltypechk / m_cxs_srcidchk / m_cxs_tgtidchk | 1 | Output | One bit each |
| m_cxs_userchk | USERCHK_W | Output | Odd parity over `CXSUSER` |
| m_cxs_crdrtnchk / m_cxs_activereqchk | 1 | Output | Inversions |
| m_cxs_crdgntchk / m_cxs_activeackchk | 1 | Input | Checked every cycle out of reset |

### Status

| Port | Width | Direction | Description |
|---|---|---|---|
| busy | 1 | Output | Any FUB flit, skid entry, credit held, or link state other than STOP |
| credits | CRW | Output | Credits held |
| link_state | 2 | Output | {ACTIVEREQ, sampled ACTIVEACK}: 00 STOP, 10 ACTIVATE, 11 RUN, 01 DEACTIVATE |
| in_packet | 1 | Output | A packet started on the link and not yet ended |
| protocol_error | 1 | Output | Sticky: a grant past `CXS_MAX_CREDIT`, ACK without REQ, or malformed `CXSCNTL` from the FUB |
| parity_error | 1 | Output | Sticky: `CXSCRDGNTCHK` or `CXSACTIVEACKCHK` mismatch |

---

## Functional Description

### Credits

`r_credits` updates every cycle by `+CXSCRDGNT - CXSVALID - CXSCRDRTN`. A gain and a spend in the same cycle cancel. A flit goes out when the skid holds one, the link is in RUN, and `r_credits` is nonzero. `r_credits` is a register, so a grant cannot be spent in the cycle it arrives. A grant that would push the count past `CXS_MAX_CREDIT` is dropped and flagged in `protocol_error`.

### Link control

| From | To | When |
|---|---|---|
| STOP | ACTIVATE | `cfg_link_enable` and (a FUB flit, a skid entry, or `cfg_link_hold`) |
| ACTIVATE | RUN | the receiver raises `CXSACTIVEACK` |
| RUN | DEACTIVATE | skid empty, no packet open, and one of: `cfg_link_enable` low, `CXSDEACTHINT` with nothing to send, `cfg_idle_cycles` idle cycles |
| DEACTIVATE | STOP | the receiver drops `CXSACTIVEACK` after every credit is home |

While `CXSACTIVEREQ` is low, `CXSCRDRTN` returns one held credit per cycle, including grants that arrive late. `CXSVALID` needs `CXSACTIVEREQ`, so the two are never high together.

### Packet tracking

`cxs_cntl_track` counts the packets each sent flit starts and ends. That gives `in_packet`, which blocks deactivation, and format checks: thermometer `START`/`END`, `ENDERROR` only with `END`, and no packet ending before it started.

---

## Timing Characteristics

- FUB to link: one skid buffer, so a flit accepted at cycle t can be sent at t+1 at the earliest.
- `CXSCRDGNT` at cycle t: usable at t+1.
- `CXSACTIVEACK` rising at cycle t: the first flit goes at t+1 at the earliest (registered sample).
- Back-to-back flits at one per cycle need `CXS_MAX_CREDIT` at least as large as the credit round trip (2.1.2).

---

## Usage Example

```systemverilog
cxs_master #(
    .CXS_ISSUE            (cxs_pkg::CXS_ISSUE_B),
    .CXS_DATA_WIDTH       (512),
    .CXS_MAX_PKT_PER_FLIT (2),
    .CXS_HAS_LAST         (1'b1),
    .CXS_MAX_CREDIT       (15),
    .CXS_LINK_CTRL        (1'b1),
    .CXS_CHECK            (1'b0)
) u_cxs_tx (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .cfg_link_enable (1'b1),
    .cfg_link_hold   (1'b0),
    .cfg_idle_cycles (8'd32),
    .fub_cxs_valid   (flit_valid),   .fub_cxs_ready   (flit_ready),
    .fub_cxs_data    (flit_data),    .fub_cxs_cntl    (flit_cntl),
    .fub_cxs_last    (flit_last),    .fub_cxs_prcltype(3'b000),
    .fub_cxs_srcid   ('0), .fub_cxs_tgtid ('0), .fub_cxs_user ('0),
    .m_cxs_valid     (CXSTXVALID),   .m_cxs_data      (CXSTXDATA),
    .m_cxs_cntl      (CXSTXCNTL),    .m_cxs_last      (CXSTXLAST),
    .m_cxs_crdgnt    (CXSTXCRDGNT),  .m_cxs_crdrtn    (CXSTXCRDRTN),
    .m_cxs_activereq (CXSTXACTIVEREQ), .m_cxs_activeack (CXSTXACTIVEACK),
    .m_cxs_deacthint (CXSTXDEACTHINT),
    .m_cxs_crdgntchk ('0), .m_cxs_activeackchk ('0),
    // remaining outputs left unconnected or monitored
    .busy (), .credits (), .link_state (), .in_packet (),
    .protocol_error (tx_proto_err), .parity_error ()
);
```

---

## Design Notes

- **The FUB supplies `CXSCNTL`.** This block carries flits; it does not pack packets into them. The framework `CXSPacketizer` shows the placement rules.
- **CXS-Lite** (`CXS_MAX_PKT_PER_FLIT = 1`, Issue C/D): there is no `CXSCNTL`, every flit is one packet, and `in_packet` is always 0.
- **Check signals are generated, not carried.** Protection starts at the interface, so the payload `*CHK` bits are computed from the outgoing flit. That differs from `axis5_master`, which carries the FUB's check bits end to end.

---

## Related Modules

- **[CXS Slave](cxs_slave.md)**: the receiver
- **[CXS Master CG](cxs_master_cg.md)**: clock-gated variant
- **[AXIS4 Master](../axis4/axis4_master.md)**: the valid/ready endpoint this one mirrors
- `gaxi_skid_buffer`, `cxs_cntl_track`, `cxs_odd_byte_parity`, `cxs_pkg`

---

## Testing

`val/amba/test_cxs_master.py` uses a GAXI master on `fub_cxs_*`, the framework `CXSReceiver` on `m_cxs_*`, and an independent `CXSMonitor`. The phases are fast, starve, gappy, back-to-back, idle pool fill, idle deactivation, reactivation, hint deactivation, mid-packet idle and parity injection.

```bash
source env_python
cd val/amba && make clean-all && make run-cxs_master-func-parallel
```

## References

- Arm. *AMBA CXS Protocol Specification*, ARM IHI 0079D, Sep. 2025 (and Issues A-C). [developer.arm.com/documentation/ihi0079/d](https://developer.arm.com/documentation/ihi0079/d/): 2.1.1 clock and reset, 2.1.2 credit exchange, 3.2 check signals, 5.2-5.6 link activation, 6.1 continuous delivery. Citation only.

---

## Navigation

- **[Back to CXS Index](README.md)**
- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
