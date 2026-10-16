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

# CXS Slave

**Module:** `cxs_slave.sv`
**Location:** `rtl/amba/cxs/`
**Status:** New (2026-10-15)

---

## Overview

`cxs_slave` is a CXS receiver endpoint, the CXS counterpart of `axis4_slave`. Flits arrive on the credited link, land in a receive FIFO, and leave on a valid/ready FUB port. The receive FIFO **is** the credit pool. A credit is granted only when a FIFO slot is free to back it, so the receiver never refuses a flit. That is the guarantee 2.1.2 requires ("the Receiver must guarantee that it can receive one flit of data for each credit that it grants").

### Key Features

- Credit grant bounded by FIFO room and `CXS_MAX_CREDIT`; a spent or returned credit is reissued the next cycle at the earliest
- `RX_FIFO_DEPTH` may be smaller than `CXS_MAX_CREDIT`, in which case the FIFO sets the pool size
- Link control: synchronizes the asynchronous `CXSACTIVEREQ`, raises `CXSACTIVEACK`, grants only in RUN, and drops ACK only once every credit is home
- `CXSDEACTHINT` driven from `cfg_deact_hint`
- `Odd_Byte_Parity` checking of every received signal, with its own check signals generated
- Sticky `protocol_error`: a flit or return with no credit, `CXSVALID` together with `CXSCRDRTN`, FIFO overflow, malformed `CXSCNTL`

---

## Parameters

The `CXS_*` property parameters are the same as for [cxs_master](cxs_master.md#parameters). Two more:

| Parameter | Type | Default | Description |
|---|---|---|---|
| RX_FIFO_DEPTH | int | CXS_MAX_CREDIT | Receive FIFO depth, i.e. the credit pool. Any depth >= 1. Below the credit round trip it throttles the link |
| CXS_CREDIT_BEYOND_SPEC | bit | 0 | Lift the 63-credit cap (rule 12) for a whole-SRAM pool; both ends must agree |
| CXS_STREAM_PRCL_BITS / CXS_STREAM_SRCID_BITS / CXS_STREAM_TGTID_BITS | int | 0 | Per-stream packet framing key (see [Streams and Interleaving](README.md#streams-and-interleaving)); 0/0/0 = one stream |
| ACTIVEREQ_SYNC_STAGES | int | 2 | Synchronizer flops on `CXSACTIVEREQ` (and its check bit); 0 = known-synchronous system |

Derived values (`CNTL_W`, the `*_PW` port widths, the check widths and `CRW`) are as for `cxs_master`.

---

## Ports

### Clock, Reset and Configuration

| Port | Width | Direction | Description |
|---|---|---|---|
| aclk / aresetn | 1 | Input | Clock, active-low asynchronous reset |
| cfg_rx_enable | 1 | Input | 0 = never activate, never grant |
| cfg_deact_hint | 1 | Input | Drives `CXSDEACTHINT` (registered) |

### CXS Receiver Interface

| Port | Width | Direction | Description |
|---|---|---|---|
| s_cxs_valid | 1 | Input | `CXSVALID` |
| s_cxs_data, s_cxs_cntl, s_cxs_last, s_cxs_prcltype, s_cxs_srcid, s_cxs_tgtid, s_cxs_user | see cxs_master | Input | Flit payload; absent signals ignored |
| s_cxs_crdgnt | 1 | Output | `CXSCRDGNT`, registered |
| s_cxs_crdrtn | 1 | Input | `CXSCRDRTN` |
| s_cxs_activereq | 1 | Input | `CXSACTIVEREQ`, asynchronous, synchronized here |
| s_cxs_activeack | 1 | Output | `CXSACTIVEACK` |
| s_cxs_deacthint | 1 | Output | `CXSDEACTHINT` |

### Check Signals (CXS_CHECK = 1)

The `s_cxs_*chk` inputs mirror the `m_cxs_*chk` outputs of `cxs_master`. `s_cxs_crdgntchk` and `s_cxs_activeackchk` are generated outputs.

### FUB Interface (valid/ready, output side)

| Port | Width | Direction | Description |
|---|---|---|---|
| fub_cxs_valid / fub_cxs_ready | 1 | Out / In | FIFO not empty / consumer ready |
| fub_cxs_data ... fub_cxs_user | as received | Output | The flit, absent fields zero |

### Status

| Port | Width | Direction | Description |
|---|---|---|---|
| busy | 1 | Output | A flit arriving or queued, credits out, or link state other than STOP |
| credits_outstanding | CRW | Output | Granted and not yet spent or returned |
| link_state | 2 | Output | {synchronized ACTIVEREQ, ACTIVEACK} |
| in_packet | 1 | Output | A packet started and not yet ended |
| protocol_error / parity_error | 1 | Output | Sticky error flags |

---

## Functional Description

### Credit pool

`r_out` counts credits outstanding, including the grant on the wire this cycle. Each cycle the block works out the state after the clock edge, before any new grant:

```
out_next = r_out + CXSCRDGNT(now) - CXSVALID - CXSCRDRTN
occ_next = fifo_count + CXSVALID - fub_pop
grant    = RUN && out_next < CXS_MAX_CREDIT && occ_next + out_next < RX_FIFO_DEPTH
```

`r_crdgnt <= grant`, so `CXSCRDGNT` is a flop fed from flops and this cycle's handshake. A credit consumed at cycle t is reissued at t+1 at the earliest.

`gaxi_fifo_sync` cannot be built 1 deep, but one credit with a one-flit buffer is a legal receiver. The FIFO is therefore built at least 2 deep while the grant still uses `RX_FIFO_DEPTH`, so the spare slot is never granted against.

### Link control

`CXSACTIVEREQ` and `CXSACTIVEREQCHK` cross through one `glitch_free_n_dff_arn`. The check bit crosses **inverted**: the synchronizer flops reset to 0, and the correct check for a reset-low ACTIVEREQ is 1. Carried uninverted, the pair would read `{0,0}`, a parity error, for every cycle the synchronizer is flushing after reset. The test suite caught exactly that.

- ACTIVATE to RUN: `CXSACTIVEACK` rises when the synchronized ACTIVEREQ is high and `cfg_rx_enable` is set.
- Credits are granted only while both are high.
- DEACTIVATE: flits still in flight are accepted, and ACK falls only when `out_next` is 0.

---

## Timing Characteristics

- Link to FUB: the FIFO is in mux-read mode, so a flit received at cycle t is offered at t+1.
- Credit reuse: a slot freed at cycle t (FUB pop) supports a grant driven at t+1.
- ACTIVEREQ to ACTIVEACK: `ACTIVEREQ_SYNC_STAGES` + 1 cycles; the first grant follows one cycle after ACK.

---

## Usage Example

```systemverilog
cxs_slave #(
    .CXS_ISSUE            (cxs_pkg::CXS_ISSUE_D),
    .CXS_DATA_WIDTH       (256),
    .CXS_MAX_PKT_PER_FLIT (3),
    .CXS_START_ALIGN      (4),
    .CXS_SRCID_WIDTH      (4),
    .CXS_TGTID_WIDTH      (2),
    .CXS_MAX_CREDIT       (15),
    .RX_FIFO_DEPTH        (8)
) u_cxs_rx (
    .aclk (aclk), .aresetn (aresetn),
    .cfg_rx_enable (1'b1), .cfg_deact_hint (want_idle),
    .s_cxs_valid (CXSRXVALID), .s_cxs_data (CXSRXDATA), .s_cxs_cntl (CXSRXCNTL),
    .s_cxs_last ('0), .s_cxs_prcltype ('0),
    .s_cxs_srcid (CXSRXSRCID), .s_cxs_tgtid (CXSRXTGTID), .s_cxs_user ('0),
    .s_cxs_crdgnt (CXSRXCRDGNT), .s_cxs_crdrtn (CXSRXCRDRTN),
    .s_cxs_activereq (CXSRXACTIVEREQ), .s_cxs_activeack (CXSRXACTIVEACK),
    .s_cxs_deacthint (CXSRXDEACTHINT),
    // check inputs tied when CXS_CHECK = 0
    .s_cxs_validchk ('0), .s_cxs_datachk ('0), .s_cxs_cntlchk ('0), .s_cxs_lastchk ('0),
    .s_cxs_prcltypechk ('0), .s_cxs_srcidchk ('0), .s_cxs_tgtidchk ('0), .s_cxs_userchk ('0),
    .s_cxs_crdrtnchk ('0), .s_cxs_activereqchk ('0),
    .s_cxs_crdgntchk (), .s_cxs_activeackchk (),
    .fub_cxs_valid (rx_valid), .fub_cxs_ready (rx_ready), .fub_cxs_data (rx_data),
    .fub_cxs_cntl (rx_cntl), .fub_cxs_last (), .fub_cxs_prcltype (),
    .fub_cxs_srcid (rx_src), .fub_cxs_tgtid (rx_tgt), .fub_cxs_user (),
    .busy (), .credits_outstanding (), .link_state (), .in_packet (),
    .protocol_error (rx_proto_err), .parity_error ()
);
```

---

## Related Modules

- **[CXS Master](cxs_master.md)**: the transmitter
- **[CXS Slave CG](cxs_slave_cg.md)**: clock-gated variant
- **[AXIS4 Slave](../axis4/axis4_slave.md)**: the valid/ready endpoint this one mirrors
- `gaxi_fifo_sync`, `glitch_free_n_dff_arn`, `cxs_cntl_track`, `cxs_odd_byte_parity`

---

## Testing

`val/amba/test_cxs_slave.py` uses the framework `CXSTransmitter` on `s_cxs_*`, a GAXI slave on `fub_cxs_*`, and a `CXSMonitor`. Every config runs twice, once with `RX_FIFO_DEPTH = CXS_MAX_CREDIT` and once with a 3-deep FIFO. The idle pool-fill phase requires exactly `min(RX_FIFO_DEPTH, CXS_MAX_CREDIT)` credits at the transmitter.

```bash
source env_python
cd val/amba && make clean-all && make run-cxs_slave-func-parallel
```

## References

- Arm. *AMBA CXS Protocol Specification*, ARM IHI 0079D, Sep. 2025 (and Issues A-C). [developer.arm.com/documentation/ihi0079/d](https://developer.arm.com/documentation/ihi0079/d/): 2.1.2 credit rules, 5.2 receiver obligations in each state, 5.4 race conditions, 5.5 asynchronous `CXSACTIVEREQ`. Citation only.

---

## Navigation

- **[Back to CXS Index](README.md)**
- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
