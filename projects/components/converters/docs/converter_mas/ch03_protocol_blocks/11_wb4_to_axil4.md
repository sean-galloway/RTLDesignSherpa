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

# 3.11 Wishbone B4 to AXI4-Lite Converter

The **wb4_to_axil4** converter presents a Wishbone B4 slave and drives an
AXI4-Lite master. It is the mirror of [3.10](10_axil4_to_wb4.md) and the
harder direction, for one reason given below.

## 3.11.1 Module Organization

```
wb4_to_axil4.sv              # Wrapper: slave + core + the two masters
├── wb4_slave.sv             # Wishbone bus -> cmd/rsp queues (rtl/amba/wb4)
├── wb4_to_axil4_core.sv     # Queues -> five AXI4-Lite channels, responses merged
├── axil4_master_wr.sv       # AW / W / B channels (rtl/amba/axil4)
└── axil4_master_rd.sv       # AR / R channels (rtl/amba/axil4)
```

## 3.11.2 Why This Direction Is Harder

Going AXI4-Lite to Wishbone, the two request paths merge into one bus and
the answers come back in issue order for free, because that is what
Wishbone does.

Coming back the other way the ordering runs against you. **Wishbone B4
terminates in issue order. AXI4-Lite's B and R channels are independent and
a slave may answer them in any order.** A read issued behind a slow write
will routinely finish first. If the converter passed each response straight
through, the Wishbone master would see its transfers terminate out of order,
which the protocol forbids and its own bookkeeping would mispair.

So the core records the direction of every command it issues in an in-order
side queue and releases only the response at the head. A response that
completed early waits in its channel's skid until its predecessors have
retired.

**Ordering cost.** A slow write at the head holds back a read that finished
behind it. `OUTSTANDING = 1` avoids the question entirely and is the
default; raise it only when the AXI slave answers roughly in order, or
head-of-line waiting eats the benefit.

## 3.11.3 Interface Specification

### Parameters

| Parameter | Default | Description |
| --- | --- | --- |
| ADDR_WIDTH | 32 | Address width, both sides |
| DATA_WIDTH | 32 | Data width, both sides |
| CMD_DEPTH / RSP_DEPTH | 2 | The wb4_slave's queue depths |
| MAX_OUTSTANDING | 16 | The wb4_slave's bus-side bound |
| CLASSIC | 0 | 0 = B4 pipelined, 1 = B4 standard; match the Wishbone master |
| OUTSTANDING | 1 | Commands in flight through the core. 1 = strictly serialised |
| SKID_DEPTH_AW/W/B/AR/R | 2 | The AXI4-Lite masters' channel skids |
| AXIL_PROT | 3'b000 | `AWPROT`/`ARPROT` driven on every command |

: Table 3.31: Wishbone to AXI4-Lite Parameters

### Ports

| Port group | Direction | Description |
| --- | --- | --- |
| `s_wb_CYC/STB/WE/ADR/DAT_W/SEL/CTI/BTE` | in | Wishbone request |
| `s_wb_STALL/ACK/ERR/RTY/DAT_R` | out | Flow control and termination |
| `m_axil_aw*`, `m_axil_w*`, `m_axil_b*` | master | AXI4-Lite write channels |
| `m_axil_ar*`, `m_axil_r*` | master | AXI4-Lite read channels |
| `busy` | out | Anything buffered, or a cycle open on the Wishbone side |

: Table 3.32: Wishbone to AXI4-Lite Ports

## 3.11.4 Command Formation

| Wishbone | AXI4-Lite |
| --- | --- |
| `WE=1`, `ADR`, `DAT_W`, `SEL` | `AWADDR` + `WDATA`, `WSTRB` = `SEL` |
| `WE=0`, `ADR` | `ARADDR` |
| `CTI` / `BTE` | **dropped** (see below) |
| - | `AWPROT`/`ARPROT` = `AXIL_PROT` |

: Table 3.33: Command Formation

A write only launches when **both** `AWREADY` and `WREADY` are high in the
same clock. Letting `AW` go while `W` stalled would leave a half-issued
transfer that the outstanding count could not describe honestly.

**The burst hints stop here.** `CTI` and `BTE` describe a registered-feedback
burst, and AXI4-Lite is single-beat with no field to carry them. A
burst-aware target behind an AXI4-Lite bus is a contradiction, so the
converter drops them rather than inventing a mapping.

## 3.11.5 Response Mapping

| AXI4-Lite `BRESP` / `RRESP` | Wishbone termination |
| --- | --- |
| OKAY | `ACK` |
| SLVERR | `ERR` |
| DECERR | `ERR` |
| - | `RTY` is never produced |

: Table 3.34: Response Mapping

B4 has one error termination and no way to say which kind, so SLVERR and
DECERR both become `ERR`. `RTY` never appears because an AXI slave has no
way to ask for a retry; a Wishbone master that wants retries needs
[`wb4_retry`](../../../../../docs/markdown/rtl-amba/wb4/wb4_retry.md) on the
other side of the bus, not here.

## 3.11.6 Formal

`formal/converters/wb4_to_axil4_core/` proves: a write takes `AW` and `W` in
the same clock and never one alone; a command becomes a write or a read,
never both; the response consumed is the head's channel **and is backed by a
real response on that channel**; the open count never exceeds `OUTSTANDING`;
OKAY becomes `ACK`, any error becomes `ERR`, and `RTY` is never produced.

The backing property earned its place. An earlier property set proved every
ordering rule above and still passed a mutation that asserted `rsp_valid`
whenever *either* channel had a response, returning a status read off a
channel that had nothing. Simulation caught it as a hang; formal did not,
until the property was added.

## 3.11.7 Testing

`dv/tests/test_wb4_to_axil4.py` drives `s_wb_*` with the framework's
Wishbone master BFM and answers `m_axil_*` with the AXI4-Lite slave BFMs
over one shared memory model, so a write really lands where a later read
finds it. Addresses beyond the memory model answer SLVERR and must arrive as
`ERR`.

The phases are sequential traffic, pipelined traffic under gappy and sparse
request pacing, and a directed **ordering probe**: write-then-read pairs
where the testbench answers the write channel slowly and the read channel
quickly, so the AXI side completes the read first every time. The scoreboard
pairs terminations with issue order, so a response that overtook its
predecessor shows up as a status or data mismatch rather than as silence.

Three RTL mutations fail the test: completing from whichever channel is
ready, corrupting read data, and launching `AW` without `W`.

## 3.11.8 Usage Example

```systemverilog
wb4_to_axil4 #(
    .ADDR_WIDTH  (32),
    .DATA_WIDTH  (32),
    .OUTSTANDING (1),      // raise only if the AXI slave answers in order
    .CLASSIC     (0)
) u_wb_to_axil (
    .aclk (clk), .aresetn (rst_n),
    .s_wb_CYC (wb_cyc), .s_wb_STB (wb_stb), .s_wb_WE (wb_we), .s_wb_ADR (wb_adr),
    .s_wb_DAT_W (wb_dat_w), .s_wb_SEL (wb_sel), .s_wb_CTI (wb_cti), .s_wb_BTE (wb_bte),
    .s_wb_STALL (wb_stall), .s_wb_ACK (wb_ack), .s_wb_ERR (wb_err), .s_wb_RTY (wb_rty),
    .s_wb_DAT_R (wb_dat_r),
    .m_axil_awaddr (awaddr), .m_axil_awprot (awprot), .m_axil_awvalid (awvalid), .m_axil_awready (awready),
    .m_axil_wdata (wdata), .m_axil_wstrb (wstrb), .m_axil_wvalid (wvalid), .m_axil_wready (wready),
    .m_axil_bresp (bresp), .m_axil_bvalid (bvalid), .m_axil_bready (bready),
    .m_axil_araddr (araddr), .m_axil_arprot (arprot), .m_axil_arvalid (arvalid), .m_axil_arready (arready),
    .m_axil_rdata (rdata), .m_axil_rresp (rresp), .m_axil_rvalid (rvalid), .m_axil_rready (rready),
    .busy ()
);
```

## Navigation

**Next:** [APB to AXI4 (Requester)](12_apb_to_axi4.md)
