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

# 3.10 AXI4-Lite to Wishbone B4 Converter

The **axil4_to_wb4** converter presents an AXI4-Lite slave and drives a
Wishbone B4 master. It is the bridge to drop in when an AXI4-Lite
interconnect has to reach a Wishbone peripheral, and it is built from parts
the library already has: the AXI4-Lite slave skids, a small conversion
core, and `wb4_master` from `rtl/amba/wb4/`.

## 3.10.1 Module Organization

```
axil4_to_wb4.sv              # Wrapper: skids + core + wb4_master
├── axil4_slave_wr.sv        # AW / W / B skid buffers (rtl/amba/axil4)
├── axil4_slave_rd.sv        # AR / R skid buffers (rtl/amba/axil4)
├── axil4_to_wb4_core.sv     # Five channels -> one command and one response queue
└── wb4_master.sv            # Queues -> Wishbone B4 bus (rtl/amba/wb4)
```

## 3.10.2 Design Philosophy

**One queue, in order.** AXI4-Lite has separate write and read paths;
Wishbone has one bus. The core merges the two paths into the single
command queue of `wb4_master` and relies on a B4 rule to route the
answers back: terminations return in issue order. A one-bit side queue,
written at issue with the direction of each command, tells the core
whether the oldest response belongs on B or on R. There is no ID, no
reorder buffer, and no state machine.

**No starvation.** A write is eligible when both AW and W are present, a
read when AR is. When both are eligible in the same clock the side not
served last is picked, so a stream of writes cannot hold reads off the bus
and vice versa.

**Wishbone status becomes an AXI response, nothing more.** `ACK` maps to
`OKAY`, `ERR` to `SLVERR`, and `RTY` to the `RTY_RESP` parameter
(`SLVERR` by default). AXI has no retry, so a retrying Wishbone slave is
reported to the requester as an error; a retry wrapper on the FUB side of
`wb4_master` is the place to absorb `RTY` transparently.

**No width conversion.** The AXI4-Lite and Wishbone address and data
widths are the same. Put `axi4_dwidth_*` or the wide-alignment blocks in
front when the interconnect width differs.

## 3.10.3 Block Diagram

### Figure 3.12: AXI4-Lite to Wishbone B4 Converter

```
 s_axil_aw ──► skid ──► fub_aw ─┐
 s_axil_w  ──► skid ──► fub_w  ─┤ pick        cmd_{we,adr,dat,sel} ──► wb4_master ──► m_wb_*
 s_axil_ar ──► skid ──► fub_ar ─┘ (alternate)         │
                                     │ side queue (we per issue)
 s_axil_b  ◄── skid ◄── fub_b  ◄─┐   ▼
 s_axil_r  ◄── skid ◄── fub_r  ◄─┴─ steer ◄── rsp_{status,dat} ◄── wb4_master
```

## 3.10.4 Interface Specification

### Parameters

| Parameter | Default | Description |
| --- | --- | --- |
| ADDR_WIDTH | 32 | Address width, both sides |
| DATA_WIDTH | 32 | Data width, both sides |
| SKID_DEPTH_AW/W/B/AR/R | 2 | AXI4-Lite channel skid depths (2..8) |
| CMD_DEPTH | 4 | `wb4_master` command queue depth |
| RSP_DEPTH | 4 | `wb4_master` response queue depth; bounds the transfers on the bus |
| SIDE_DEPTH | 8 | Core direction queue; at least CMD_DEPTH + RSP_DEPTH so the master sets the pipeline depth |
| CLASSIC | 0 | 0 = B4 pipelined, 1 = B4 standard (classic) mode; match the slave |
| RTY_RESP | 2'b10 | AXI response returned for a Wishbone RTY |

: Table 3.26: AXI4-Lite to Wishbone Parameters

The core alone (`axil4_to_wb4_core`) takes `ADDR_WIDTH`, `DATA_WIDTH`,
`SIDE_DEPTH` and `RTY_RESP`.

### Ports

| Port group | Direction | Description |
| --- | --- | --- |
| `s_axil_aw*`, `s_axil_w*`, `s_axil_b*` | slave | AXI4-Lite write channels (AWPROT accepted, not carried) |
| `s_axil_ar*`, `s_axil_r*` | slave | AXI4-Lite read channels |
| `m_wb_CYC/STB/WE/ADR/DAT_W/SEL` | out | Wishbone request |
| `m_wb_STALL/ACK/ERR/RTY/DAT_R` | in | Wishbone flow control and termination |
| `busy` | out | Anything buffered in the skids or a cycle open on the bus |

: Table 3.27: AXI4-Lite to Wishbone Ports

The core's ports are the five `fub_*` channels of the two slave blocks on
one side and the `cmd_*` / `rsp_*` queues of `wb4_master` on the other.

## 3.10.5 Command Formation

| AXI4-Lite | Wishbone command |
| --- | --- |
| AWADDR, WDATA, WSTRB | `we=1`, `adr`, `dat`, `sel` = WSTRB |
| ARADDR | `we=0`, `adr`, `sel` = all ones |
| AWPROT / ARPROT | not carried (Wishbone has no protection bits) |

: Table 3.28: Command Formation

A write consumes AW and W in the same clock (`fub_awready` and
`fub_wready` are the same signal), so a W beat that arrives before its AW
simply waits in its skid. A command is only issued when the side queue
has room; when the side queue is full the core stalls, which with
`SIDE_DEPTH >= CMD_DEPTH + RSP_DEPTH` never happens before the master's
own queues are full.

## 3.10.6 Response Mapping

| Wishbone status | B / R response |
| --- | --- |
| ACK | OKAY (2'b00) |
| ERR | SLVERR (2'b10) |
| RTY | `RTY_RESP` (default SLVERR) |

: Table 3.29: Response Mapping

`RDATA` is the Wishbone `DAT_R` of the termination. A response that
arrives with nothing recorded in the side queue is a master protocol
violation (`wb4_master` reports it in simulation); the core drops it so
the queue cannot wedge on it.

## 3.10.7 Timing

| Path | Clocks |
| --- | --- |
| AW+W or AR accepted at `s_axil_*` to `STB` on the bus | 2 (skid, master command queue) |
| Termination on the bus to `BVALID` / `RVALID` | 2 (master response queue, skid) |
| Sustained rate, pipelined slave | one transfer per clock per direction pair, up to `RSP_DEPTH` in flight |
| Sustained rate, `CLASSIC=1` | one transfer at a time (B4 standard mode) |

: Table 3.30: AXI4-Lite to Wishbone Timing

## 3.10.8 Formal

`formal/converters/axil4_to_wb4_core/` (sv2v flatten, then SymbiYosys)
proves on the core: a command is issued only with a request present and
carries the payload of the channel it took; B and R never fire together
and each consumes exactly one response; the response steered to B or R is
the oldest open transfer's; the open count never exceeds `SIDE_DEPTH`;
OKAY / SLVERR / `RTY_RESP` follow the status; and a write is never issued
straight after a write while a read is pending. Covers reach both
directions, the alternation, an SLVERR on B, a retry on R, and a full
side queue.

## 3.10.9 Testing

`dv/tests/test_axil4_to_wb4.py` drives `s_axil_*` with the AXI4-Lite master
BFMs and answers `m_wb_*` with the framework's Wishbone slave BFM over a
memory model (ERR and RTY windows by address) while the Wishbone monitor
checks the B4 rules on the wire. The scoreboard mirrors every OKAY write
byte-by-byte (strobed writes included) and checks every read against the
mirror, and every response code against the window its address is in.
Phases: sequential; several transfers in flight against a stalling, a
slow-terminating and a mixed slave; drain with one monitor transfer per
transaction and no violations. The classic build runs the same phases
against a classic-mode slave and returns DECERR for a retry to prove the
`RTY_RESP` path. Four RTL mutations (direction bit inverted, RTY mapped to
OKAY, write strobes dropped, read address taken from AW) all fail the test.

## 3.10.10 Usage Example

```systemverilog
axil4_to_wb4 #(
    .ADDR_WIDTH (32),
    .DATA_WIDTH (32),
    .CMD_DEPTH  (4),
    .RSP_DEPTH  (4),
    .SIDE_DEPTH (8),
    .CLASSIC    (0)
) u_axil_to_wb (
    .aclk           (clk),
    .aresetn        (rst_n),
    .s_axil_awaddr  (awaddr),  .s_axil_awprot (awprot), .s_axil_awvalid (awvalid), .s_axil_awready (awready),
    .s_axil_wdata   (wdata),   .s_axil_wstrb  (wstrb),  .s_axil_wvalid  (wvalid),  .s_axil_wready  (wready),
    .s_axil_bresp   (bresp),   .s_axil_bvalid (bvalid), .s_axil_bready  (bready),
    .s_axil_araddr  (araddr),  .s_axil_arprot (arprot), .s_axil_arvalid (arvalid), .s_axil_arready (arready),
    .s_axil_rdata   (rdata),   .s_axil_rresp  (rresp),  .s_axil_rvalid  (rvalid),  .s_axil_rready  (rready),
    .m_wb_CYC (wb_cyc), .m_wb_STB (wb_stb), .m_wb_WE (wb_we), .m_wb_ADR (wb_adr),
    .m_wb_DAT_W (wb_dat_w), .m_wb_SEL (wb_sel),
    .m_wb_STALL (wb_stall), .m_wb_ACK (wb_ack), .m_wb_ERR (wb_err), .m_wb_RTY (wb_rty),
    .m_wb_DAT_R (wb_dat_r),
    .busy ()
);
```
