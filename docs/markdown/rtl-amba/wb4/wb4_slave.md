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

# wb4_slave

## Overview

`wb4_slave` accepts Wishbone B4 **pipelined** transfers one per clock and
presents each on a command queue; it terminates them, in order, from a
response queue with a registered `ACK`, `ERR` or `RTY` and read data. It is
the Wishbone counterpart of `apb4_slave`, with the same `cmd_*`/`rsp_*`
valid/ready contract on the FUB side. There is no state machine: `STALL` is
the inverse of "can accept", and the termination side is one counter and one
register.

**Protocol scope:** B4 pipelined. The FUB chooses the termination through
`rsp_status`, so a FUB can answer `RTY` without the slave knowing why.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | Wishbone address width |
| DATA_WIDTH | int | 32 | Wishbone data width (port size) |
| CMD_DEPTH | int | 2 | Command queue depth in **entries**, 2..8 |
| RSP_DEPTH | int | 2 | Response queue depth in **entries**, 2..8 |
| MAX_OUTSTANDING | int | 16 | Transfers accepted but not yet terminated before `STALL` asserts |
| CLASSIC | int | 0 | 0 = B4 pipelined; 1 = B4 standard ("classic") mode, see the [family README](README.md). Match the peer: the modes do not mix |
| SEL_WIDTH | int | DATA_WIDTH/8 | Byte-select width (derived) |

`MAX_OUTSTANDING` bounds the FUB's in-order pipeline, not the master's: a
master's own limit is its response queue. Set it to at least the number of
commands the FUB can hold before it produces the first response, or the bus
stalls short of the FUB's throughput.

## Ports

```systemverilog
module wb4_slave
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int CMD_DEPTH       = 2,
    parameter int RSP_DEPTH       = 2,
    parameter int MAX_OUTSTANDING = 16,
    parameter int CLASSIC         = 0,
    parameter int SEL_WIDTH       = DATA_WIDTH / 8,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = SEL_WIDTH,
    parameter int STW = WB4_STATUS_WIDTH,
    parameter int CPW = 1 + AW + DW + SW,   // command packet: {we, adr, dat, sel}
    parameter int RPW = STW + DW            // response packet: {status, dat}
) (
    input  logic              clk,
    input  logic              aresetn,

    // Wishbone B4 pipelined slave
    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [AW-1:0]     s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [SW-1:0]     s_wb_SEL,
    output logic              s_wb_STALL,
    output logic              s_wb_ACK,
    output logic              s_wb_ERR,
    output logic              s_wb_RTY,
    output logic [DW-1:0]     s_wb_DAT_R,

    // Command queue (bus -> FUB)
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_we,
    output logic [AW-1:0]     cmd_adr,
    output logic [DW-1:0]     cmd_dat,
    output logic [SW-1:0]     cmd_sel,

    // Response queue (FUB -> bus)
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [STW-1:0]    rsp_status,
    input  logic [DW-1:0]     rsp_dat
);
```

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| clk | 1 | Input | Bus clock |
| aresetn | 1 | Input | Active-low asynchronous reset |

### Wishbone Slave Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_wb_CYC | 1 | Input | Cycle |
| s_wb_STB | 1 | Input | Strobe: a request is presented |
| s_wb_WE | 1 | Input | Write enable |
| s_wb_ADR | ADDR_WIDTH | Input | Address |
| s_wb_DAT_W | DATA_WIDTH | Input | Write data (`DAT_I` at the slave) |
| s_wb_SEL | SEL_WIDTH | Input | Byte select |
| s_wb_STALL | 1 | Output | Cannot accept this clock; combinational from queue room and the outstanding count, never from `STB` |
| s_wb_ACK | 1 | Output | Normal termination (registered, one clock) |
| s_wb_ERR | 1 | Output | Error termination (registered, one clock) |
| s_wb_RTY | 1 | Output | Retry termination (registered, one clock) |
| s_wb_DAT_R | DATA_WIDTH | Output | Read data (`DAT_O` at the slave); holds between terminations |

### Command Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cmd_valid | 1 | Output | Command valid |
| cmd_ready | 1 | Input | FUB takes the command |
| cmd_we | 1 | Output | Write (1) or read (0) |
| cmd_adr | ADDR_WIDTH | Output | Address |
| cmd_dat | DATA_WIDTH | Output | Write data |
| cmd_sel | SEL_WIDTH | Output | Byte select |

### Response Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| rsp_valid | 1 | Input | Response valid |
| rsp_ready | 1 | Output | Response queue has room |
| rsp_status | 2 | Input | `WB4_RSP_ACK` (0), `WB4_RSP_ERR` (1), `WB4_RSP_RTY` (2) |
| rsp_dat | DATA_WIDTH | Input | Read data |

## Functional Description

```
STALL  = !cmd queue room || r_outstanding == MAX_OUTSTANDING
accept = CYC && STB && !STALL     -> push {we, adr, dat, sel}, r_outstanding++
term   = rsp head valid && r_outstanding != 0 && CYC
         -> register ACK|ERR|RTY from status, DAT_R, pop, r_outstanding--
orphan = rsp head valid && (r_outstanding == 0 || r_abandoned != 0) -> pop and drop
abort  = !CYC && r_outstanding != 0 -> r_abandoned += r_outstanding, r_outstanding <= 0
```

**Classic mode** (`CLASSIC=1`): `STALL` is driven low; a request is
accepted when nothing is outstanding and no termination is on the wire
this clock, so a held presentation is taken exactly once; `MAX_OUTSTANDING`
is effectively 1.

**Orphan guard.** A response with nothing outstanding cannot belong to any
transfer (a duplicate from the FUB, or a response to a transfer the master
abandoned). It is dropped, and reported in simulation. Left in the queue it
would terminate the *next* transfer and every later response would be off by
one: the positional mis-pairing `apb4_slave`'s guard exists for.

**Abort.** A master that drops `CYC` with transfers outstanding has ended the
cycle. The outstanding count moves to an *abandoned* count, and that many
later responses from the FUB are dropped as they arrive, even if the master
has started a new cycle by then. Without that, a late response for an
abandoned transfer would terminate the new cycle's first transfer, which is
exactly what the slave test's abort phase caught before the count existed.
Terminations are only ever driven inside a cycle, and never while a
response is still owed to an abandoned transfer.

### Timing

| Path | Clocks |
|---|---|
| `STB` accepted to `cmd_valid` | 1 (command skid) |
| `rsp_valid` to `ACK`/`ERR`/`RTY` | 2 (response skid, then the output register) |
| Sustained throughput | one accept and one termination per clock |

## Usage Example

```systemverilog
wb4_slave #(
    .ADDR_WIDTH      (32),
    .DATA_WIDTH      (32),
    .CMD_DEPTH       (2),
    .RSP_DEPTH       (2),
    .MAX_OUTSTANDING (16)
) u_wb_slave (
    .clk        (clk),
    .aresetn    (aresetn),
    .s_wb_CYC   (wb_cyc),   .s_wb_STB   (wb_stb),
    .s_wb_WE    (wb_we),    .s_wb_ADR   (wb_adr),
    .s_wb_DAT_W (wb_dat_i), .s_wb_SEL   (wb_sel),
    .s_wb_STALL (wb_stall), .s_wb_ACK   (wb_ack),
    .s_wb_ERR   (wb_err),   .s_wb_RTY   (wb_rty),
    .s_wb_DAT_R (wb_dat_o),
    .cmd_valid  (cmd_valid), .cmd_ready (cmd_ready),
    .cmd_we     (cmd_we),    .cmd_adr   (cmd_adr),
    .cmd_dat    (cmd_dat),   .cmd_sel   (cmd_sel),
    .rsp_valid  (rsp_valid), .rsp_ready (rsp_ready),
    .rsp_status (rsp_status),.rsp_dat   (rsp_dat)
);
```

## Notes

- The FUB must answer commands in the order it received them; the slave
  pairs responses to transfers by position.
- Under `ifdef FORMAL` the block asserts: at most one of `ACK`/`ERR`/`RTY`
  per clock; a termination only for a transfer that was outstanding inside
  a cycle; `r_outstanding <= MAX_OUTSTANDING`; and that every accept found
  queue room.

## Related

- [wb4_master](wb4_master.md) - the mirror image
- [apb4_slave](../apb4/apb4_slave.md) - the same FUB-side contract over APB
- [gaxi_skid_buffer](../gaxi/gaxi_skid_buffer.md) - both queues

## Test

`val/amba/test_wb4_slave.py` drives the block alone against the framework's Wishbone
BFMs (`CocoTBFramework.components.wb4`), with the GAXI BFMs on the queues;
`val/amba/test_wb4_master_slave_loop.py` runs it back to back with its
counterpart. See the [family README](README.md). Formal:
`formal/amba/wb4_slave/`.
