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

# wb4_master

## Overview

`wb4_master` turns a command stream into Wishbone B4 **pipelined** bus cycles
and returns every termination as a response. It is the Wishbone counterpart of
`apb4_master`: the same `cmd_*`/`rsp_*` valid/ready queues on the FUB side,
each a `gaxi_skid_buffer`. There is no state machine. `STB` follows the head
of the command queue, the slave accepts a request on `STB && !STALL`, and
every `ACK`, `ERR` or `RTY` is enqueued as it arrives. Terminations arrive in
issue order (a B4 rule), so nothing is tagged.

**Protocol scope:** B4 pipelined. `RTY` is reported in `rsp_status`; the
master never retries on its own. No `CTI`/`BTE`, `LOCK` or tag signals.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | Wishbone address width |
| DATA_WIDTH | int | 32 | Wishbone data width (port size) |
| CMD_DEPTH | int | 4 | Command queue depth in **entries**, 2..8 |
| RSP_DEPTH | int | 4 | Response queue depth in **entries**, 2..8; also the maximum transfers in flight |
| SEL_WIDTH | int | DATA_WIDTH/8 | Byte-select width (derived) |

**RSP_DEPTH is the outstanding limit.** Wishbone gives a master no way to
refuse a termination, so a request is only put on the bus when its response
slot is already reserved. `RSP_DEPTH` therefore bounds both the queue and the
pipeline depth; 4 sustains one transfer per clock against a slave with up to
four clocks of termination latency.

## Ports

```systemverilog
module wb4_master
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int CMD_DEPTH  = 4,
    parameter int RSP_DEPTH  = 4,
    parameter int SEL_WIDTH  = DATA_WIDTH / 8,
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

    // Wishbone B4 pipelined master
    output logic              m_wb_CYC,
    output logic              m_wb_STB,
    output logic              m_wb_WE,
    output logic [AW-1:0]     m_wb_ADR,
    output logic [DW-1:0]     m_wb_DAT_W,
    output logic [SW-1:0]     m_wb_SEL,
    input  logic              m_wb_STALL,
    input  logic              m_wb_ACK,
    input  logic              m_wb_ERR,
    input  logic              m_wb_RTY,
    input  logic [DW-1:0]     m_wb_DAT_R,

    // Command queue (FUB -> bus)
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_we,
    input  logic [AW-1:0]     cmd_adr,
    input  logic [DW-1:0]     cmd_dat,
    input  logic [SW-1:0]     cmd_sel,

    // Response queue (bus -> FUB)
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [STW-1:0]    rsp_status,
    output logic [DW-1:0]     rsp_dat
);
```

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| clk | 1 | Input | Bus clock |
| aresetn | 1 | Input | Active-low asynchronous reset (invert Wishbone `RST_I` at the boundary) |

### Wishbone Master Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_wb_CYC | 1 | Output | Cycle: high from the first `STB` until the last outstanding transfer terminates |
| m_wb_STB | 1 | Output | Strobe: a request is presented |
| m_wb_WE | 1 | Output | Write enable |
| m_wb_ADR | ADDR_WIDTH | Output | Address |
| m_wb_DAT_W | DATA_WIDTH | Output | Write data (`DAT_O` in the specification) |
| m_wb_SEL | SEL_WIDTH | Output | Byte select, reads and writes |
| m_wb_STALL | 1 | Input | Slave cannot accept this clock; the request is held |
| m_wb_ACK | 1 | Input | Normal termination |
| m_wb_ERR | 1 | Input | Error termination |
| m_wb_RTY | 1 | Input | Retry termination |
| m_wb_DAT_R | DATA_WIDTH | Input | Read data (`DAT_I`) |

### Command Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cmd_valid | 1 | Input | Command valid |
| cmd_ready | 1 | Output | Command queue has room |
| cmd_we | 1 | Input | Write (1) or read (0) |
| cmd_adr | ADDR_WIDTH | Input | Address |
| cmd_dat | DATA_WIDTH | Input | Write data |
| cmd_sel | SEL_WIDTH | Input | Byte select |

### Response Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| rsp_valid | 1 | Output | Response valid |
| rsp_ready | 1 | Input | FUB takes the response |
| rsp_status | 2 | Output | `WB4_RSP_ACK` (0), `WB4_RSP_ERR` (1), `WB4_RSP_RTY` (2) |
| rsp_dat | DATA_WIDTH | Output | Read data (undefined for writes, ERR and RTY) |

## Functional Description

Two counters and three wires replace the FSM an APB master needs:

```
issue    = cmd head valid && r_reserved < RSP_DEPTH
STB      = issue
CYC      = issue || r_inflight != 0
accept   = STB && !STALL          -> pop command, r_inflight++, r_reserved++
term     = CYC && (ACK|ERR|RTY)   -> push {status, DAT_R}, r_inflight--
rsp pop  = rsp_valid && rsp_ready -> r_reserved--
```

`r_inflight` counts transfers the slave has accepted but not terminated;
`r_reserved` counts everything issued that the FUB has not yet taken off the
response queue, which is exactly what can occupy that queue in the worst
case. Reserving at issue rather than reading the queue's count back avoids
the "count is stale by one" reasoning the APB master's back-to-back path
needs.

`ERR` and `RTY` are mutually exclusive in the specification. If a slave
asserts both, `ERR` wins, so a broken slave reads as an error rather than a
retry.

### Timing

| Path | Clocks |
|---|---|
| `cmd_valid` accepted to `STB` | 1 (command skid) |
| `ACK`/`ERR`/`RTY` to `rsp_valid` | 1 (response skid) |
| Sustained throughput | one request and one termination per clock |

A stalled request is held unchanged until accepted: the command skid's head
does not move until `STB && !STALL`.

## Usage Example

```systemverilog
wb4_master #(
    .ADDR_WIDTH (32),
    .DATA_WIDTH (32),
    .CMD_DEPTH  (4),
    .RSP_DEPTH  (4)
) u_wb_master (
    .clk        (clk),
    .aresetn    (aresetn),
    .m_wb_CYC   (wb_cyc),   .m_wb_STB   (wb_stb),
    .m_wb_WE    (wb_we),    .m_wb_ADR   (wb_adr),
    .m_wb_DAT_W (wb_dat_o), .m_wb_SEL   (wb_sel),
    .m_wb_STALL (wb_stall), .m_wb_ACK   (wb_ack),
    .m_wb_ERR   (wb_err),   .m_wb_RTY   (wb_rty),
    .m_wb_DAT_R (wb_dat_i),
    .cmd_valid  (cmd_valid), .cmd_ready (cmd_ready),
    .cmd_we     (cmd_we),    .cmd_adr   (cmd_adr),
    .cmd_dat    (cmd_dat),   .cmd_sel   (cmd_sel),
    .rsp_valid  (rsp_valid), .rsp_ready (rsp_ready),
    .rsp_status (rsp_status),.rsp_dat   (rsp_dat)
);
```

## Notes

- A termination that arrives with nothing in flight is a slave protocol
  violation. It is still enqueued (the FUB sees it) and reported in
  simulation.
- Under `ifdef FORMAL` the block asserts: `STB` implies `CYC`; `CYC` covers
  every in-flight transfer; a stalled request is held stable; the credit
  invariant `r_reserved <= RSP_DEPTH`; and that every termination found
  queue space.

## Related

- [wb4_slave](wb4_slave.md) - the mirror image
- [apb4_master](../apb4/apb4_master.md) - the same FUB-side contract over APB
- [gaxi_skid_buffer](../gaxi/gaxi_skid_buffer.md) - both queues

## Test

`val/amba/test_wb4_master_slave_loop.py` (master and slave back to back, see
the [family README](README.md)). Formal: `formal/amba/wb4_master/`.
