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

# 3.5 PeakRDL Adapter

The **peakrdl_to_cmdrsp** module drives a PeakRDL-generated register block from a command/response stream. Data flows cmd/rsp -> PeakRDL: `cmd_*` are inputs and `regblk_*` request signals are outputs, with the register block's acks and read data coming back in. Fair warning — the name reads in the opposite order to the dataflow. The ports below are authoritative.

## Overview

PeakRDL generates register blocks with a selectable cpuif, and this adapter mates with the **passthrough** cpuif (`regblk_req` / `req_is_wr` / `wr_biten` / stall / ack / err — NOT the APB cpuif's PSEL/PENABLE pins, so if you came here looking for PSEL, back up). It:

1. Decouples the register interface from the implementation
2. Provides a clean handshake protocol
3. Enables pipelined register access
4. Supports custom control logic integration

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 12 | Address width (register-block sized) |
| DATA_WIDTH | int | 32 | Data width |

: Table 3.20: PeakRDL Adapter Parameters

## Ports

The full port list, straight from the RTL:

```systemverilog
module peakrdl_to_cmdrsp #(
    parameter int ADDR_WIDTH = 12,  // Address width for cmd/rsp interface
    parameter int DATA_WIDTH = 32   // Must match PeakRDL generation (typically 32)
) (
    // Clock and Reset
    input  logic                    aclk,
    input  logic                    aresetn,

    // =========================================================================
    // CMD/RSP Interface (rtldesignsherpa standard)
    // =========================================================================
    // Command Channel
    input  logic                    cmd_valid,
    output logic                    cmd_ready,
    input  logic                    cmd_pwrite,         // 1=write, 0=read
    input  logic [ADDR_WIDTH-1:0]   cmd_paddr,          // Byte address
    input  logic [DATA_WIDTH-1:0]   cmd_pwdata,         // Write data
    input  logic [DATA_WIDTH/8-1:0] cmd_pstrb,          // Byte strobes

    // Response Channel
    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic [DATA_WIDTH-1:0]   rsp_prdata,         // Read data
    output logic                    rsp_pslverr,        // Error flag

    // =========================================================================
    // PeakRDL Passthrough Interface
    // =========================================================================
    output logic                    regblk_req,         // Request -- HELD until ack
    output logic                    regblk_req_is_wr,   // Write flag
    output logic [ADDR_WIDTH-1:0]   regblk_addr,        // Address
    output logic [DATA_WIDTH-1:0]   regblk_wr_data,     // Write data
    output logic [DATA_WIDTH-1:0]   regblk_wr_biten,    // Write bit enables
    input  logic                    regblk_req_stall_wr, // Write stall
    input  logic                    regblk_req_stall_rd, // Read stall
    input  logic                    regblk_rd_ack,      // Read acknowledge
    input  logic                    regblk_rd_err,      // Read error
    input  logic [DATA_WIDTH-1:0]   regblk_rd_data,     // Read data
    input  logic                    regblk_wr_ack,      // Write acknowledge
    input  logic                    regblk_wr_err       // Write error
);
```

## Functional Description

Direction: cmd/rsp -> PeakRDL. `cmd_*` arrive from upstream (e.g. the APB shim's packet stream); the adapter drives the register block's `regblk_*` request signals and returns its acks as rsp packets.

### Write

```
Cycle 0: cmd_valid, cmd_pwrite=1 accepted (cmd_ready high in CMD_IDLE);
         regblk_req driven the same cycle, strobes converted to bit
         enables
Cycle N: regblk_wr_ack -> rsp queued (RSP_VALID), pslverr from
         regblk_wr_err
         (if regblk_req_stall_wr: state parks in CMD_STALLED and
         retries when the stall clears)
Cycle M: rsp_valid && rsp_ready -> back to idle

`regblk_req` is HELD asserted from acceptance through the ack cycle
(`(cmd_state == CMD_WAIT_ACK) || (CMD_IDLE && cmd_valid)`) -- it is
not a one-cycle strobe. The generated passthrough regblock samples the
request level and needs the hold; a consumer that starts a new access
every cycle req is high would double-fire non-idempotent registers
(TASK-064 records the earlier strobe mis-documentation).
```

### Read

Same shape via `regblk_rd_ack`/`regblk_rd_data`/`regblk_rd_err`, with
`rsp_prdata` carried in the response.

### 3.5.5 Implementation

Two small FSMs do all the work, from the RTL:

```systemverilog
typedef enum logic [1:0] {
    CMD_IDLE     = 2'b00,   // ready to accept a command
    CMD_WAIT_ACK = 2'b01,   // register block has the request
    CMD_STALLED  = 2'b10    // req_stall_* asserted; retry
} cmd_state_t;

typedef enum logic {
    RSP_IDLE  = 1'b0,
    RSP_VALID = 1'b1        // response held until rsp_ready
} rsp_state_t;
```

The command is registered on acceptance so the request can be replayed
out of CMD_STALLED; in CMD_IDLE the request muxes straight from the
live cmd inputs, so an unstalled single-cycle ack costs no extra
latency. `cmd_ready = (cmd_state == CMD_IDLE)` gives one outstanding
command, which is what a register block wants.

### 3.5.6 Resource Utilization

```
FSM state:            3 regs (cmd_state 2b + rsp_state 1b)
Command capture:      77 regs (pwrite 1 + paddr 12 + pwdata 32 + wr_biten 32)
Response capture:     33 regs (prdata 32 + pslverr 1)
Request replay muxes: ~77 LUTs (four 2:1 selects, 1+12+32+32 bits --
                      IDLE-vs-registered request presentation)
FSM + control decode: ~25 LUTs

Total: ~113 regs, ~100 LUTs  (counted from the declarations at the
documented defaults ADDR_WIDTH=12, DATA_WIDTH=32; all of it is live
state -- the command capture replays the request out of
CMD_STALLED/CMD_WAIT_ACK, and the response capture holds the rsp packet)
```

## Waveforms

### Figure 3.8: PeakRDL Adapter

![PeakRDL Adapter](../assets/mermaid/peakrdl_adapter.png)

## Usage Example

### 3.5.7 Use Cases

The adapter sits between a command/response packet stream and a
PeakRDL-generated register block:

```systemverilog
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH (12),
    .DATA_WIDTH (32)
) u_adapter (
    .aclk                (aclk),
    .aresetn             (aresetn),

    // command/response stream (e.g. from apb4_slave_cdc's unpacker)
    .cmd_valid           (cmd_valid),
    .cmd_ready           (cmd_ready),
    .cmd_pwrite          (cmd_pwrite),
    .cmd_paddr           (cmd_paddr),
    .cmd_pwdata          (cmd_pwdata),
    .cmd_pstrb           (cmd_pstrb),
    .rsp_valid           (rsp_valid),
    .rsp_ready           (rsp_ready),
    .rsp_prdata          (rsp_prdata),
    .rsp_pslverr         (rsp_pslverr),

    // PeakRDL register block hookup
    .regblk_req          (hwif_req),
    .regblk_req_is_wr    (hwif_req_is_wr),
    .regblk_addr         (hwif_addr),
    .regblk_wr_data      (hwif_wr_data),
    .regblk_wr_biten     (hwif_wr_biten),
    .regblk_req_stall_wr (hwif_req_stall_wr),
    .regblk_req_stall_rd (hwif_req_stall_rd),
    .regblk_rd_ack       (hwif_rd_ack),
    .regblk_rd_err       (hwif_rd_err),
    .regblk_rd_data      (hwif_rd_data),
    .regblk_wr_ack       (hwif_wr_ack),
    .regblk_wr_err       (hwif_wr_err)
);
```

Typical deployments: CSR blocks behind the APB shim (see 3.4), or any
fabric whose endpoint speaks the cmd/rsp packet convention.

### 3.5.8 Integration Example

The flow a real deployment uses (CSRs behind the APB shim):

```
AXI4 master → axi4_to_apb4_shim → APB bus → apb4_to_peakrdl
                                              ├─ apb4_slave_cdc  (APB -> cmd/rsp)
                                              └─ peakrdl_to_cmdrsp
                                                        │
                                              regblk_* request/ack
                                                        ↓
                                          PeakRDL-generated register block
```

The shim's own cmd/rsp stream is internal — its external pins are APB.
The block that turns a bus back into the cmd/rsp surface this adapter
consumes is `apb4_to_peakrdl` (which wraps `apb4_slave_cdc` +
`peakrdl_to_cmdrsp`); wire the adapter directly only when your fabric
already speaks cmd/rsp packets.

The wiring is exactly the instantiation in 3.5.7; the earlier example
here showed the adapter hanging off a register block's APB port through
`reg_*` signals that do not exist — the reversed-direction reading this
page used to make.

## 3.5.9 APB4 Front End (apb4_to_peakrdl)

`peakrdl_to_cmdrsp` above takes a cmd/rsp stream. `apb4_to_peakrdl` is the
module that produces one from an APB4 slave port, and it crosses clock domains
while doing it -- APB on `pclk`, the register block on `aclk`. It is a
two-stage composition and adds no register logic of its own:

| Stage | Module | Domain |
|-------|--------|--------|
| 1 | `apb4_slave_cdc` | `pclk` in, `aclk` out |
| 2 | `peakrdl_to_cmdrsp` | `aclk` |

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `ADDR_WIDTH` | int | 12 | APB and cpuif byte address width |
| `DATA_WIDTH` | int | 32 | Must match the PeakRDL generation |
| `PROT_WIDTH` | int | 3 | `PPROT` width |
| `STRB_WIDTH` | int | DATA_WIDTH/8 | Derived; do not override |
| `CDC_DEPTH` | int | 2 | Command/response CDC FIFO depth (>= 2) |
| `USE_JOHNSON` | int | 0 | CDC pointer encoding: 0 = Gray (power-of-2 depth only), 1 = Johnson (any depth) |
| `USE_2_PHASE_CDC` | bit | 1 | **Deprecated and ignored.** Accepted for compatibility; `apb4_slave_cdc` does not reference it, so setting it changes nothing |

: apb4_to_peakrdl Parameters

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `aclk` | 1 | Input | Register-block clock; drives the cpuif master |
| `aresetn` | 1 | Input | Active-low reset, `aclk` domain |
| `pclk` | 1 | Input | APB clock |
| `presetn` | 1 | Input | Active-low reset, `pclk` domain |
| `s_apb_PSEL` | 1 | Input | APB select |
| `s_apb_PENABLE` | 1 | Input | APB enable |
| `s_apb_PREADY` | 1 | Output | APB ready |
| `s_apb_PADDR` | ADDR_WIDTH | Input | APB address |
| `s_apb_PWRITE` | 1 | Input | Write/read direction |
| `s_apb_PWDATA` | DATA_WIDTH | Input | Write data |
| `s_apb_PSTRB` | STRB_WIDTH | Input | Write strobes |
| `s_apb_PPROT` | PROT_WIDTH | Input | Protection attributes |
| `s_apb_PRDATA` | DATA_WIDTH | Output | Read data |
| `s_apb_PSLVERR` | 1 | Output | Slave error |
| `cpuif_req` | 1 | Output | Passthrough request |
| `cpuif_req_is_wr` | 1 | Output | Request is a write |
| `cpuif_addr` | ADDR_WIDTH | Output | Request address |
| `cpuif_wr_data` | DATA_WIDTH | Output | Write data |
| `cpuif_wr_biten` | DATA_WIDTH | Output | Per-bit write enables, expanded from `PSTRB` |
| `cpuif_req_stall_wr` | 1 | Input | Register block stalls a write |
| `cpuif_req_stall_rd` | 1 | Input | Register block stalls a read |
| `cpuif_rd_ack` | 1 | Input | Read acknowledge |
| `cpuif_rd_err` | 1 | Input | Read error, returned as `PSLVERR` |
| `cpuif_rd_data` | DATA_WIDTH | Input | Read data |
| `cpuif_wr_ack` | 1 | Input | Write acknowledge |
| `cpuif_wr_err` | 1 | Input | Write error, returned as `PSLVERR` |

: apb4_to_peakrdl Ports
