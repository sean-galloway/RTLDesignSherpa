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

# APB5 Slave

**Module:** `apb5_slave.sv`
**Location:** `rtl/amba/apb5/`
**Status:** Production Ready

---

## Overview

The APB5 Slave module implements a complete AMBA APB5 slave interface with all APB5 extensions. It receives APB transactions from the bus and provides a command/response interface for backend logic, supporting user-defined signals, wake-up generation, and optional parity.

### Key Features

- Full AMBA APB5 protocol compliance
- Receives PAUSER/PWUSER from master
- Generates PRUSER/PBUSER responses
- PWAKEUP output for wake-up signaling
- Optional parity support for data integrity
- Command/response FIFO buffering
- Configurable buffer depth

---

## Module Architecture

```mermaid
flowchart LR
    subgraph APB5["APB5 Slave Interface"]
        psel["PSEL"]
        pen["PENABLE"]
        paddr["PADDR"]
        pwrite["PWRITE"]
        pwdata["PWDATA"]
        pstrb["PSTRB"]
        pprot["PPROT"]
        pauser["PAUSER"]
        pwuser["PWUSER"]
        pready["PREADY"]
        prdata["PRDATA"]
        pslverr["PSLVERR"]
        pwakeup["PWAKEUP"]
        pruser["PRUSER"]
        pbuser["PBUSER"]
    end

    subgraph CTRL["Control Logic"]
        fsm["APB5<br/>FSM"]
        buf["Skid<br/>Buffer"]
    end

    subgraph CMD["Command Interface"]
        cv["cmd_valid"]
        cr["cmd_ready"]
        cd["cmd_data"]
    end

    subgraph RSP["Response Interface"]
        rv["rsp_valid"]
        rr["rsp_ready"]
        rd["rsp_data"]
    end

    psel --> fsm
    pen --> fsm
    paddr --> buf
    pwrite --> buf
    pwdata --> buf
    pstrb --> buf
    pprot --> buf
    pauser --> buf
    pwuser --> buf

    fsm --> pready
    buf --> cv
    buf --> cd
    cr --> buf

    rv --> fsm
    rd --> prdata
    rd --> pslverr
    rd --> pruser
    rd --> pbuser
    rr --> fsm

    fsm --> pwakeup
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | APB address bus width |
| DATA_WIDTH | int | 32 | APB data bus width |
| PROT_WIDTH | int | 3 | Protection signal width |
| AUSER_WIDTH | int | 4 | Address/request user signal width |
| WUSER_WIDTH | int | 4 | Write data user signal width |
| RUSER_WIDTH | int | 4 | Read data user signal width |
| BUSER_WIDTH | int | 4 | Response user signal width |
| DEPTH | int | 2 | Skid-buffer depth in entries; must be one of {2, 4, 6, 8} |
| ENABLE_PARITY | bit | 0 | Enable parity generation and checking |
| STRB_WIDTH | int | DATA_WIDTH/8 | Write strobe width (calculated) |

`DEPTH` sets both the command and the response `gaxi_skid_buffer` depth. It is a
literal entry count, not a log2 exponent.

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| pclk | 1 | Input | APB clock |
| presetn | 1 | Input | APB active-low reset |

### APB5 Slave Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_apb_PSEL | 1 | Input | APB select signal |
| s_apb_PENABLE | 1 | Input | APB enable signal |
| s_apb_PREADY | 1 | Output | Slave ready response |
| s_apb_PADDR | ADDR_WIDTH | Input | APB address |
| s_apb_PWRITE | 1 | Input | Write/read indicator |
| s_apb_PWDATA | DATA_WIDTH | Input | Write data |
| s_apb_PSTRB | STRB_WIDTH | Input | Write byte strobes |
| s_apb_PPROT | PROT_WIDTH | Input | Protection attributes |
| s_apb_PAUSER | AUSER_WIDTH | Input | User-defined request attributes |
| s_apb_PWUSER | WUSER_WIDTH | Input | User-defined write data attributes |
| s_apb_PRDATA | DATA_WIDTH | Output | Read data to master |
| s_apb_PSLVERR | 1 | Output | Slave error response |
| s_apb_PWAKEUP | 1 | Output | Wake-up signal to master |
| s_apb_PRUSER | RUSER_WIDTH | Output | User-defined read data attributes |
| s_apb_PBUSER | BUSER_WIDTH | Output | User-defined response attributes |

### Parity Signals (Optional)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_apb_PWDATAPARITY | STRB_WIDTH | Input | Write data parity from master |
| s_apb_PADDRPARITY | 1 | Input | Address parity from master |
| s_apb_PCTRLPARITY | 1 | Input | Control signals parity from master |
| s_apb_PRDATAPARITY | STRB_WIDTH | Output | Read data parity to master |
| s_apb_PREADYPARITY | 1 | Output | PREADY parity to master |
| s_apb_PSLVERRPARITY | 1 | Output | PSLVERR parity to master |

### Command Interface (to backend)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cmd_valid | 1 | Output | Command valid to backend |
| cmd_ready | 1 | Input | Backend ready |
| cmd_pwrite | 1 | Output | Command write/read |
| cmd_paddr | ADDR_WIDTH | Output | Command address |
| cmd_pwdata | DATA_WIDTH | Output | Command write data |
| cmd_pstrb | STRB_WIDTH | Output | Command write strobes |
| cmd_pprot | PROT_WIDTH | Output | Command protection |
| cmd_pauser | AUSER_WIDTH | Output | Command address user |
| cmd_pwuser | WUSER_WIDTH | Output | Command write user |

### Response Interface (from backend)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| rsp_valid | 1 | Input | Response valid from backend |
| rsp_ready | 1 | Output | Slave ready for response |
| rsp_prdata | DATA_WIDTH | Input | Response read data |
| rsp_pslverr | 1 | Input | Response error status |
| rsp_pruser | RUSER_WIDTH | Input | Response read user |
| rsp_pbuser | BUSER_WIDTH | Input | Response user |

### Wake-up Control

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| wakeup_request | 1 | Input | Wake-up request from backend; registered onto `s_apb_PWAKEUP` |

### Status Outputs

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| parity_error_wdata | 1 | Output | Write-data parity mismatch (tied to 0 when ENABLE_PARITY=0) |
| parity_error_ctrl | 1 | Output | Address or control parity mismatch (tied to 0 when ENABLE_PARITY=0) |

---

## Functionality

### APB5 Slave Protocol

The slave responds to APB transactions with proper timing:

1. **SETUP Phase**: PSEL=1, PENABLE=0 - Capture address and control
2. **ACCESS Phase**: PSEL=1, PENABLE=1 - Assert PREADY when response ready

### Response Timing

```mermaid
sequenceDiagram
    participant M as APB Master
    participant S as APB5 Slave
    participant B as Backend

    M->>S: PSEL=1, PADDR, PWRITE, PAUSER
    Note over S: SETUP phase
    M->>S: PENABLE=1
    Note over S: ACCESS phase
    S->>B: cmd_valid, cmd_data
    B->>S: rsp_valid, rsp_data
    S->>M: PREADY=1, PRDATA, PRUSER, PBUSER
```

---

## Timing Diagrams

### Write Transaction with Wait States

<!-- TODO: Add wavedrom timing diagram for APB5 slave write with wait states -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - PCLK
> - PSEL
> - PENABLE
> - PADDR
> - PWRITE (high)
> - PWDATA
> - PAUSER, PWUSER
> - PREADY (with wait states)
> - PSLVERR
> - PBUSER


### Read Transaction

<!-- TODO: Add wavedrom timing diagram for APB5 slave read -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - PCLK
> - PSEL
> - PENABLE
> - PADDR
> - PWRITE (low)
> - PAUSER
> - PREADY
> - PRDATA
> - PRUSER, PBUSER


### Wake-up Signaling

<!-- TODO: Add wavedrom timing diagram for wake-up -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - PCLK
> - wakeup_request (from backend)
> - PWAKEUP (to master)
> - Timing relationship


---

## Usage Example

```systemverilog
apb5_slave #(
    .ADDR_WIDTH     (32),
    .DATA_WIDTH     (32),
    .AUSER_WIDTH    (4),
    .WUSER_WIDTH    (4),
    .RUSER_WIDTH    (4),
    .BUSER_WIDTH    (4),
    .DEPTH          (2),
    .ENABLE_PARITY  (0)
) u_apb5_slave (
    .pclk           (apb_clk),
    .presetn        (apb_rst_n),

    // APB5 slave interface
    .s_apb_PSEL     (s_apb_psel),
    .s_apb_PENABLE  (s_apb_penable),
    .s_apb_PREADY   (s_apb_pready),
    .s_apb_PADDR    (s_apb_paddr),
    .s_apb_PWRITE   (s_apb_pwrite),
    .s_apb_PWDATA   (s_apb_pwdata),
    .s_apb_PSTRB    (s_apb_pstrb),
    .s_apb_PPROT    (s_apb_pprot),
    .s_apb_PAUSER   (s_apb_pauser),
    .s_apb_PWUSER   (s_apb_pwuser),
    .s_apb_PRDATA   (s_apb_prdata),
    .s_apb_PSLVERR  (s_apb_pslverr),
    .s_apb_PWAKEUP  (s_apb_pwakeup),
    .s_apb_PRUSER   (s_apb_pruser),
    .s_apb_PBUSER   (s_apb_pbuser),

    // Backend command interface
    .cmd_valid      (backend_cmd_valid),
    .cmd_ready      (backend_cmd_ready),
    .cmd_pwrite     (backend_cmd_write),
    .cmd_paddr      (backend_cmd_addr),
    .cmd_pwdata     (backend_cmd_wdata),
    .cmd_pstrb      (backend_cmd_strb),
    .cmd_pprot      (backend_cmd_prot),
    .cmd_pauser     (backend_cmd_auser),
    .cmd_pwuser     (backend_cmd_wuser),

    // Backend response interface
    .rsp_valid      (backend_rsp_valid),
    .rsp_ready      (backend_rsp_ready),
    .rsp_prdata     (backend_rsp_rdata),
    .rsp_pslverr    (backend_rsp_error),
    .rsp_pruser     (backend_rsp_ruser),
    .rsp_pbuser     (backend_rsp_buser),

    // Wake-up
    .wakeup_request (backend_wakeup),

    // Parity interface (unused here because ENABLE_PARITY=0)
    .s_apb_PWDATAPARITY  ('0),
    .s_apb_PADDRPARITY   (1'b0),
    .s_apb_PCTRLPARITY   (1'b0),
    .s_apb_PRDATAPARITY  (),
    .s_apb_PREADYPARITY  (),
    .s_apb_PSLVERRPARITY (),
    .parity_error_wdata  (),
    .parity_error_ctrl   ()
);
```

---

## Design Notes

### Backpressure Handling

- If backend cannot accept commands (`cmd_ready=0`), slave inserts wait states
- PREADY held low until backend accepts command and provides response

### User Signal Propagation

- PAUSER/PWUSER captured during SETUP phase, forwarded to backend
- PRUSER/PBUSER from backend driven during ACCESS phase response

### Wake-up Generation

`wakeup_request` is registered once before it drives `s_apb_PWAKEUP`, giving a
single-cycle delay from request to assertion. The slave does not qualify
PWAKEUP with bus state -- it simply mirrors the (registered) backend request.

### Parity Implementation

When `ENABLE_PARITY=1` the slave checks the parity the master supplies and
generates parity for its own outputs:

| Parity signal | Direction | Covers | Granularity |
|---------------|-----------|--------|-------------|
| s_apb_PWDATAPARITY[i] | Checked | PWDATA byte lane `i` | One bit per byte (STRB_WIDTH bits total) |
| s_apb_PADDRPARITY | Checked | Whole PADDR | One bit for the entire address |
| s_apb_PCTRLPARITY | Checked | {PWRITE, PSTRB, PPROT} concatenated | One bit for the whole control group |
| s_apb_PRDATAPARITY[i] | Generated | PRDATA byte lane `i` | One bit per byte |
| s_apb_PREADYPARITY | Generated | PREADY | One bit |
| s_apb_PSLVERRPARITY | Generated | PSLVERR | One bit |

Each parity bit is the XOR reduction of the covered signals, so it is 1 when the
covered field contains an odd number of ones (an even-parity encoding). Per-byte
data parity detects one bit error in each byte independently; the single address
and control bits detect only an odd number of errors across the whole group.

`parity_error_wdata` and `parity_error_ctrl` are combinational and qualified by
`s_apb_PSEL && s_apb_PENABLE`; they read 0 outside the ACCESS phase and are
hard-tied to 0 when `ENABLE_PARITY=0`. The slave reports mismatches but does not
itself convert them into PSLVERR -- that policy is left to the integrator.

---

## Related Documentation

- **[APB5 Master](apb5_master.md)** - APB5 master interface
- **[APB5 Slave CG](apb5_slave_cg.md)** - Clock-gated variant
- **[APB5 Slave CDC](apb5_slave_cdc.md)** - Clock domain crossing variant
- **[APB4 Slave](../apb/apb_slave.md)** - APB4 version for comparison

---

## Navigation

- **[← Back to APB5 Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
