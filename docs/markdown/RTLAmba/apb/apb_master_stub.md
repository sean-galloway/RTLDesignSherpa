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

# apb_master_stub

A lightweight APB master stub module that provides packed command/response interfaces for simplified testbench integration and system-level testing.

## Overview

The `apb_master_stub` module acts as a simple APB master that accepts packed command packets and returns packed response packets. It's designed for testbench use where a simple APB master is needed without the full functionality of the standard `apb_master` module. The packed interface simplifies integration with test drivers and verification components.

## Module Declaration

```systemverilog
module apb_master_stub #(
    parameter int CMD_DEPTH         = 6,
    parameter int RSP_DEPTH         = 6,
    parameter int DATA_WIDTH        = 32,
    parameter int ADDR_WIDTH        = 32,
    parameter int STRB_WIDTH        = DATA_WIDTH / 8,
    parameter int CMD_PACKET_WIDTH  = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 3 + 1 + 1 + 1,
                                        // addr, data, strb, prot, pwrite, first, last
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + 1 + 1 + 1, // data, pslverr, first, last
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH
) (
    // Clock and Reset
    input  logic                         pclk,
    input  logic                         presetn,

    // APB Master Interface
    output logic                         m_apb_PSEL,
    output logic                         m_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0]        m_apb_PADDR,
    output logic                         m_apb_PWRITE,
    output logic [DATA_WIDTH-1:0]        m_apb_PWDATA,
    output logic [STRB_WIDTH-1:0]        m_apb_PSTRB,
    output logic [2:0]                   m_apb_PPROT,
    input  logic [DATA_WIDTH-1:0]        m_apb_PRDATA,
    input  logic                         m_apb_PSLVERR,
    input  logic                         m_apb_PREADY,

    // Command Packet Interface (packed)
    input  logic                         cmd_valid,
    output logic                         cmd_ready,
    input  logic [CMD_PACKET_WIDTH-1:0]  cmd_data,

    // Response Packet Interface (packed)
    output logic                         rsp_valid,
    input  logic                         rsp_ready,
    output logic [RESP_PACKET_WIDTH-1:0] rsp_data
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CMD_DEPTH | int | 6 | Command FIFO depth (log2) |
| RSP_DEPTH | int | 6 | Response FIFO depth (log2) |
| DATA_WIDTH | int | 32 | APB data bus width |
| ADDR_WIDTH | int | 32 | APB address bus width |
| STRB_WIDTH | int | DATA_WIDTH/8 | Write strobe width (calculated) |
| CMD_PACKET_WIDTH | int | Calculated | Command packet width |
| RESP_PACKET_WIDTH | int | Calculated | Response packet width |

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| pclk | 1 | Input | APB clock |
| presetn | 1 | Input | APB active-low reset |

### APB Master Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_apb_PSEL | 1 | Output | Peripheral select |
| m_apb_PENABLE | 1 | Output | Enable signal |
| m_apb_PADDR | AW | Output | Address bus |
| m_apb_PWRITE | 1 | Output | Write/read (1=write, 0=read) |
| m_apb_PWDATA | DW | Output | Write data |
| m_apb_PSTRB | SW | Output | Write strobe |
| m_apb_PPROT | 3 | Output | Protection attributes |
| m_apb_PRDATA | DW | Input | Read data |
| m_apb_PSLVERR | 1 | Input | Slave error |
| m_apb_PREADY | 1 | Input | Ready signal |

### Packed Command Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cmd_valid | 1 | Input | Command packet valid |
| cmd_ready | 1 | Output | Ready for command packet |
| cmd_data | CPW | Input | Packed command (addr, data, strb, prot, pwrite, first, last) |

### Packed Response Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| rsp_valid | 1 | Output | Response packet valid |
| rsp_ready | 1 | Input | Ready for response packet |
| rsp_data | RPW | Output | Packed response (data, pslverr, first, last) |

## Functional Description

### Packet Interface

The stub uses packed interfaces to simplify testbench integration:

**Command Packet Format** (MSB to LSB):
- `last` (1 bit): Last transfer indicator
- `first` (1 bit): First transfer indicator
- `pwrite` (1 bit): Write/read operation
- `pprot` (3 bits): Protection attributes
- `pstrb` (SW bits): Write strobe
- `pwdata` (DW bits): Write data
- `paddr` (AW bits): Address

**Response Packet Format** (MSB to LSB):
- `last` (1 bit): Last transfer indicator
- `first` (1 bit): First transfer indicator
- `pslverr` (1 bit): Slave error
- `prdata` (DW bits): Read data

### Operation

1. Test driver presents packed command on `cmd_data` with `cmd_valid=1`
2. Stub accepts when `cmd_ready=1`
3. Stub unpacks command and drives APB protocol
4. On APB completion, stub packs response and asserts `rsp_valid=1`
5. Test driver reads response when `rsp_ready=1`

## Usage Example

```systemverilog
// Instantiate APB master stub
apb_master_stub #(
    .DATA_WIDTH(32),
    .ADDR_WIDTH(16)
) u_apb_master_stub (
    .pclk(clk),
    .presetn(rst_n),
    // APB interface to slave/interconnect
    .m_apb_PSEL(apb_psel),
    .m_apb_PENABLE(apb_penable),
    .m_apb_PADDR(apb_paddr),
    .m_apb_PWRITE(apb_pwrite),
    .m_apb_PWDATA(apb_pwdata),
    .m_apb_PSTRB(apb_pstrb),
    .m_apb_PPROT(apb_pprot),
    .m_apb_PRDATA(apb_prdata),
    .m_apb_PSLVERR(apb_pslverr),
    .m_apb_PREADY(apb_pready),
    // Packed interface to test driver
    .cmd_valid(test_cmd_valid),
    .cmd_ready(test_cmd_ready),
    .cmd_data(test_cmd_data),
    .rsp_valid(test_rsp_valid),
    .rsp_ready(test_rsp_ready),
    .rsp_data(test_rsp_data)
);

// Example: Send write command (in testbench)
// Pack command: addr=0x1000, data=0xDEADBEEF, write=1
assign test_cmd_data = {1'b1, 1'b1, 1'b1, 3'b000, 4'hF, 32'hDEADBEEF, 16'h1000};
assign test_cmd_valid = 1'b1;
```

## Design Notes

### Testbench Usage

This module is intended for:
- System-level testbenches
- Integration testing
- Simple APB traffic generation
- Verification component integration

For production use, consider the full-featured `apb_master` module.

### Packed Interface Benefits

- Simplified connection to test drivers
- Reduces signal count
- Easier integration with verification IP
- Convenient for parameterized test sequences

## Related Modules

- `apb_master.sv` - Full-featured APB master with independent interfaces
- `apb_slave_stub.sv` - Companion APB slave stub
- `apb_monitor.sv` - APB transaction monitoring

## References

- **APB Protocol**: AMBA APB Protocol Specification v2.0
- **Full APB Master**: [apb_master.md](apb_master.md)
- **APB Slave Stub**: [apb_slave_stub.md](apb_slave_stub.md)

---

## Navigation

- **[← Back to APB Index](README.md)** (if exists, otherwise remove this line)
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
