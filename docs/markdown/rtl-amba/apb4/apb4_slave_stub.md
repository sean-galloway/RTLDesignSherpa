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

# apb4_slave_stub

## Overview

The `apb4_slave_stub` is a lightweight APB slave that converts APB protocol signals into packed command/response packets. It exists for testbench use — when you need a simple APB slave without the full functionality of the standard `apb4_slave` module. The packed interface simplifies integration with test responders and verification components.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| DEPTH | int | 4 | Skid-buffer depth in **entries** (not a log2 exponent); must be one of 2..8 inclusive |
| DATA_WIDTH | int | 32 | APB data bus width |
| ADDR_WIDTH | int | 32 | APB address bus width |
| STRB_WIDTH | int | DATA_WIDTH/8 | Write strobe width (calculated) |
| CMD_PACKET_WIDTH | int | Calculated | Command packet width |
| RESP_PACKET_WIDTH | int | Calculated | Response packet width |

## Ports

```systemverilog
module apb4_slave_stub #(
    parameter int DEPTH    = 4,
    parameter int DATA_WIDTH    = 32,
    parameter int ADDR_WIDTH    = 32,
    parameter int STRB_WIDTH    = DATA_WIDTH / 8,
    parameter int CMD_PACKET_WIDTH = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 4, // addr, data, strb, prot, pwrite
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + 1, // data, resp
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH
) (
    // Clock and Reset
    input  logic                        pclk,
    input  logic                        presetn,

    // APB Slave Interface
    input  logic                        s_apb_PSEL,
    input  logic                        s_apb_PENABLE,
    input  logic [AW-1:0]               s_apb_PADDR,
    input  logic                        s_apb_PWRITE,
    input  logic [DW-1:0]               s_apb_PWDATA,
    input  logic [SW-1:0]               s_apb_PSTRB,
    input  logic [2:0]                  s_apb_PPROT,
    output logic [DW-1:0]               s_apb_PRDATA,
    output logic                        s_apb_PSLVERR,
    output logic                        s_apb_PREADY,

    // Command Packet Interface (packed)
    output logic                        cmd_valid,
    input  logic                        cmd_ready,
    output logic [CPW-1:0]              cmd_data,

    // Response Packet Interface (packed)
    input  logic                        rsp_valid,
    output logic                        rsp_ready,
    input  logic [RPW-1:0]              rsp_data
);
```

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| pclk | 1 | Input | APB clock |
| presetn | 1 | Input | APB active-low reset |

### APB Slave Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_apb_PSEL | 1 | Input | Peripheral select |
| s_apb_PENABLE | 1 | Input | Enable signal |
| s_apb_PADDR | AW | Input | Address bus |
| s_apb_PWRITE | 1 | Input | Write/read (1=write, 0=read) |
| s_apb_PWDATA | DW | Input | Write data |
| s_apb_PSTRB | SW | Input | Write strobe |
| s_apb_PPROT | 3 | Input | Protection attributes |
| s_apb_PRDATA | DW | Output | Read data |
| s_apb_PSLVERR | 1 | Output | Slave error |
| s_apb_PREADY | 1 | Output | Ready signal |

### Packed Command Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cmd_valid | 1 | Output | Command packet valid |
| cmd_ready | 1 | Input | Ready for command packet |
| cmd_data | CPW | Output | Packed command (pwrite, pprot, pstrb, paddr, pwdata) |

### Packed Response Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| rsp_valid | 1 | Input | Response packet valid |
| rsp_ready | 1 | Output | Ready for response packet |
| rsp_data | RPW | Input | Packed response (resp, prdata) |

## Functional Description

### Packet Interface

The stub uses packed interfaces to simplify testbench integration:

**Command Packet Format** (MSB to LSB):
- `pwrite` (1 bit): Write/read operation
- `pprot` (3 bits): Protection attributes
- `pstrb` (SW bits): Write strobe
- `paddr` (AW bits): Address
- `pwdata` (DW bits): Write data — the LSB field (paddr sits ABOVE pwdata, matching the comparison table below)

**Response Packet Format** (MSB to LSB):
- `pslverr` (1 bit): Slave error
- `prdata` (DW bits): Read data

### Packet Format Is Not Symmetric With `apb4_master_stub`

`apb4_master_stub` carries two extra bits in each direction — `first` and `last`:

| | `apb4_slave_stub` | `apb4_master_stub` |
|---|---|---|
| `CMD_PACKET_WIDTH` | `AW + DW + SW + 4` | `AW + DW + SW + 3 + 1 + 1 + 1` |
| Command fields | pwrite, pprot, pstrb, paddr, pwdata | last, first, pwrite, pprot, pstrb, paddr, pwdata |
| `RESP_PACKET_WIDTH` | `DW + 1` | `DW + 1 + 1 + 1` |
| Response fields | pslverr, prdata | last, first, pslverr, prdata |

**This is intentional, not a defect.** The `first`/`last` bits exist so
`apb4_master_stub` can carry AXI4 burst framing through the AXI4-to-APB bridge;
an APB slave has no burst to frame and so has no use for them.

The two stubs are **never** connected packed-side to packed-side. They face each
other across the APB bus, and the APB bus itself has no `first`/`last` signals,
so no incompatibility arises. Do not attempt to wire `apb4_master_stub.cmd_data`
directly into `apb4_slave_stub` — the widths differ and the field alignment
differs.

### Difference From `apb4_slave`

This stub is a simplified two-state FSM (`IDLE`, `XFER_DATA`) with combinational
outputs. It does **not** implement the `PENABLE` rising-edge detect or the
orphan-response guard present in [apb4_slave](apb4_slave.md). Use `apb4_slave` for
anything synthesized into a real design, particularly behind a CDC.

### Operation

1. APB master drives transaction on APB interface
2. Stub detects PSEL/PENABLE and packs command
3. Stub presents command packet on `cmd_data` with `cmd_valid=1`
4. Test responder reads command when `cmd_ready=1`
5. Test responder provides response on `rsp_data` with `rsp_valid=1`
6. Stub unpacks response and drives APB PRDATA/PSLVERR/PREADY

## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
```systemverilog
// Instantiate APB slave stub
apb4_slave_stub #(
    .DATA_WIDTH(32),
    .ADDR_WIDTH(16)
) u_apb4_slave_stub (
    .pclk(clk),
    .presetn(rst_n),
    // APB interface from master/interconnect
    .s_apb_PSEL(apb_psel),
    .s_apb_PENABLE(apb_penable),
    .s_apb_PADDR(apb_paddr),
    .s_apb_PWRITE(apb_pwrite),
    .s_apb_PWDATA(apb_pwdata),
    .s_apb_PSTRB(apb_pstrb),
    .s_apb_PPROT(apb_pprot),
    .s_apb_PRDATA(apb_prdata),
    .s_apb_PSLVERR(apb_pslverr),
    .s_apb_PREADY(apb_pready),
    // Packed interface to test responder
    .cmd_valid(test_cmd_valid),
    .cmd_ready(test_cmd_ready),
    .cmd_data(test_cmd_data),
    .rsp_valid(test_rsp_valid),
    .rsp_ready(test_rsp_ready),
    .rsp_data(test_rsp_data)
);

// Example: Respond to command (in testbench)
// When cmd_valid: unpack command, generate response
always_comb begin
    test_cmd_ready = 1'b1;  // Always ready
    if (test_cmd_valid) begin
        // Unpack command
        logic [DW-1:0] wdata = test_cmd_data[DW-1:0];
        logic [AW-1:0] addr = test_cmd_data[DW+AW-1:DW];
        logic pwrite = test_cmd_data[CPW-1];

        // Generate response
        test_rsp_data = {1'b0, read_memory(addr)};  // No error, return data
        test_rsp_valid = 1'b1;
    end
end
```

## Design Notes

### Testbench Usage

This module is intended for:
- System-level testbenches
- Integration testing
- Simple APB slave emulation
- Memory model integration
- Verification component integration

For production use, consider the full-featured `apb4_slave` module.

### Response Generation

The stub expects immediate response from the test driver. For multi-cycle latency:
- Test driver should buffer commands
- Assert `rsp_valid` only when response is ready
- Stub will hold PREADY low until response arrives

### Packed Interface Benefits

- Simplified connection to test drivers
- Reduces signal count
- Easier integration with verification IP
- Convenient for memory models and responders

## Related Modules

- `apb4_slave.sv` - Full-featured APB slave with independent interfaces
- `apb4_master_stub.sv` - Companion APB master stub
- `apb4_monitor.sv` - APB transaction monitoring

## Testing

**No dedicated testbench, and none is expected.** This is a stub: a tie-off
shell that presents the interface and drives inert values, so there is no
behaviour to verify beyond elaboration. `make verilator` lints it as its own
top on every run, which is the coverage that applies.

Treat any behaviour described on this page as unverified by simulation.

---

## References

- **APB Protocol**: ARM IHI 0024C -- AMBA APB Protocol Specification, Version 2.0 (APB4)
- **Full APB Slave**: [apb4_slave.md](apb4_slave.md)
- **APB Master Stub**: [apb4_master_stub.md](apb4_master_stub.md)
- **APB5 Equivalent**: [apb5_slave_stub.md](../apb5/apb5_slave_stub.md)

---

## Navigation

- **[← Back to APB Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
