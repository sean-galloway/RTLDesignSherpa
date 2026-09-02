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

# apb4_master_stub

## Overview

The `apb4_master_stub` is a lightweight APB master that accepts packed command packets and returns packed response packets. It exists for testbench use — when you need a simple APB master without the full functionality of the standard `apb4_master` module. The packed interface simplifies integration with test drivers and verification components.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CMD_DEPTH | int | 6 | Command buffer depth in **entries** (not a log2 exponent) |
| RSP_DEPTH | int | 6 | Response buffer depth in **entries** (not a log2 exponent) |
| DATA_WIDTH | int | 32 | APB data bus width |
| ADDR_WIDTH | int | 32 | APB address bus width |
| STRB_WIDTH | int | DATA_WIDTH/8 | Write strobe width (calculated) |
| CMD_PACKET_WIDTH | int | Calculated | Command packet width |
| RESP_PACKET_WIDTH | int | Calculated | Response packet width |

## Ports

```systemverilog
module apb4_master_stub #(
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
- `paddr` (AW bits): Address
- `pwdata` (DW bits): Write data — the LSB field (paddr sits ABOVE pwdata)

**Response Packet Format** (MSB to LSB):
- `last` (1 bit): Last transfer indicator
- `first` (1 bit): First transfer indicator
- `pslverr` (1 bit): Slave error
- `prdata` (DW bits): Read data

### First/Last Framing

`first` and `last` exist so that AXI4 burst framing survives the trip through an
APB bridge. `apb4_master` does not carry them through its own command-to-response
pipeline, so the stub keeps a small side FIFO (`gaxi_fifo_sync`, depth
`CMD_DEPTH`): `{last, first}` is enqueued on every command-side handshake and
dequeued on every response-side handshake.

This pairing is essential when the upstream pipelines commands ahead of
responses. Tapping `first`/`last` combinationally from the live `cmd_data` input
instead — as an earlier revision did — pairs command N's response with command
N+1's framing bits as soon as the internal command FIFO accepts N+1. In the
AXI4-to-APB bridge that manifested as `axi4_to_apb4_convert` never seeing
`first=1` again in `RSP_IDLE`, hanging the FSM and surfacing as a timeout on the
master AXI4 R channel.

The side FIFO drains on the EXTERNAL response handshake, so under response
backpressure the accepted-not-yet-drained count can reach
CMD_DEPTH + 1 + RSP_DEPTH — and the FIFO is sized for exactly that bound
(`CMD_DEPTH + RSP_DEPTH + 2`), with a loud simulation `$error` tripwire
should a future change break it. (The original CMD_DEPTH sizing silently
dropped framing records under backpressure; that was TASK-067, fixed.)

### Packet Format Is Not Symmetric With `apb4_slave_stub`

`apb4_slave_stub` omits `first` and `last` in both directions and is therefore
two bits narrower per packet. The two stubs face each other across the APB bus,
never packed-side to packed-side, so this asymmetry is intentional and causes no
integration problem — but the packed buses must not be wired together directly.
See [apb4_slave_stub.md](apb4_slave_stub.md) for the side-by-side comparison.

### Operation

1. Test driver presents packed command on `cmd_data` with `cmd_valid=1`
2. Stub accepts when `cmd_ready=1`
3. Stub unpacks command, enqueues `{last, first}`, and drives APB protocol
4. On APB completion, stub packs the response with the dequeued `{last, first}` and asserts `rsp_valid=1`
5. Test driver reads response when `rsp_ready=1`

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
// Instantiate APB master stub
apb4_master_stub #(
    .DATA_WIDTH(32),
    .ADDR_WIDTH(16)
) u_apb4_master_stub (
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
// Field order per the RTL unpack: {last, first, pwrite, pprot, pstrb, paddr, pwdata}
assign test_cmd_data = {1'b1, 1'b1, 1'b1, 3'b000, 4'hF, 16'h1000, 32'hDEADBEEF};
assign test_cmd_valid = 1'b1;
```

## Design Notes

### Testbench Usage

This module is intended for:
- System-level testbenches
- Integration testing
- Simple APB traffic generation
- Verification component integration

For production use, consider the full-featured `apb4_master` module.

### Packed Interface Benefits

- Simplified connection to test drivers
- Reduces signal count
- Easier integration with verification IP
- Convenient for parameterized test sequences

## Related Modules

- `apb4_master.sv` - Full-featured APB master with independent interfaces
- `apb4_slave_stub.sv` - Companion APB slave stub
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
- **Full APB Master**: [apb4_master.md](apb4_master.md)
- **APB Slave Stub**: [apb4_slave_stub.md](apb4_slave_stub.md)
- **APB5 Equivalent**: [apb5_master_stub.md](../apb5/apb5_master_stub.md)

---

## Navigation

- **[← Back to APB Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
