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

# peakrdl_to_cmdrsp

**Module:** `peakrdl_to_cmdrsp.sv`
**Location:** `rtl/amba/shims/`
**Status:** ✅ Production Ready

---

## Overview

Protocol adapter that bridges between the RTL Design Sherpa standard cmd/rsp interface and the PeakRDL register block "passthrough" cpuif interface. This shim enables seamless integration of PeakRDL-generated register blocks with RTL Design Sherpa's APB infrastructure.

### Key Features

- ✅ **Protocol Conversion:** cmd/rsp valid/ready ↔ PeakRDL passthrough cpuif
- ✅ **Stall Handling:** Proper support for PeakRDL req_stall signals
- ✅ **Strobe Conversion:** Byte strobes → bit enables (PeakRDL requirement)
- ✅ **Error Propagation:** PeakRDL errors → cmd/rsp PSLVERR
- ✅ **FSM-Based:** Robust state machines for cmd and rsp channels
- ✅ **Assertions Included:** Comprehensive protocol checking (simulation only)

---

## Background: PeakRDL Integration

**PeakRDL** is a register description language compiler that generates SystemVerilog register blocks from `.rdl` files. The generated blocks use a "passthrough" cpuif (CPU interface) that differs from standard bus protocols.

**This adapter solves:**
- Integration with RTL Design Sherpa's cmd/rsp-based APB infrastructure
- Byte strobe → bit enable conversion (PeakRDL uses bit-level enables)
- Stall handling (PeakRDL can stall requests separately for read/write)
- Response channel synchronization

**See Also:** `rtl/amba/shims/peakrdl_adapter_README.md` for PeakRDL workflow guide

---

## Module Declaration

```systemverilog
module peakrdl_to_cmdrsp #(
    parameter int ADDR_WIDTH = 12,  // Address width (match PeakRDL generation)
    parameter int DATA_WIDTH = 32   // Must match PeakRDL (typically 32)
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
    output logic                    regblk_req,         // Request strobe
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

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ADDR_WIDTH` | 12 | Address width for cmd/rsp interface (4 KB register space) |
| `DATA_WIDTH` | 32 | Data width (must match PeakRDL generation, typically 32) |

**Note:** These must match the PeakRDL register block generation parameters.

---

## Ports

### CMD/RSP Interface (RTL Design Sherpa Standard)

**Command Channel:**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cmd_valid` | Input | 1 | Command valid |
| `cmd_ready` | Output | 1 | Ready to accept command |
| `cmd_pwrite` | Input | 1 | Write operation (1=write, 0=read) |
| `cmd_paddr` | Input | ADDR_WIDTH | Byte address |
| `cmd_pwdata` | Input | DATA_WIDTH | Write data |
| `cmd_pstrb` | Input | DATA_WIDTH/8 | Byte strobes (1=valid byte) |

**Response Channel:**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `rsp_valid` | Output | 1 | Response valid |
| `rsp_ready` | Input | 1 | Ready to consume response |
| `rsp_prdata` | Output | DATA_WIDTH | Read data |
| `rsp_pslverr` | Output | 1 | Error flag (1=error) |

### PeakRDL Passthrough Interface

**Request Signals:**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `regblk_req` | Output | 1 | Request strobe (valid for 1 cycle) |
| `regblk_req_is_wr` | Output | 1 | Operation type (1=write, 0=read) |
| `regblk_addr` | Output | ADDR_WIDTH | Register address |
| `regblk_wr_data` | Output | DATA_WIDTH | Write data |
| `regblk_wr_biten` | Output | DATA_WIDTH | Write bit enables (1=update bit) |

**Stall/Acknowledge Signals:**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `regblk_req_stall_wr` | Input | 1 | Write request stalled (retry later) |
| `regblk_req_stall_rd` | Input | 1 | Read request stalled (retry later) |
| `regblk_rd_ack` | Input | 1 | Read completed (1 cycle pulse) |
| `regblk_wr_ack` | Input | 1 | Write completed (1 cycle pulse) |
| `regblk_rd_data` | Input | DATA_WIDTH | Read data (valid with rd_ack) |
| `regblk_rd_err` | Input | 1 | Read error (valid with rd_ack) |
| `regblk_wr_err` | Input | 1 | Write error (valid with wr_ack) |

---

## Behavior

### Command State Machine

**States:**
```
CMD_IDLE       → Waiting for command
CMD_WAIT_ACK   → Waiting for register block ack
CMD_STALLED    → Stalled, retry when stall clears
```

**Transitions:**
```
IDLE:
  - cmd_valid && !stall → WAIT_ACK
  - cmd_valid && stall  → STALLED

WAIT_ACK:
  - regblk_wr_ack || regblk_rd_ack → IDLE

STALLED:
  - !stall → WAIT_ACK (retry request)
```

### Response State Machine

**States:**
```
RSP_IDLE    → No response pending
RSP_VALID   → Response valid, waiting for rsp_ready
```

**Transitions:**
```
IDLE:
  - regblk_wr_ack || regblk_rd_ack → VALID

VALID:
  - rsp_ready → IDLE
```

### Strobe to Bit Enable Conversion

**PeakRDL requires bit-level write enables:**
```systemverilog
function automatic logic [DATA_WIDTH-1:0] strb_to_biten(
    input logic [STRB_WIDTH-1:0] strb
);
    for (int i = 0; i < STRB_WIDTH; i++) begin
        biten[i*8 +: 8] = {8{strb[i]}};
    end
    return biten;
endfunction
```

**Example (32-bit):**
```
cmd_pstrb = 4'b1100
            ↓
regblk_wr_biten = 32'hFFFF_0000
                   (upper 16 bits enabled)
```

### Stall Handling

**Separate stalls for read and write:**
- `regblk_req_stall_wr`: Write request cannot be accepted
- `regblk_req_stall_rd`: Read request cannot be accepted

**Behavior:**
1. If stall asserted when cmd_valid:
   - Register command locally
   - Enter CMD_STALLED state
   - Keep regblk_req deasserted
2. When stall clears:
   - Assert regblk_req with registered command
   - Move to CMD_WAIT_ACK

**Purpose:** Allows PeakRDL register block to implement internal arbitration or serialization.

---

## Usage Examples

### Example 1: Basic Integration with PeakRDL Register Block

```systemverilog
// Generate PeakRDL register block
// $ peakrdl regblock my_regs.rdl -o my_regs.sv

// Instantiate adapter
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(12),   // 4 KB register space
    .DATA_WIDTH(32)
) u_adapter (
    .aclk(apb_clk),
    .aresetn(apb_resetn),

    // From APB master stub (cmd/rsp interface)
    .cmd_valid(apb_cmd_valid),
    .cmd_ready(apb_cmd_ready),
    .cmd_pwrite(apb_cmd_pwrite),
    .cmd_paddr(apb_cmd_paddr),
    .cmd_pwdata(apb_cmd_pwdata),
    .cmd_pstrb(apb_cmd_pstrb),

    .rsp_valid(apb_rsp_valid),
    .rsp_ready(apb_rsp_ready),
    .rsp_prdata(apb_rsp_prdata),
    .rsp_pslverr(apb_rsp_pslverr),

    // To PeakRDL register block
    .regblk_req(my_regs_req),
    .regblk_req_is_wr(my_regs_req_is_wr),
    .regblk_addr(my_regs_addr),
    .regblk_wr_data(my_regs_wr_data),
    .regblk_wr_biten(my_regs_wr_biten),

    .regblk_req_stall_wr(my_regs_req_stall_wr),
    .regblk_req_stall_rd(my_regs_req_stall_rd),
    .regblk_rd_ack(my_regs_rd_ack),
    .regblk_rd_err(my_regs_rd_err),
    .regblk_rd_data(my_regs_rd_data),
    .regblk_wr_ack(my_regs_wr_ack),
    .regblk_wr_err(my_regs_wr_err)
);

// Instantiate PeakRDL register block
my_regs u_regs (
    .clk(apb_clk),
    .rst(~apb_resetn),

    // Passthrough cpuif
    .cpuif_req(my_regs_req),
    .cpuif_req_is_wr(my_regs_req_is_wr),
    .cpuif_addr(my_regs_addr),
    .cpuif_wr_data(my_regs_wr_data),
    .cpuif_wr_biten(my_regs_wr_biten),
    .cpuif_req_stall_wr(my_regs_req_stall_wr),
    .cpuif_req_stall_rd(my_regs_req_stall_rd),
    .cpuif_rd_ack(my_regs_rd_ack),
    .cpuif_rd_err(my_regs_rd_err),
    .cpuif_rd_data(my_regs_rd_data),
    .cpuif_wr_ack(my_regs_wr_ack),
    .cpuif_wr_err(my_regs_wr_err),

    // Field interfaces
    .hwif_in(...),
    .hwif_out(...)
);
```

### Example 2: APB to PeakRDL Complete Path

```systemverilog
// APB Master → APB Slave Stub → peakrdl_to_cmdrsp → PeakRDL Register Block

// APB slave stub (APB protocol → cmd/rsp)
apb_slave_stub #(
    .DATA_WIDTH(32),
    .ADDR_WIDTH(12)
) u_apb_slave (
    .pclk(apb_clk),
    .presetn(apb_resetn),

    // APB slave interface
    .s_apb_PSEL(apb_psel),
    .s_apb_PADDR(apb_paddr),
    .s_apb_PENABLE(apb_penable),
    .s_apb_PWRITE(apb_pwrite),
    .s_apb_PWDATA(apb_pwdata),
    .s_apb_PSTRB(apb_pstrb),
    .s_apb_PREADY(apb_pready),
    .s_apb_PRDATA(apb_prdata),
    .s_apb_PSLVERR(apb_pslverr),

    // cmd/rsp interface
    .cmd_valid(cmd_valid),
    .cmd_ready(cmd_ready),
    .cmd_pwrite(cmd_pwrite),
    .cmd_paddr(cmd_paddr),
    .cmd_pwdata(cmd_pwdata),
    .cmd_pstrb(cmd_pstrb),
    .rsp_valid(rsp_valid),
    .rsp_ready(rsp_ready),
    .rsp_prdata(rsp_prdata),
    .rsp_pslverr(rsp_pslverr)
);

// PeakRDL adapter (cmd/rsp → passthrough cpuif)
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(12),
    .DATA_WIDTH(32)
) u_adapter (
    .aclk(apb_clk),
    .aresetn(apb_resetn),
    .cmd_valid(cmd_valid),
    .cmd_ready(cmd_ready),
    // ... cmd/rsp interface ...
    .regblk_req(regblk_req),
    // ... passthrough cpuif ...
);

// PeakRDL register block
my_regs u_regs (
    .clk(apb_clk),
    .rst(~apb_resetn),
    .cpuif_req(regblk_req),
    // ... passthrough cpuif ...
);
```

---

## Timing Diagrams

### Read Transaction (No Stall)

```
Cycle:         0    1    2    3    4    5
              ___  ___  ___  ___  ___  ___
aclk       __|   |_|   |_|   |_|   |_|   |_

cmd_valid  ____/¯¯¯¯¯\_____________________
cmd_ready  ¯¯¯¯¯¯¯¯¯\______/¯¯¯¯¯¯¯¯¯¯¯¯¯¯
cmd_pwrite ____[  0  ]_____________________
cmd_paddr  ____[0x100]_____________________

regblk_req ________/¯\_____________________
regblk_rd_ack __________/¯\_________________

rsp_valid  ____________/¯¯¯¯¯\_____________
rsp_ready  ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯\______/¯¯¯¯¯
rsp_prdata ____________[DATA  ]_____________
```

### Write Transaction with Stall

```
Cycle:         0    1    2    3    4    5    6
              ___  ___  ___  ___  ___  ___  ___
aclk       __|   |_|   |_|   |_|   |_|   |_|   |_

cmd_valid  ____/¯¯¯¯¯\_____________________________
cmd_ready  ¯¯¯¯¯¯¯¯¯\______________/¯¯¯¯¯¯¯¯¯¯¯¯¯¯

regblk_req_stall_wr ___/¯¯¯¯¯¯¯\___________________
               (stalled in cycles 1-2)

regblk_req ____________/¯\_________________________
                 (asserted when stall clears)

regblk_wr_ack ______________/¯\___________________

rsp_valid  ________________/¯¯¯¯¯\________________
rsp_ready  ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯\______/¯¯¯¯¯¯¯¯
```

---

## Testing

```bash
# Run adapter test
pytest val/amba/test_peakrdl_to_cmdrsp.py -v

# Test with waveforms
pytest val/amba/test_peakrdl_to_cmdrsp.py --vcd=peakrdl.vcd -v
gtkwave peakrdl.vcd
```

---

## Assertions

**Included assertions (simulation only):**

1. **cmd_valid_stable:** cmd_valid must remain high until cmd_ready
2. **cmd_data_stable:** cmd signals must remain stable until cmd_ready
3. **rsp_valid_stable:** rsp_valid must remain high until rsp_ready
4. **rsp_data_stable:** rsp signals must remain stable until rsp_ready

**Purpose:** Catch protocol violations during simulation.

---

## Performance

### Latency

| Operation | Typical Latency | Notes |
|-----------|-----------------|-------|
| Read (no stall) | 2 cycles | req → rd_ack → rsp |
| Write (no stall) | 2 cycles | req → wr_ack → rsp |
| Read (with stall) | 2 + stall cycles | Depends on PeakRDL arbitration |
| Write (with stall) | 2 + stall cycles | Depends on PeakRDL arbitration |

### Throughput

- **Maximum:** 1 transaction per 2 cycles (no stalls)
- **Typical:** 1 transaction per 3-5 cycles (APB overhead)

---

## Synthesis Notes

### Resource Usage

**Typical (ADDR_WIDTH=12, DATA_WIDTH=32):**
- ~50 LUTs
- ~100 FFs
- 0 BRAM

**Components:**
- Command FSM: ~20 LUTs, ~40 FFs
- Response FSM: ~10 LUTs, ~35 FFs
- Strobe conversion: ~20 LUTs (combinatorial)

---

## Related Modules

- **[apb_slave_stub](../apb/apb_slave_stub.md)** - APB → cmd/rsp conversion (upstream)
- **[apb_master_stub](../apb/apb_master_stub.md)** - cmd/rsp → APB conversion

**External:**
- PeakRDL: https://github.com/SystemRDL/PeakRDL
- PeakRDL regblock: https://github.com/SystemRDL/PeakRDL-regblock

---

## When to Use

**✅ Use This Adapter When:**
- Integrating PeakRDL-generated register blocks
- Using RTL Design Sherpa APB infrastructure
- Need cmd/rsp ↔ passthrough cpuif conversion

**✅ Alternatives:**
- PeakRDL native APB cpuif (if not using cmd/rsp)
- Custom register implementation (if not using PeakRDL)

---

## PeakRDL Workflow

**Complete workflow documented in:** `rtl/amba/shims/peakrdl_adapter_README.md`

**Quick summary:**
1. Write `.rdl` register description
2. Generate SystemVerilog: `peakrdl regblock my_regs.rdl -o my_regs.sv`
3. Select passthrough cpuif during generation
4. Use this adapter to bridge to APB infrastructure

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to Shims Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
