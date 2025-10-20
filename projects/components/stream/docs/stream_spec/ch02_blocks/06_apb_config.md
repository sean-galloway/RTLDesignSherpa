# APB Config Specification

**Module:** `stream_regs.rdl` (PeakRDL definition) + wrapper
**Location:** `regs/` (definition), `rtl/stream_macro/` (wrapper)
**Status:** Future - PeakRDL generation planned (following HPET pattern)

---

## Overview

The APB Config provides the APB slave interface for STREAM configuration and control. Following the same pattern as `apb_hpet`, this will be implemented using:
1. PeakRDL register definition (`stream_regs.rdl`)
2. Auto-generated register RTL (`peakrdl_generate.py`)
3. Wrapper module with optional CDC (`apb_slave_cdc`)

### Implementation Status

**Current:** Not yet implemented - deferred until after Phase 2 RTL completion
**Future:** Will follow HPET pattern with PeakRDL-generated registers

**Reference:** See `projects/components/apb_hpet/` for proven implementation pattern

### Key Features

- APB slave interface (APB4 protocol)
- 8 channel register sets (16 bytes per channel)
- Global control and status registers
- Kick-off via single APB write
- Optional CDC wrapper (like HPET `apb_slave_cdc`)

---

## Register Map

### Global Registers

| Offset | Name | Access | Width | Description |
|--------|------|--------|-------|-------------|
| 0x00 | GLOBAL_CTRL | RW | 32 | Global enable, channel resets |
| 0x04 | GLOBAL_STATUS | RO | 32 | Channel idle/error status |
| 0x08 | GLOBAL_CONFIG | RW | 32 | Global configuration |
| 0x0C | (Reserved) | - | - | - |

**GLOBAL_CTRL (0x00):**
```
Bits [31:24] - Reserved
Bits [23:16] - Channel reset (one-hot, auto-clear)
Bits [15:8]  - Reserved
Bit  [0]     - Global enable
```

**GLOBAL_STATUS (0x04):**
```
Bits [31:24] - Reserved
Bits [23:16] - Channel error flags
Bits [15:8]  - Reserved
Bits [7:0]   - Channel idle flags
```

### Channel Registers (8 channels   0x10 bytes)

**Base addresses:**
- CH0: 0x10 - 0x1F
- CH1: 0x20 - 0x2F
- CH2: 0x30 - 0x3F
- CH3: 0x40 - 0x4F
- CH4: 0x50 - 0x5F
- CH5: 0x60 - 0x6F
- CH6: 0x70 - 0x7F
- CH7: 0x80 - 0x8F

**Per-Channel Registers:**

| Offset | Name | Access | Width | Description |
|--------|------|--------|-------|-------------|
| +0x00 | CHx_CTRL | WO | 32 | Descriptor address (write to kick off) |
| +0x04 | CHx_STATUS | RO | 32 | Channel status |
| +0x08 | CHx_RD_BURST | RW | 32 | Read burst length config |
| +0x0C | CHx_WR_BURST | RW | 32 | Write burst length config |

**CHx_CTRL (+0x00):**
```
Bits [31:0] - Descriptor address (word-aligned)

Action: Write to this register kicks off descriptor chain fetch
```

**CHx_STATUS (+0x04):**
```
Bits [31:3]  - Reserved
Bit  [2]     - Error flag
Bit  [1]     - Idle flag
Bit  [0]     - Enable flag
```

**CHx_RD_BURST (+0x08):**
```
Bits [31:8]  - Reserved
Bits [7:0]   - Read burst length (beats)

Used by AXI Read Engine for cfg_burst_len
```

**CHx_WR_BURST (+0x0C):**
```
Bits [31:8]  - Reserved
Bits [7:0]   - Write burst length (beats)

Used by AXI Write Engine for cfg_burst_len
```

---

## Interface

### Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int ADDR_WIDTH = 32;
parameter int DATA_WIDTH = 32;
```

### Ports

**APB Slave Interface:**
```systemverilog
input  logic                        pclk;
input  logic                        presetn;

input  logic [ADDR_WIDTH-1:0]       paddr;
input  logic                        psel;
input  logic                        penable;
input  logic                        pwrite;
input  logic [DATA_WIDTH-1:0]       pwdata;
input  logic [3:0]                  pstrb;
output logic                        pready;
output logic [DATA_WIDTH-1:0]       prdata;
output logic                        pslverr;
```

**Configuration Outputs (per channel):**
```systemverilog
output logic [NUM_CHANNELS-1:0]              ch_enable;
output logic [NUM_CHANNELS-1:0]              ch_reset;
output logic [NUM_CHANNELS-1:0][63:0]        ch_desc_addr;
output logic [NUM_CHANNELS-1:0][7:0]         ch_read_burst_len;
output logic [NUM_CHANNELS-1:0][7:0]         ch_write_burst_len;
```

**Status Inputs (per channel):**
```systemverilog
input  logic [NUM_CHANNELS-1:0]              ch_idle;
input  logic [NUM_CHANNELS-1:0]              ch_error;
input  logic [NUM_CHANNELS-1:0][31:0]        ch_bytes_xfered;
```

---

## Operation

### Kick-Off Sequence

**Software writes descriptor address to CHx_CTRL:**

```c
// Software: Kick off channel 0 transfer
write_apb(ADDR_CH0_CTRL, 0x1000_0000);

// Hardware response:
// 1. Register captures descriptor address
// 2. ch_desc_addr[0] <= 0x1000_0000
// 3. ch_enable[0] auto-asserts
// 4. Scheduler begins descriptor fetch
```

### Auto-Enable Behavior

```systemverilog
// On CHx_CTRL write
if (pwrite && paddr == CHx_CTRL_ADDR) begin
    r_ch_desc_addr[channel_id] <= pwdata;
    r_ch_enable[channel_id] <= 1'b1;  // Auto-enable on kick-off
end

// Auto-clear when transfer completes
if (ch_idle[channel_id]) begin
    r_ch_enable[channel_id] <= 1'b0;
end
```

---

## PeakRDL Generation Workflow

### Step-by-Step Process

**See:** `regs/README.md` for complete workflow details

1. **Create:** `regs/stream_regs.rdl` (register definition)
2. **Generate:**
   ```bash
   cd projects/components/stream/regs
   ../../bin/peakrdl_generate.py stream_regs.rdl --copy-rtl ../rtl/stream_macro
   ```
3. **Create Wrapper:** `rtl/stream_macro/apb_config.sv` to instantiate generated registers

### Wrapper Pattern (Future Implementation)

```systemverilog
// apb_config.sv wrapper (to be created)
module apb_config (
    // APB interface
    input  logic        pclk,
    // ...

    // Configuration outputs
    output logic [7:0]  ch_enable,
    // ...
);

    // Instantiate PeakRDL-generated registers
    stream_regs u_regs (
        .pclk    (pclk),
        .presetn (presetn),
        .paddr   (paddr),
        // ... APB signals

        // Generated field outputs
        .global_ctrl_enable    (global_enable),
        .ch0_ctrl_desc_addr    (ch_desc_addr[0]),
        .ch0_rd_burst          (ch_read_burst_len[0]),
        // ...
    );

    // Optional CDC wrapper (if crossing clock domains)
    // Like HPET: apb_hpet.sv wraps apb_slave_cdc

endmodule
```

---

## CDC Considerations

**If APB clock != STREAM aclk:**

Use CDC wrapper pattern from HPET:

```systemverilog
// APB domain (pclk)
apb_slave_cdc #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_cdc (
    // APB side (pclk domain)
    .s_pclk     (pclk),
    .s_presetn  (presetn),
    .s_paddr    (paddr),
    // ...

    // Core side (aclk domain)
    .m_pclk     (aclk),
    .m_presetn  (aresetn),
    .m_paddr    (paddr_sync),
    // ...
);

// STREAM registers in aclk domain
stream_regs u_regs (
    .pclk    (aclk),  // Note: aclk, not pclk
    .paddr   (paddr_sync),
    // ...
);
```

---

## Default Values

**On reset (presetn = 0):**

```systemverilog
// Global
global_enable <= 1'b0;

// Per-channel
for (int i = 0; i < NUM_CHANNELS; i++) begin
    ch_enable[i] <= 1'b0;
    ch_reset[i] <= 1'b0;
    ch_desc_addr[i] <= 64'h0;
    ch_read_burst_len[i] <= 8'd8;   // Default: 8-beat read bursts
    ch_write_burst_len[i] <= 8'd16; // Default: 16-beat write bursts
end
```

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/integration_tests/`

**Test Scenarios:**
1. Register read/write (all registers)
2. Kick-off via CHx_CTRL write
3. Auto-enable behavior
4. Status register reads
5. Multi-channel configuration
6. Reset behavior

---

## Related Documentation

- **Register Generation:** `regs/README.md` - PeakRDL workflow
- **HPET Example:** `projects/components/apb_hpet/` - Reference implementation
- **Scheduler:** `02_scheduler.md` - Consumer of configuration

---

**Last Updated:** 2025-10-17
