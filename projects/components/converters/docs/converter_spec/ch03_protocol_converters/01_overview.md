# Chapter 3: Protocol Converters - Overview

## Introduction

Protocol converters enable communication between components using different communication protocols, essential for integrating diverse IP blocks in complex SoC designs.

## Available Converters

### 1. AXI4-to-APB Bridge
- **Module:** `axi4_to_apb_convert.sv`
- **Purpose:** Full protocol translation from AXI4 to APB
- **Features:** Address width adaptation, state machine control, error mapping

### 2. PeakRDL Adapter
- **Module:** `peakrdl_to_cmdrsp.sv`
- **Purpose:** Register interface to command/response protocol
- **Features:** Protocol decoupling, single-cycle commands, pipelined responses

---

## AXI4-to-APB Bridge

### Overview

Converts AXI4 master transactions (from CPU, DMA) to APB peripheral accesses.

**Key Challenges:**
- Protocol differences (5-channel AXI4 vs 2-phase APB)
- Address width mismatch (64-bit AXI4 vs 32-bit APB)
- Burst support (AXI4 bursts → sequential APB transactions)
- Error response mapping (PSLVERR → BRESP/RRESP)

### Block Diagram

![AXI4-to-APB Converter](../assets/graphviz/axi4_to_apb.png)

### State Machine

The converter uses a state machine to manage protocol translation:

![AXI4-to-APB FSM](../assets/puml/axi4_to_apb_fsm.png)

**States:**
- **IDLE** - Wait for AXI4 transaction
- **READ** - Process AXI4 read → APB read
- **WRITE** - Process AXI4 write → APB write

### Use Cases

1. **CPU to APB Peripherals** - Main processor accessing GPIO, UART, SPI
2. **DMA to Configuration Registers** - DMA controller configuring peripherals
3. **Mixed Protocol Systems** - Integrating AXI4 fabric with legacy APB devices

### Documentation

See [02_axi4_to_apb.md](02_axi4_to_apb.md) for detailed specification.

---

## PeakRDL Adapter

### Overview

Converts PeakRDL-generated register interface to a custom command/response protocol, enabling protocol decoupling and flexible register implementations.

**Key Features:**
- APB-style register interface (input)
- Command/response handshake (output)
- Configurable address and data widths
- Single-cycle command issue

### Block Diagram

![PeakRDL Adapter](../assets/graphviz/peakrdl_adapter.png)

### Interface Types

**Register Interface (APB-style):**
- `reg_addr[ADDR_WIDTH-1:0]` - Register address
- `reg_wdata[DATA_WIDTH-1:0]` - Write data
- `reg_write` - Write enable
- `reg_read` - Read enable
- `reg_rdata[DATA_WIDTH-1:0]` - Read data
- `reg_error` - Error flag

**Command/Response Protocol:**
- Command: valid/ready handshake with addr, data, write flag
- Response: valid/ready handshake with data, error flag

### Use Cases

1. **PeakRDL Register Blocks** - Decoupling register interface from implementation
2. **Custom Control Logic** - Flexible register access mechanism
3. **Testbench Stimulus** - Command-driven register access in verification

### Documentation

See [03_peakrdl_adapter.md](03_peakrdl_adapter.md) for detailed specification.

---

## Comparison

| Feature | AXI4-to-APB | PeakRDL Adapter |
|---------|-------------|-----------------|
| **Input Protocol** | AXI4 (5 channels) | APB-style register |
| **Output Protocol** | APB (2 phases) | Command/response |
| **Complexity** | High (FSM, burst handling) | Low (pass-through) |
| **Use Case** | System interconnect | Register decoupling |
| **Performance** | Sequential per APB | Single-cycle cmd |

---

## Design Considerations

### When to Use Protocol Converters

**Use AXI4-to-APB when:**
- Integrating AXI4 masters with APB peripherals
- Building CPU-to-peripheral bridges
- System has mixed protocol requirements

**Use PeakRDL adapter when:**
- Decoupling register interface from implementation
- Need flexible register access protocol
- Building custom control/configuration logic

### Integration Guidelines

1. **Address Map Planning** - Ensure non-overlapping regions
2. **Error Handling** - Map error responses appropriately
3. **Performance Analysis** - Consider latency impact
4. **Testing Strategy** - Verify protocol compliance

---

**Next Sections:**
- [02_axi4_to_apb.md](02_axi4_to_apb.md) - Detailed AXI4-to-APB specification
- [03_peakrdl_adapter.md](03_peakrdl_adapter.md) - Detailed PeakRDL adapter specification
