# AXI4 to AXI4-Lite Protocol Converter

## Overview

The AXI4-to-AXI4-Lite converter provides protocol downgrade from full AXI4 to simplified AXI4-Lite by decomposing multi-beat bursts into multiple single-beat transactions.

**Available Modules:**
- **axi4_to_axil4_rd.sv** - Read-only converter (AR + R channels)
- **axi4_to_axil4_wr.sv** - Write-only converter (AW + W + B channels)
- **axi4_to_axil4.sv** - Full bidirectional converter (wrapper)

---

## Key Features

### Protocol Translation
- **Burst Decomposition** - Multi-beat bursts → multiple single-beat transactions
- **Signal Removal** - Drops AXI4-specific signals (ID, USER, REGION, QOS)
- **Burst Types** - Supports FIXED, INCR, WRAP (all converted to single beats)
- **Response Aggregation** - Collects worst-case error across burst
- **ID Preservation** - Returns responses with original transaction ID

### Performance
- **Single-Beat Passthrough** - Zero-cycle overhead for single transactions (ARLEN/AWLEN = 0)
- **Pipelined Decomposition** - Minimizes latency for multi-beat bursts
- **Independent Channels** - AW and W can complete in any order (write path)

### Design Characteristics
- **Data Width Match** - Input and output data widths must be identical
- **No Width Conversion** - Pure protocol translation only
- **Configurable Skid Buffers** - Optional timing closure helpers

---

## Read Converter (axi4_to_axil4_rd)

### Module Parameters

```systemverilog
module axi4_to_axil4_rd #(
    parameter int AXI_ID_WIDTH      = 8,      // Transaction ID width (1-16)
    parameter int AXI_ADDR_WIDTH    = 32,     // Address bus width (12-64)
    parameter int AXI_DATA_WIDTH    = 32,     // Data bus width (must match)
    parameter int AXI_USER_WIDTH    = 1,      // User signal width (0-1024)
    parameter int SKID_DEPTH_AR     = 2,      // Address skid depth (2-8)
    parameter int SKID_DEPTH_R      = 4       // Response skid depth (2-8)
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // Slave AXI4 Read Interface (Input - Full Protocol)
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    // Master AXI4-Lite Read Interface (Output - Simplified Protocol)
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_araddr,
    output logic [2:0]                  m_axil_arprot,
    output logic                        m_axil_arvalid,
    input  logic                        m_axil_arready,

    input  logic [AXI_DATA_WIDTH-1:0]   m_axil_rdata,
    input  logic [1:0]                  m_axil_rresp,
    input  logic                        m_axil_rvalid,
    output logic                        m_axil_rready
);
```

### Burst Decomposition Algorithm

**Single Beat (ARLEN = 0):**
1. Pass AR through immediately (zero-cycle overhead)
2. Pass R response back directly
3. Assert RLAST on single R beat

**Multi-Beat Burst (ARLEN > 0):**
1. Capture burst parameters (address, length, size, burst type)
2. Enter burst decomposition FSM
3. For each beat (0 to ARLEN):
   - Issue single-beat AXIL4 AR with current address
   - Wait for AXIL4 R response
   - Increment address (INCR/WRAP) or keep same (FIXED)
   - Accumulate worst-case response
4. Assert RLAST on final beat
5. Return to idle

**FSM States:**
- **RD_IDLE** - Waiting for AR transaction, passthrough single beats
- **RD_BURST** - Processing multi-beat burst (beats 0 to ARLEN-1)
- **RD_LAST_BEAT** - Final beat of burst (assert RLAST)

### Response Aggregation

Responses are accumulated using worst-case priority:
- SLVERR (0b10) > DECERR (0b11) > EXOKAY (0b01) > OKAY (0b00)

The worst response across all beats is returned with RLAST.

### Example Waveforms

**4-Beat INCR Burst (32-bit, size=2):**
```
Cycle  AR                 AXIL AR             AXIL R           AXI4 R
  0    addr=0x1000        -                   -                -
       len=3
  1    -                  addr=0x1000         -                -
  2    -                  -                   data=0xAAAA      data=0xAAAA, last=0
  3    -                  addr=0x1004         -                -
  4    -                  -                   data=0xBBBB      data=0xBBBB, last=0
  5    -                  addr=0x1008         -                -
  6    -                  -                   data=0xCCCC      data=0xCCCC, last=0
  7    -                  addr=0x100C         -                -
  8    -                  -                   data=0xDDDD      data=0xDDDD, last=1
```

---

## Write Converter (axi4_to_axil4_wr)

### Module Parameters

```systemverilog
module axi4_to_axil4_wr #(
    parameter int AXI_ID_WIDTH      = 8,      // Transaction ID width (1-16)
    parameter int AXI_ADDR_WIDTH    = 32,     // Address bus width (12-64)
    parameter int AXI_DATA_WIDTH    = 32,     // Data bus width (must match)
    parameter int AXI_USER_WIDTH    = 1,      // User signal width (0-1024)
    parameter int SKID_DEPTH_AW     = 2,      // Address skid depth (2-8)
    parameter int SKID_DEPTH_W      = 4,      // Write data skid depth (2-8)
    parameter int SKID_DEPTH_B      = 4       // Response skid depth (2-8)
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // Slave AXI4 Write Interface (Input - Full Protocol)
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // Master AXI4-Lite Write Interface (Output - Simplified Protocol)
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_awaddr,
    output logic [2:0]                  m_axil_awprot,
    output logic                        m_axil_awvalid,
    input  logic                        m_axil_awready,

    output logic [AXI_DATA_WIDTH-1:0]   m_axil_wdata,
    output logic [STRB_WIDTH-1:0]       m_axil_wstrb,
    output logic                        m_axil_wvalid,
    input  logic                        m_axil_wready,

    input  logic [1:0]                  m_axil_bresp,
    input  logic                        m_axil_bvalid,
    output logic                        m_axil_bready
);
```

### Write Channel Synchronization

**Key Challenge:** AXI4-Lite requires AW and W to complete together, but AXI4 allows them to be independent.

**Solution:**
1. Track when AW has been sent for current beat (`r_aw_sent` flag)
2. Only consume W beat when:
   - AW is handshaking this cycle, OR
   - AW has already completed for this beat
3. Advance to next beat only when both AW and W complete

### Burst Decomposition Algorithm

**Single Beat (AWLEN = 0):**
1. Pass AW and W through immediately
2. Wait for B response
3. Return B with original ID

**Multi-Beat Burst (AWLEN > 0):**
1. Capture burst parameters (address, length, size, burst type, ID)
2. Enter burst decomposition FSM
3. For each beat (0 to AWLEN):
   - Issue AXIL4 AW with current address
   - Synchronize W data for this beat
   - Wait for both AW and W to complete
   - Collect B response
   - Increment address (INCR/WRAP) or keep same (FIXED)
   - Accumulate worst-case response
4. Return single B response with original ID after all beats complete

**FSM States:**
- **WR_IDLE** - Waiting for AW transaction, passthrough single beats
- **WR_BURST** - Processing multi-beat burst (beats 0 to AWLEN-1)
- **WR_LAST_BEAT** - Final beat of burst

### Example Waveforms

**2-Beat INCR Burst (32-bit, size=2):**
```
Cycle  AW/W               AXIL AW/W           AXIL B           AXI4 B
  0    addr=0x2000        -                   -                -
       len=1
       data0=0xAAAA
  1    -                  addr=0x2000         -                -
                          data=0xAAAA
  2    data1=0xBBBB       -                   resp=OKAY        -
  3    -                  addr=0x2004         -                -
                          data=0xBBBB
  4    -                  -                   resp=OKAY        resp=OKAY, id=X
```

Note: AXI4 B response waits until all AXIL4 B responses collected.

---

## Full Bidirectional Converter (axi4_to_axil4)

### Module Structure

The full converter is a wrapper that instantiates both read and write converters:

```systemverilog
module axi4_to_axil4 #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 4
) (
    // Clock and reset
    // Full AXI4 slave interface (all 5 channels)
    // Full AXI4-Lite master interface (all 5 channels)
);

    // Instantiate read converter
    axi4_to_axil4_rd #(...) u_rd_converter (...);

    // Instantiate write converter
    axi4_to_axil4_wr #(...) u_wr_converter (...);

endmodule
```

---

## Use Cases

### 1. AXI4 CPU to AXI4-Lite Peripherals

**Scenario:** CPU with full AXI4 master accessing simple peripherals with AXI4-Lite slaves.

**Benefits:**
- Peripherals can use simpler AXI4-Lite interface
- CPU can issue bursts for efficiency
- Converter handles burst decomposition transparently

### 2. DMA to Configuration Registers

**Scenario:** DMA controller with AXI4 accessing memory-mapped registers.

**Benefits:**
- Burst reads/writes decomposed automatically
- Register blocks don't need burst support
- Simplified peripheral design

### 3. Protocol Bridge in SoC

**Scenario:** Mixed protocol system with AXI4 fabric and AXI4-Lite peripherals.

**Benefits:**
- Clean protocol boundary
- Reduced complexity in peripheral design
- Easier IP integration

---

## Performance Characteristics

### Latency

**Single-Beat Transaction:**
- Read: 0 cycles (passthrough)
- Write: 0 cycles (passthrough)

**Multi-Beat Burst:**
- Read: 2 × N cycles (N = burst length)
- Write: 2 × N cycles + B response aggregation

### Throughput

**Single-Beat:**
- 100% throughput (back-to-back single transactions)

**Multi-Beat:**
- Limited by AXIL4 single-beat nature
- ~50% throughput (2 cycles per beat)

### Area

**Resource Usage:**
- Read converter: ~200 LUTs, ~100 FFs
- Write converter: ~250 LUTs, ~120 FFs
- Full converter: ~450 LUTs, ~220 FFs

---

## Integration Guidelines

### Parameter Selection

**Data Width:**
- Must match on both sides (no width conversion)
- Common values: 32, 64, 128, 256 bits

**ID Width:**
- Sized for expected number of outstanding transactions
- Typical: 4-8 bits (16-256 IDs)

**Skid Buffer Depths:**
- Increase for timing closure in high-frequency designs
- Default values usually sufficient

### Address Mapping

**Example System:**
```
AXI4 Master                AXI4-Lite Slave
(CPU/DMA)                  (Peripherals)
    |                           |
    |  64-bit addr              |  32-bit addr
    |  Bursts up to 256         |  Single beats only
    |                           |
    +--[axi4_to_axil4]----------+
```

**Address Truncation:**
- Upper bits dropped (64-bit → 32-bit)
- Ensure peripherals within 32-bit address space

### Error Handling

**Response Mapping:**
- AXIL4 OKAY → AXI4 OKAY
- AXIL4 SLVERR → AXI4 SLVERR

**Burst Error:**
- Any AXIL4 beat error → entire AXI4 burst marked with error
- Worst-case response returned

---

## Testing and Verification

### Test Coverage

**Functional Tests:**
- Single-beat read/write (passthrough verification)
- Multi-beat bursts (2, 4, 8, 16 beats)
- INCR burst type (address incrementing)
- FIXED burst type (same address)
- WRAP burst type (address wrapping)
- Error response propagation
- Back-to-back transactions
- Outstanding transaction handling

**Performance Tests:**
- Maximum throughput measurement
- Latency characterization
- Resource utilization

### Test Results

All 28 protocol converter tests passing:
- ✅ AXI4→AXIL4 Read: 7/7 tests
- ✅ AXI4→AXIL4 Write: 7/7 tests
- ✅ AXIL4→AXI4 Read: 7/7 tests (protocol upgrade)
- ✅ AXIL4→AXI4 Write: 7/7 tests (protocol upgrade)

---

## Limitations

1. **No Data Width Conversion** - Input and output data widths must match
2. **No Burst Optimization** - All bursts decomposed, no AXIL4 burst support
3. **Sequential Processing** - One AXIL4 beat at a time per burst
4. **Address Width** - Upper address bits dropped if AXIL4 narrower

---

## Related Modules

**Reverse Direction:**
- **axil4_to_axi4_rd.sv** - AXI4-Lite to AXI4 upgrade (read)
- **axil4_to_axi4_wr.sv** - AXI4-Lite to AXI4 upgrade (write)

**Data Width Conversion:**
- **axi4_dwidth_converter_rd.sv** - Width conversion with protocol
- **axi4_dwidth_converter_wr.sv** - Width conversion with protocol

**See Also:**
- Chapter 2: Data Width Converters
- [05_axil4_to_axi4.md](05_axil4_to_axi4.md) - Protocol upgrade specification

---

**Version:** 1.0
**Status:** Production Ready
**Last Updated:** 2025-11-06
**Test Status:** All tests passing (28/28)
