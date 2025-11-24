# 2.7 Protocol Conversion

Protocol Conversion enables the bridge to interface with slaves using different bus protocols. While the bridge internally uses AXI4, it can convert to simpler protocols like APB (Advanced Peripheral Bus) for low-bandwidth peripheral access.

## 2.7.1 Purpose and Function

Protocol conversion performs the following critical functions:

1. **Protocol Translation**: Converts AXI4 transactions to target protocol (e.g., APB)
2. **Handshake Mapping**: Translates ready/valid to protocol-specific handshakes
3. **Burst Decomposition**: Breaks AXI bursts into single-beat target transactions
4. **Response Mapping**: Converts protocol-specific responses back to AXI responses
5. **Timing Adaptation**: Handles different timing requirements between protocols

## 2.7.2 Supported Protocols

### Current Support (Phase 2)

**AXI4 (Native)**:
- Full AXI4 protocol
- No conversion required
- Maximum performance

**AXI4-Lite (Master-Side)**:
- Simplified AXI4 subset
- Single-beat transactions only (ARLEN=0, AWLEN=0)
- Converts to full AXI4 for crossbar
- Common for control/status registers

**APB (Slave-Side)**:
- APB3 and APB4 support
- For low-bandwidth peripherals
- Simplified handshaking

### Future Support (Phase 2+)

- **AHB**: Advanced High-performance Bus
- **Wishbone**: Open-source bus standard
- **Custom**: User-defined protocols

## 2.7.3 Conversion Architecture Overview

```
        MASTER SIDE                CROSSBAR              SLAVE SIDE
        
    AXI4-Lite Master          Full AXI4 Fabric         APB Peripheral
           |                        |                          |
           |                        |                          |
    [AXI4-Lite]                [Full AXI4]              [Full AXI4]
           |                        |                          |
           v                        |                          v
    ┌──────────────┐                |                  ┌──────────────┐
    │ AXI4-Lite → │                |                  │  AXI4 → APB  │
    │  AXI4       │                |                  │  Converter   │
    │  Adapter    │                |                  │              │
    └──────────────┘                |                  └──────────────┘
           |                        |                          |
           v                        v                          v
       [Full AXI4]──────────> [Full AXI4] ────────────────>[APB]
                     To Crossbar               To Peripheral
```

## 2.7.4 Block Diagram

![Protocol Conversion Architecture](../assets/graphviz/protocol_conversion_apb.svg)

*Figure 2.7: Protocol conversion showing AXI4 to APB conversion with state machine, burst decomposition, and response mapping.*

## 2.7.5 AXI4-Lite to AXI4 Conversion (Master-Side)

### AXI4-Lite Protocol Overview

AXI4-Lite is a simplified subset of AXI4 designed for simple control/status register access:

```
Key Differences from Full AXI4:
- FIXED burst length: ARLEN/AWLEN always = 0 (single beat)
- FIXED burst size: No SIZE field, always full data width
- FIXED burst type: No BURST field, always INCR
- NO exclusive access: No LOCK support
- NO unaligned transfers: Address must be aligned
- Simpler ID: Typically 1-4 bits (fewer outstanding transactions)

Similarities to AXI4:
- Same 5 channels: AR, R, AW, W, B
- Same valid/ready handshaking
- Same response codes: OKAY, SLVERR, DECERR, EXOKAY
- Same data widths: 32 or 64 bits typically
```

### Conversion Requirements

To adapt AXI4-Lite masters to the full AXI4 crossbar, the adapter must:

1. **Add Missing Signals**: Provide default values for burst-related signals
2. **Validate Constraints**: Ensure single-beat assumption holds
3. **Pass-Through Simplicity**: Most signals connect directly

### Signal Mapping

```systemverilog
// AXI4-Lite to AXI4 Signal Mapping

// AR Channel (Read Address)
// AXI4-Lite Input          AXI4 Crossbar Output
axi4lite_arvalid      →     axi4_arvalid
axi4lite_arready      ←     axi4_arready
axi4lite_araddr       →     axi4_araddr
axi4lite_arprot       →     axi4_arprot
axi4lite_arid (opt)   →     axi4_arid

// Added by adapter (constants):
                            axi4_arlen    = 8'h00      // Always 1 beat
                            axi4_arsize   = log2(DW/8) // Full width
                            axi4_arburst  = 2'b01      // INCR
                            axi4_arlock   = 1'b0       // No lock
                            axi4_arcache  = 4'b0000    // Device non-buf
                            axi4_arqos    = 4'h0       // No QoS
                            axi4_arregion = 4'h0       // Region 0

// R Channel (Read Data)
// AXI4 Crossbar Input      AXI4-Lite Output
axi4_rvalid           →     axi4lite_rvalid
axi4_rready           ←     axi4lite_rready
axi4_rdata            →     axi4lite_rdata
axi4_rresp            →     axi4lite_rresp
axi4_rid (opt)        →     axi4lite_rid (opt)

// Discarded by adapter:
axi4_rlast                  // Always 1 for single beat

// AW Channel (Write Address)
axi4lite_awvalid      →     axi4_awvalid
axi4lite_awready      ←     axi4_awready
axi4lite_awaddr       →     axi4_awaddr
axi4lite_awprot       →     axi4_awprot
axi4lite_awid (opt)   →     axi4_awid

// Added by adapter:
                            axi4_awlen    = 8'h00
                            axi4_awsize   = log2(DW/8)
                            axi4_awburst  = 2'b01
                            axi4_awlock   = 1'b0
                            axi4_awcache  = 4'b0000
                            axi4_awqos    = 4'h0
                            axi4_awregion = 4'h0

// W Channel (Write Data)
axi4lite_wvalid       →     axi4_wvalid
axi4lite_wready       ←     axi4_wready
axi4lite_wdata        →     axi4_wdata
axi4lite_wstrb        →     axi4_wstrb

// Added by adapter:
                            axi4_wlast    = 1'b1       // Always last

// B Channel (Write Response)
axi4_bvalid           →     axi4lite_bvalid
axi4_bready           ←     axi4lite_bready
axi4_bresp            →     axi4lite_bresp
axi4_bid (opt)        →     axi4lite_bid (opt)
```

### Implementation

The AXI4-Lite adapter is extremely simple, primarily providing constant values:

```systemverilog
// AXI4-Lite to AXI4 Adapter (simplified)
module axi4lite_to_axi4_adapter #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH = 4         // Optional, often 0 for AXI4-Lite
) (
    input logic clk,
    input logic rst_n,
    
    // AXI4-Lite Master Interface
    input  logic                     lite_arvalid,
    output logic                     lite_arready,
    input  logic [ADDR_WIDTH-1:0]    lite_araddr,
    input  logic [2:0]               lite_arprot,
    input  logic [ID_WIDTH-1:0]      lite_arid,    // Optional
    
    output logic                     lite_rvalid,
    input  logic                     lite_rready,
    output logic [DATA_WIDTH-1:0]    lite_rdata,
    output logic [1:0]               lite_rresp,
    output logic [ID_WIDTH-1:0]      lite_rid,     // Optional
    
    input  logic                     lite_awvalid,
    output logic                     lite_awready,
    input  logic [ADDR_WIDTH-1:0]    lite_awaddr,
    input  logic [2:0]               lite_awprot,
    input  logic [ID_WIDTH-1:0]      lite_awid,    // Optional
    
    input  logic                     lite_wvalid,
    output logic                     lite_wready,
    input  logic [DATA_WIDTH-1:0]    lite_wdata,
    input  logic [DATA_WIDTH/8-1:0]  lite_wstrb,
    
    output logic                     lite_bvalid,
    input  logic                     lite_bready,
    output logic [1:0]               lite_bresp,
    output logic [ID_WIDTH-1:0]      lite_bid,     // Optional
    
    // Full AXI4 Crossbar Interface
    output logic                     axi4_arvalid,
    input  logic                     axi4_arready,
    output logic [ADDR_WIDTH-1:0]    axi4_araddr,
    output logic [7:0]               axi4_arlen,
    output logic [2:0]               axi4_arsize,
    output logic [1:0]               axi4_arburst,
    output logic                     axi4_arlock,
    output logic [3:0]               axi4_arcache,
    output logic [2:0]               axi4_arprot,
    output logic [3:0]               axi4_arqos,
    output logic [3:0]               axi4_arregion,
    output logic [ID_WIDTH-1:0]      axi4_arid,
    
    input  logic                     axi4_rvalid,
    output logic                     axi4_rready,
    input  logic [DATA_WIDTH-1:0]    axi4_rdata,
    input  logic [1:0]               axi4_rresp,
    input  logic                     axi4_rlast,
    input  logic [ID_WIDTH-1:0]      axi4_rid,
    
    // ... (AW, W, B channels similar)
);

    // AR Channel: Pass-through with constants
    assign axi4_arvalid  = lite_arvalid;
    assign lite_arready  = axi4_arready;
    assign axi4_araddr   = lite_araddr;
    assign axi4_arprot   = lite_arprot;
    assign axi4_arid     = lite_arid;
    
    // Constants for single-beat burst
    assign axi4_arlen    = 8'h00;                    // 1 beat
    assign axi4_arsize   = $clog2(DATA_WIDTH/8);     // Full width
    assign axi4_arburst  = 2'b01;                    // INCR
    assign axi4_arlock   = 1'b0;                     // No lock
    assign axi4_arcache  = 4'b0000;                  // Device non-buf
    assign axi4_arqos    = 4'h0;                     // No QoS
    assign axi4_arregion = 4'h0;                     // Region 0
    
    // R Channel: Pass-through, ignore rlast
    assign lite_rvalid = axi4_rvalid;
    assign axi4_rready = lite_rready;
    assign lite_rdata  = axi4_rdata;
    assign lite_rresp  = axi4_rresp;
    assign lite_rid    = axi4_rid;
    // axi4_rlast ignored (always 1 for single beat)
    
    // AW Channel: Similar to AR
    assign axi4_awvalid  = lite_awvalid;
    assign lite_awready  = axi4_awready;
    assign axi4_awaddr   = lite_awaddr;
    assign axi4_awprot   = lite_awprot;
    assign axi4_awid     = lite_awid;
    assign axi4_awlen    = 8'h00;
    assign axi4_awsize   = $clog2(DATA_WIDTH/8);
    assign axi4_awburst  = 2'b01;
    assign axi4_awlock   = 1'b0;
    assign axi4_awcache  = 4'b0000;
    assign axi4_awqos    = 4'h0;
    assign axi4_awregion = 4'h0;
    
    // W Channel: Pass-through, add wlast
    assign axi4_wvalid = lite_wvalid;
    assign lite_wready = axi4_wready;
    assign axi4_wdata  = lite_wdata;
    assign axi4_wstrb  = lite_wstrb;
    assign axi4_wlast  = 1'b1;                       // Always last
    
    // B Channel: Pass-through
    assign lite_bvalid = axi4_bvalid;
    assign axi4_bready = lite_bready;
    assign lite_bresp  = axi4_bresp;
    assign lite_bid    = axi4_bid;

endmodule
```

### Resource Utilization

**AXI4-Lite Adapter Resources**:
```
Logic Elements:  ~50-100 LEs (minimal, mostly wiring)
Registers:       ~50 regs (if skid buffers added)
Block RAM:       0

Breakdown:
- Signal pass-through: ~20 LEs (buffering)
- Constant generation: ~10 LEs
- Optional skid buffers: ~50 regs (for timing)

Note: Most implementations are purely combinatorial wire
      assignments with optional pipeline registers.
```

### Performance Impact

**Latency**:
- **Zero-latency** (combinatorial) if no pipeline stages
- **1-2 cycles** if skid buffers added for timing
- No protocol conversion overhead

**Throughput**:
- **1 transaction per cycle** (same as native AXI4)
- No degradation for single-beat transactions
- Limited by AXI4-Lite's single-beat constraint

### Configuration

```toml
[[masters]]
name = "control_processor"
protocol = "axi4lite"          # Specify simplified protocol
channels = "rw"                # Full read-write
arid_width = 0                 # Often no ID in AXI4-Lite
awid_width = 0
addr_width = 32
data_width = 32                # Typically 32 or 64 bits
```

### Common Issues and Debug

**Issue 1: Burst Detected on AXI4-Lite**
```
Symptom: ARLEN/AWLEN != 0 on AXI4-Lite interface
Cause: Master not properly configured as AXI4-Lite
Check: Verify master only issues single-beat transactions
```

**Issue 2: Unaligned Addresses**
```
Symptom: ARADDR/AWADDR not aligned to data width
Cause: AXI4-Lite requires full-width aligned access
Check: Address[log2(DW/8)-1:0] should be zero
```

**Issue 3: rlast/wlast Handling**
```
Symptom: Master expects rlast/wlast but doesn't have them
Cause: True AXI4-Lite interface omits these signals
Solution: Adapter provides wlast=1 to crossbar, strips rlast
```

## 2.7.6 AXI4 to APB Conversion (Slave-Side)

### APB Protocol Overview

APB is a simple, low-power bus protocol:

```
Characteristics:
- Single address phase
- Single data phase
- No burst support (one transfer per operation)
- Minimal logic
- Low power consumption
- Suitable for peripherals: UARTs, timers, GPIOs
```

### APB Signals

```
Address Phase:
  PADDR[N-1:0]  - Address bus
  PSEL          - Slave select
  PENABLE       - Enable (2nd cycle of transfer)
  PWRITE        - Write direction (1=write, 0=read)
  
Data Phase (Write):
  PWDATA[N-1:0] - Write data
  PSTRB[N/8-1:0]- Write strobes (APB4 only)
  
Data Phase (Read):
  PRDATA[N-1:0] - Read data
  
Response:
  PREADY        - Slave ready (can extend transfer)
  PSLVERR       - Slave error (APB3+)
```

### APB State Machine

APB requires a 2-phase handshake:

```
IDLE:
  - Wait for AXI request (ARVALID or AWVALID)
  - PSEL = 0, PENABLE = 0
  
SETUP:
  - Assert PSEL = 1
  - Drive PADDR, PWRITE, PWDATA (if write)
  - PENABLE = 0
  - Duration: 1 cycle
  
ACCESS:
  - Assert PENABLE = 1
  - Wait for PREADY = 1
  - Capture PRDATA (if read) or PSLVERR
  - Can extend multiple cycles if PREADY = 0
  
Complete:
  - De-assert PSEL, PENABLE
  - Return to IDLE or SETUP (if more beats)
```

### Read Transaction Conversion

**AXI4 Read**:
```
Cycle 0: ARVALID=1, ARADDR=0x100, ARLEN=3 (4 beats)
Cycle 1: ARREADY=1
Cycles 2-5: R beats returning
```

**Converted to APB** (4 separate APB reads):
```
Beat 0:
  Cycle 0: PSEL=1, PENABLE=0, PADDR=0x100, PWRITE=0 (SETUP)
  Cycle 1: PSEL=1, PENABLE=1, wait PREADY (ACCESS)
  Cycle 2: PREADY=1, capture PRDATA → First R beat

Beat 1:
  Cycle 3: PSEL=1, PENABLE=0, PADDR=0x104 (SETUP)
  Cycle 4: PSEL=1, PENABLE=1, wait PREADY (ACCESS)
  Cycle 5: PREADY=1, capture PRDATA → Second R beat
  
... (beats 2 and 3 similar)
```

**Latency**: 2-3 cycles per beat (SETUP + ACCESS + ready)

### Write Transaction Conversion

**AXI4 Write**:
```
Cycle 0: AWVALID=1, AWADDR=0x200, AWLEN=1 (2 beats)
Cycle 1: AWREADY=1
Cycle 1: WVALID=1, WDATA=0xAAAA_BBBB, WLAST=0
Cycle 2: WREADY=1
Cycle 2: WVALID=1, WDATA=0xCCCC_DDDD, WLAST=1
Cycle 3: WREADY=1
Cycle 4: BVALID=1, BRESP=OKAY
```

**Converted to APB** (2 separate APB writes):
```
Beat 0:
  Cycle 0: PSEL=1, PENABLE=0, PADDR=0x200, PWRITE=1, PWDATA=0xAAAA_BBBB
  Cycle 1: PSEL=1, PENABLE=1, wait PREADY
  Cycle 2: PREADY=1 → First write complete

Beat 1:
  Cycle 3: PSEL=1, PENABLE=0, PADDR=0x204, PWRITE=1, PWDATA=0xCCCC_DDDD
  Cycle 4: PSEL=1, PENABLE=1, wait PREADY
  Cycle 5: PREADY=1 → Second write complete, return B
```

### Burst Handling

APB does not support bursts, so:

```
AXI Burst: AWLEN = 15 (16 beats)
→ 16 separate APB transfers
→ Address increments per AWBURST type:
   - INCR: Addr += SIZE each beat
   - WRAP: Wrapping within boundary
   - FIXED: Same address each beat
```

### Response Mapping

```
APB → AXI Response Translation:

PREADY=1, PSLVERR=0 → RRESP/BRESP = 2'b00 (OKAY)
PREADY=1, PSLVERR=1 → RRESP/BRESP = 2'b10 (SLVERR)

Timeout (PREADY stuck at 0):
  After N cycles → RRESP/BRESP = 2'b11 (DECERR)
```

## 2.7.5 Implementation

### AXI4-to-APB Converter FSM

```systemverilog
// Simplified AXI4-to-APB converter
typedef enum logic [2:0] {
    IDLE,
    AR_SETUP,
    AR_ACCESS,
    AW_SETUP,
    W_ACCESS,
    B_RESPONSE
} state_t;

state_t state, next_state;

always_ff @(posedge clk) begin
    if (!rst_n) state <= IDLE;
    else state <= next_state;
end

always_comb begin
    next_state = state;
    
    case (state)
        IDLE: begin
            if (arvalid) next_state = AR_SETUP;
            else if (awvalid) next_state = AW_SETUP;
        end
        
        AR_SETUP: begin
            next_state = AR_ACCESS;  // 1 cycle SETUP
        end
        
        AR_ACCESS: begin
            if (pready) begin
                if (more_beats) next_state = AR_SETUP;  // Next beat
                else next_state = IDLE;
            end
        end
        
        AW_SETUP: begin
            if (wvalid) next_state = W_ACCESS;
        end
        
        W_ACCESS: begin
            if (pready) begin
                if (!wlast) next_state = AW_SETUP;  // Next beat
                else next_state = B_RESPONSE;
            end
        end
        
        B_RESPONSE: begin
            if (bready) next_state = IDLE;
        end
    endcase
end

// APB signal generation
assign psel = (state != IDLE);
assign penable = (state == AR_ACCESS || state == W_ACCESS);
assign pwrite = (state == AW_SETUP || state == W_ACCESS);
```

### Address Generation

```systemverilog
// Address increment for burst
logic [ADDR_WIDTH-1:0] current_addr;
logic [7:0] beat_count;

always_ff @(posedge clk) begin
    if (state == IDLE) begin
        current_addr <= arvalid ? araddr : awaddr;
        beat_count <= 0;
    end else if ((state == AR_ACCESS || state == W_ACCESS) && pready) begin
        beat_count <= beat_count + 1;
        
        case (burst_type)
            2'b01: current_addr <= current_addr + (1 << size);  // INCR
            2'b10: current_addr <= wrap_address(current_addr);  // WRAP
            2'b00: current_addr <= current_addr;                // FIXED
        endcase
    end
end

assign paddr = current_addr;
```

## 2.7.6 Resource Utilization

### APB Converter Resources

**Per APB Slave Interface**:
```
Logic Elements:  ~400 LEs
Registers:       ~150 regs
Block RAM:       0

Breakdown:
- FSM control:           ~100 LEs, ~20 regs
- Address generation:    ~80 LEs, ~40 regs
- Burst counter:         ~50 LEs, ~20 regs
- Response accumulation: ~80 LEs, ~30 regs
- Data path MUX:         ~90 LEs, ~40 regs
```

### Scaling

Adding APB slaves:
- Linear scaling: +~400 LEs per APB slave
- Shared address decoder logic
- Independent per-slave FSMs

## 2.7.7 Timing Characteristics

### Latency

**APB Read Latency** (per beat):
```
Best case: 2 cycles (SETUP + ACCESS with PREADY=1)
Typical: 3-5 cycles (if slave extends with PREADY=0)
Worst case: Configurable timeout (e.g., 1000 cycles)

For 8-beat AXI burst:
  Total: 8 × 3 = 24 cycles typical
```

**APB Write Latency** (per beat):
```
Similar to read: 2-5 cycles per beat
```

### Throughput

**Severely Limited**:
```
APB: ~0.3-0.5 transactions/cycle (due to 2-3 cycle protocol)
AXI4: 1 transaction/cycle (burst mode)

APB suitable only for low-bandwidth peripherals
```

## 2.7.8 Configuration Parameters

### Protocol Conversion Configuration (TOML)

```toml
[[slaves]]
name = "uart_peripheral"
protocol = "apb"            # "axi4", "apb", "ahb" (future)
base_address = 0xF000_0000
size = 0x1000
data_width = 32
apb_timeout = 1000          # Cycles before timeout error

[[slaves]]
name = "ddr_memory"
protocol = "axi4"           # Native, no conversion
base_address = 0x8000_0000
size = 0x4000_0000
data_width = 64
```

## 2.7.9 Debug and Observability

### Recommended Debug Signals

```
APB Converter:
- FSM state
- APB phase (SETUP, ACCESS)
- Beat counter (progress through burst)
- PREADY timeout counter
- Response accumulation (for burst)

APB Bus:
- PSEL, PENABLE, PWRITE
- PADDR, PWDATA, PRDATA
- PREADY, PSLVERR
```

### Common Issues and Debug

**Symptom**: APB slave not responding (timeout)  
**Check**:
- PREADY signal (stuck at 0?)
- APB slave clock/reset
- PSEL assertion
- Timeout threshold

**Symptom**: Data corruption on APB  
**Check**:
- SETUP phase duration (should be 1 cycle)
- PENABLE assertion timing
- Data sampling on correct cycle

**Symptom**: Burst to APB takes too long  
**Check**:
- Burst length (consider limiting ARLEN/AWLEN)
- APB slave response time (PREADY)
- Alternative: Use AXI4 slave instead

## 2.7.10 Verification Considerations

### Test Scenarios

1. **Single APB Transfer**:
```
- AXI ARLEN=0 (1 beat) → 1 APB read
- Verify SETUP → ACCESS sequence
- Check PREADY handling
```

2. **APB Burst Decomposition**:
```
- AXI AWLEN=7 (8 beats) → 8 APB writes
- Verify address increment
- Check each beat completes before next
```

3. **APB PREADY Extension**:
```
- Slave holds PREADY=0 for N cycles
- Verify converter waits
- Check no data corruption
```

4. **APB Error Response**:
```
- Slave asserts PSLVERR
- Verify mapped to AXI SLVERR
- Check error propagated to master
```

5. **APB Timeout**:
```
- Slave never asserts PREADY
- Verify timeout after N cycles
- Check DECERR response
```

## 2.7.11 Performance Considerations

### When to Use APB

**Good Use Cases**:
- Low-speed peripherals (UART, GPIO, timers)
- Infrequent accesses
- Simple register interfaces
- Power-sensitive designs

**Poor Use Cases**:
- High-bandwidth devices
- Burst-intensive masters
- Performance-critical paths
- Memory interfaces

### APB vs. AXI4 Comparison

```
Feature          APB              AXI4
Complexity       Simple           Complex
Throughput       Low (~0.3/cyc)   High (1/cyc burst)
Latency/beat     2-5 cycles       1 cycle
Burst Support    No               Yes (up to 256)
Resources        ~400 LEs         Native (no converter)
Power            Very low         Moderate
Use Case         Peripherals      Memory, DMA
```

## 2.7.12 Mixed Protocol Bridges

### Example Configuration

```toml
# Bridge with mixed protocols
[bridge]
num_masters = 2
num_slaves = 3

[[masters]]
name = "cpu"
protocol = "axi4"

[[masters]]
name = "dma"
protocol = "axi4"

[[slaves]]
name = "ddr_memory"
protocol = "axi4"          # High bandwidth

[[slaves]]
name = "sram"
protocol = "axi4"          # Medium bandwidth

[[slaves]]
name = "peripherals"
protocol = "apb"           # Low bandwidth, simple
```

### Routing Optimization

```
CPU → DDR Memory: AXI4-to-AXI4 (native, fast)
CPU → Peripherals: AXI4-to-APB (converted, slower)
DMA → SRAM: AXI4-to-AXI4 (native, fast)
DMA → Peripherals: AXI4-to-APB (rare, acceptable slowdown)
```

## 2.7.13 Master-Side vs Slave-Side Conversion

### Comparison

```
Feature              Master-Side (AXI4-Lite)    Slave-Side (APB)
──────────────────────────────────────────────────────────────────
Complexity           Very Simple                Complex
Resource Usage       ~50-100 LEs                ~400 LEs
Latency Added        0-1 cycles                 2-5 cycles/beat
Throughput Impact    None                       Severe (3x slower)
Burst Handling       Single beat only           Decompose to singles
State Machine        None (combinatorial)       Multi-state FSM
Buffering Required   Optional (timing)          Essential
Use Case             Control registers          Peripherals
```

### When to Use Each

**AXI4-Lite Master Adapter**:
- Simple control/status register interfaces
- Low-complexity masters (MCUs, simple CPUs)
- Minimal resource overhead acceptable
- No burst performance needed

**APB Slave Converter**:
- Legacy peripheral integration
- Very simple slave devices (GPIO, timers)
- Low-bandwidth acceptable
- Power optimization critical

## 2.7.14 Future Protocol Support

### Planned Features

**AXI4-Lite**:
- Subset of AXI4
- No burst support (ALEN=0 always)
- Simpler than full AXI4
- Common for control registers

**AHB (AMBA High-performance Bus)**:
- More capable than APB
- Pipeline support
- Burst support
- Suitable for moderate-bandwidth peripherals

**Wishbone**:
- Open-source bus standard
- Common in FPGA designs
- Multiple addressing modes
- Configurable data widths

### Under Consideration

- **Custom Protocol**: User-defined through configuration
- **Stream Interface**: AXI4-Stream for data streaming
- **PCIe TLP**: For PCIe endpoint integration
- **CHI**: ARM's Coherent Hub Interface

## 2.7.14 Best Practices

### Design Recommendations

1. **Limit APB Burst Lengths**: Configure masters to use short bursts to APB slaves
2. **Proper Timeouts**: Set realistic timeout values for APB slaves
3. **Protocol Matching**: Use native AXI4 where possible, APB only when necessary
4. **Address Map Planning**: Group APB peripherals together for efficient decoding
5. **Width Matching**: Match APB data width to peripheral requirements

### Performance Tips

```
Inefficient: 256-beat AXI burst → APB
  256 beats × 3 cyc/beat = 768 cycles

Better: Limit to 4-beat bursts → APB
  64 bursts of 4 beats each
  Still long, but more manageable

Best: Use AXI4-Lite slave for registers
  No burst, but native protocol
```

---

**Related Sections**:
- Section 2.3: Crossbar Core (protocol integration point)
- Section 3.3: Slave Port Interface (APB signal specifications)
- Chapter 4: Programming (configuring protocol conversion)
- Appendix A: Generator Deep Dive (protocol converter generation)
