# AXI Data Upsize/Dnsize Generic Modules - Usage Guide

**Version:** 1.0
**Created:** 2025-10-25
**Purpose:** Document usage of generic axi_data_upsize and axi_data_dnsize modules

---

## Overview

Two generic, reusable modules for AXI data width conversion:

- **axi_data_upsize.sv**: Narrow→wide accumulator (combine multiple narrow beats into one wide beat)
- **axi_data_dnsize.sv**: Wide→narrow splitter (split one wide beat into multiple narrow beats)

These modules are **protocol-agnostic** and can be used with:
- AXI4 Write Channel (W data)
- AXI4 Read Channel (R data)
- AXI-Stream data paths
- Custom handshake protocols with valid/ready flow control

---

## Module: axi_data_upsize

### Purpose
Accumulates multiple narrow-width data beats into a single wide-width data beat.

### Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| NARROW_WIDTH | int | 32 | Input data width (bits) |
| WIDE_WIDTH | int | 128 | Output data width (bits) |
| NARROW_SB_WIDTH | int | 0 | Narrow sideband width (0=none) |
| WIDE_SB_WIDTH | int | 0 | Wide sideband width (0=none) |
| SB_OR_MODE | bit | 0 | 0=concatenate sideband, 1=OR sideband |

**Constraints:**
- WIDE_WIDTH must be > NARROW_WIDTH
- WIDE_WIDTH must be integer multiple of NARROW_WIDTH
- WIDTH_RATIO = WIDE_WIDTH / NARROW_WIDTH must be >= 2

### Ports

```systemverilog
module axi_data_upsize #(...) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // Narrow Input (from master or slave)
    input  logic                        narrow_valid,
    output logic                        narrow_ready,
    input  logic [NARROW_WIDTH-1:0]     narrow_data,
    input  logic [NARROW_SB_WIDTH-1:0]  narrow_sideband,
    input  logic                        narrow_last,

    // Wide Output (to slave or master)
    output logic                        wide_valid,
    input  logic                        wide_ready,
    output logic [WIDE_WIDTH-1:0]       wide_data,
    output logic [WIDE_SB_WIDTH-1:0]    wide_sideband,
    output logic                        wide_last
);
```

### Behavior

**Accumulation Process:**
1. Accepts narrow beats via valid/ready handshake
2. Accumulates data into internal buffer at position determined by beat counter
3. Accumulates sideband based on SB_OR_MODE:
   - SB_OR_MODE=0 (concatenate): Packs sideband bits into wide sideband
   - SB_OR_MODE=1 (OR): Bitwise-OR all narrow sideband values
4. Completes when:
   - Beat counter reaches WIDTH_RATIO, OR
   - narrow_last is asserted (early termination)
5. Presents wide beat on output

**Sideband Modes:**
- **Concatenate (SB_OR_MODE=0)**: For WSTRB signals
  - Example: 4 narrow beats with WSTRB[3:0] = {0x3, 0x5, 0x7, 0x9}
  - Result: wide WSTRB[15:0] = {0x9, 0x7, 0x5, 0x3} = 0x9753
- **OR (SB_OR_MODE=1)**: For RRESP signals
  - Example: 4 narrow beats with RRESP[1:0] = {OK, SLVERR, OK, OK}
  - Result: wide RRESP[1:0] = SLVERR (any error propagates)

**Early Termination:**
- If narrow_last asserted before counter reaches WIDTH_RATIO:
  - Immediately completes accumulation
  - wide_last asserted on output
  - Partial data beats are zero-padded

### Usage Example 1: AXI4 Write UPSIZE (32→128)

```systemverilog
// Convert 32-bit W channel to 128-bit W channel
// Concatenate WSTRB (4 bits → 16 bits)

axi_data_upsize #(
    .NARROW_WIDTH    (32),
    .WIDE_WIDTH      (128),
    .NARROW_SB_WIDTH (4),   // WSTRB for 32-bit
    .WIDE_SB_WIDTH   (16),  // WSTRB for 128-bit
    .SB_OR_MODE      (0)    // Concatenate WSTRB
) u_w_upsize (
    .aclk            (aclk),
    .aresetn         (aresetn),

    // From narrow master W channel
    .narrow_valid    (s_axi_wvalid),
    .narrow_ready    (s_axi_wready),
    .narrow_data     (s_axi_wdata),
    .narrow_sideband (s_axi_wstrb),
    .narrow_last     (s_axi_wlast),

    // To wide slave W channel
    .wide_valid      (int_wvalid),
    .wide_ready      (int_wready),
    .wide_data       (int_wdata),
    .wide_sideband   (int_wstrb),
    .wide_last       (int_wlast)
);
```

**Operation:**
- Accepts 4 narrow W beats (32 bits each)
- Accumulates into 1 wide W beat (128 bits)
- WSTRB concatenated: 4 narrow WSTRB[3:0] → 1 wide WSTRB[15:0]
- WLAST on 4th narrow beat → WLAST on wide beat

### Usage Example 2: AXI4 Read DOWNSIZE (128→32)

```systemverilog
// Convert 128-bit R channel to 32-bit R channel
// OR RRESP (2 bits each, error propagates)

axi_data_upsize #(
    .NARROW_WIDTH    (32),
    .WIDE_WIDTH      (128),
    .NARROW_SB_WIDTH (2),   // RRESP for each beat
    .WIDE_SB_WIDTH   (2),   // RRESP for wide beat
    .SB_OR_MODE      (1)    // OR RRESP (error propagates)
) u_r_upsize (
    .aclk            (aclk),
    .aresetn         (aresetn),

    // From narrow slave R channel
    .narrow_valid    (int_rvalid),
    .narrow_ready    (int_rready),
    .narrow_data     (int_rdata),
    .narrow_sideband (int_rresp),
    .narrow_last     (int_rlast),

    // To wide master R channel
    .wide_valid      (m_axi_rvalid),
    .wide_ready      (m_axi_rready),
    .wide_data       (m_axi_rdata),
    .wide_sideband   (m_axi_rresp),
    .wide_last       (m_axi_rlast)
);
```

**Operation:**
- Accepts 4 narrow R beats (32 bits each)
- Accumulates into 1 wide R beat (128 bits)
- RRESP OR'd: Any SLVERR or DECERR propagates to wide RRESP
- RLAST on 4th narrow beat → RLAST on wide beat

---

## Module: axi_data_dnsize

### Purpose
Splits a single wide-width data beat into multiple narrow-width data beats.

### Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| WIDE_WIDTH | int | 128 | Input data width (bits) |
| NARROW_WIDTH | int | 32 | Output data width (bits) |
| WIDE_SB_WIDTH | int | 0 | Wide sideband width (0=none) |
| NARROW_SB_WIDTH | int | 0 | Narrow sideband width (0=none) |
| SB_BROADCAST | bit | 1 | 1=broadcast sideband, 0=slice sideband |
| TRACK_BURSTS | bit | 0 | 1=track bursts for LAST, 0=simple mode |
| BURST_LEN_WIDTH | int | 8 | Burst length counter width |
| **DUAL_BUFFER** | **int** | **0** | **1=dual buffer (100% throughput, 2× area), 0=single buffer (80% throughput)** |

**Constraints:**
- NARROW_WIDTH must be < WIDE_WIDTH
- WIDE_WIDTH must be integer multiple of NARROW_WIDTH
- WIDTH_RATIO = WIDE_WIDTH / NARROW_WIDTH must be >= 2

### Ports

```systemverilog
module axi_data_dnsize #(...) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // Burst Control (only if TRACK_BURSTS=1)
    input  logic [BURST_LEN_WIDTH-1:0]  burst_len,
    input  logic                        burst_start,

    // Wide Input (from slave or master)
    input  logic                        wide_valid,
    output logic                        wide_ready,
    input  logic [WIDE_WIDTH-1:0]       wide_data,
    input  logic [WIDE_SB_WIDTH-1:0]    wide_sideband,
    input  logic                        wide_last,

    // Narrow Output (to master or slave)
    output logic                        narrow_valid,
    input  logic                        narrow_ready,
    output logic [NARROW_WIDTH-1:0]     narrow_data,
    output logic [NARROW_SB_WIDTH-1:0]  narrow_sideband,
    output logic                        narrow_last
);
```

### Behavior

**Splitting Process:**
1. Accepts wide beat via valid/ready handshake
2. Buffers data internally
3. Extracts narrow slices based on beat pointer
4. Handles sideband based on SB_BROADCAST:
   - SB_BROADCAST=1 (broadcast): All narrow beats get same sideband value
   - SB_BROADCAST=0 (slice): Extract appropriate sideband slice
5. Generates narrow_last based on mode:
   - Simple mode: narrow_last on final beat IF wide_last was set
   - Burst tracking mode: narrow_last on final beat of entire burst

**Sideband Modes:**
- **Broadcast (SB_BROADCAST=1)**: For RRESP signals
  - All narrow beats get same wide RRESP value
  - Example: wide RRESP=SLVERR → all 4 narrow beats get RRESP=SLVERR
- **Slice (SB_BROADCAST=0)**: For WSTRB signals
  - Each narrow beat gets appropriate WSTRB slice
  - Example: wide WSTRB[15:0]=0x9753 → narrow beats get {0x3, 0x5, 0x7, 0x9}

**Burst Tracking Mode (TRACK_BURSTS=1):**
- Used for AXI4 Read UPSIZE to generate correct RLAST
- burst_start pulse with burst_len (encoded as beats-1) starts tracking
- Counts narrow beats emitted
- Asserts narrow_last on final beat of entire burst
- Example: burst_len=7 (8 beats), WIDTH_RATIO=4
  - Need 2 wide beats to produce 8 narrow beats
  - narrow_last asserted on 8th narrow beat (not on 4th)

### Usage Example 1: AXI4 Write DOWNSIZE (128→32)

```systemverilog
// Convert 128-bit W channel to 32-bit W channel
// Slice WSTRB (16 bits → 4 bits per beat)

axi_data_dnsize #(
    .WIDE_WIDTH      (128),
    .NARROW_WIDTH    (32),
    .WIDE_SB_WIDTH   (16),  // WSTRB for 128-bit
    .NARROW_SB_WIDTH (4),   // WSTRB for 32-bit
    .SB_BROADCAST    (0),   // Slice WSTRB
    .TRACK_BURSTS    (0)    // Simple mode (use wide_last)
) u_w_dnsize (
    .aclk            (aclk),
    .aresetn         (aresetn),

    // Burst control not used in simple mode
    .burst_len       ('0),
    .burst_start     (1'b0),

    // From wide slave W channel
    .wide_valid      (int_wvalid),
    .wide_ready      (int_wready),
    .wide_data       (int_wdata),
    .wide_sideband   (int_wstrb),
    .wide_last       (int_wlast),

    // To narrow master W channel
    .narrow_valid    (m_axi_wvalid),
    .narrow_ready    (m_axi_wready),
    .narrow_data     (m_axi_wdata),
    .narrow_sideband (m_axi_wstrb),
    .narrow_last     (m_axi_wlast)
);
```

**Operation:**
- Accepts 1 wide W beat (128 bits)
- Splits into 4 narrow W beats (32 bits each)
- WSTRB sliced: wide WSTRB[15:0] → 4 narrow WSTRB[3:0] slices
- WLAST on wide beat → WLAST on 4th narrow beat

### Usage Example 2: AXI4 Read UPSIZE (128→32) with Burst Tracking

```systemverilog
// Convert 128-bit R channel to 32-bit R channel
// Broadcast RRESP (all narrow beats get same value)
// Track burst length to generate correct RLAST

axi_data_dnsize #(
    .WIDE_WIDTH      (128),
    .NARROW_WIDTH    (32),
    .WIDE_SB_WIDTH   (2),   // RRESP
    .NARROW_SB_WIDTH (2),   // RRESP
    .SB_BROADCAST    (1),   // Broadcast RRESP
    .TRACK_BURSTS    (1),   // Enable burst tracking
    .BURST_LEN_WIDTH (8)    // AXI4 ARLEN width
) u_r_dnsize (
    .aclk            (aclk),
    .aresetn         (aresetn),

    // Burst control from AR channel
    .burst_len       (s_axi_arlen),
    .burst_start     (s_axi_arvalid && s_axi_arready),

    // From wide master R channel
    .wide_valid      (m_axi_rvalid),
    .wide_ready      (m_axi_rready),
    .wide_data       (m_axi_rdata),
    .wide_sideband   (m_axi_rresp),
    .wide_last       (m_axi_rlast),

    // To narrow slave R channel
    .narrow_valid    (s_axi_rvalid),
    .narrow_ready    (s_axi_rready),
    .narrow_data     (s_axi_rdata),
    .narrow_sideband (s_axi_rresp),
    .narrow_last     (s_axi_rlast)
);
```

**Operation:**
- Burst length from AR channel (e.g., ARLEN=7 means 8 beats)
- Accepts wide R beats (128 bits each)
- Splits into narrow R beats (32 bits each)
- RRESP broadcast: All 4 narrow beats from one wide beat get same RRESP
- RLAST generation:
  - Not based on wide_rlast
  - Based on burst tracking: asserted on final narrow beat of entire burst
  - Example: ARLEN=7 (8 narrow beats), WIDTH_RATIO=4
    - Consume 2 wide R beats
    - Produce 8 narrow R beats
    - RLAST asserted on 8th narrow beat

---

## Integration in AXI4 Width Converters

### Write Converter Structure

```
                    +-------------------+
S_AXI (narrow) ---->| AW Channel Skid   |----> int_aw (narrow)
  32-bit            +-------------------+

                    +-------------------+
                    | W Channel Skid    |
                    +-------------------+
                            |
                            v
                    +-------------------+
                    | axi_data_upsize OR|  <-- Generic Module
                    | axi_data_dnsize   |
                    +-------------------+
                            |
                            v
                    +-------------------+
                    | W Channel Skid    |----> M_AXI (wide)
                    +-------------------+        128-bit

                    +-------------------+
                    | B Channel Skid    |<---- int_b (narrow)
                    +-------------------+
```

**Upsize (32→128):** Uses axi_data_upsize with SB_OR_MODE=0 (concatenate WSTRB)
**Downsize (128→32):** Uses axi_data_dnsize with SB_BROADCAST=0 (slice WSTRB)

### Read Converter Structure

```
                    +-------------------+
S_AXI (narrow) ---->| AR Channel Skid   |----> int_ar (wide)
  32-bit            +-------------------+

                    +-------------------+
                    | R Channel Skid    |
                    +-------------------+
                            |
                            v
                    +-------------------+
                    | axi_data_upsize OR|  <-- Generic Module
                    | axi_data_dnsize   |
                    +-------------------+
                            |
                            v
                    +-------------------+
                    | R Channel Skid    |<---- M_AXI (wide)
                    +-------------------+        128-bit
```

**Upsize (32→128):** Uses axi_data_dnsize with SB_BROADCAST=1, TRACK_BURSTS=1 (broadcast RRESP, track burst)
**Downsize (128→32):** Uses axi_data_upsize with SB_OR_MODE=1 (OR RRESP)

---

## Testing

### Test Infrastructure

**Testbench Classes:**
- `axi_data_upsize_tb.py`: Comprehensive testbench for upsize module
- `axi_data_dnsize_tb.py`: Comprehensive testbench for dnsize module

**Pytest Test Runners:**
- `test_axi_data_upsize.py`: Parameterized tests with 6 configurations
- `test_axi_data_dnsize.py`: Parameterized tests with 8 configurations

**Test Scenarios:**
1. Basic operation: Verify correct data accumulation/splitting
2. Sideband handling: Verify concatenate/slice/OR/broadcast modes
3. LAST propagation: Verify correct LAST generation
4. Burst tracking: Verify correct LAST with burst tracking mode
5. Backpressure: Verify correct operation with stalls
6. Continuous streaming: Verify zero-bubble operation

### Running Tests

```bash
# Navigate to test directory
cd projects/components/converters/dv/tests

# Run upsize tests
pytest test_axi_data_upsize.py -v

# Run dnsize tests
pytest test_axi_data_dnsize.py -v

# Run specific configuration
pytest test_axi_data_upsize.py::test_axi_data_upsize[32to128_wstrb_concat] -v

# Run with waveforms
pytest test_axi_data_dnsize.py::test_axi_data_dnsize[128to32_rresp_burst_track] -v --waves
```

---

## Parameter Selection Guide

### Choosing SB_OR_MODE (axi_data_upsize)

| Use Case | SB_OR_MODE | Rationale |
|----------|------------|-----------|
| Write UPSIZE WSTRB | 0 (concatenate) | Pack narrow WSTRB bits into wide WSTRB |
| Read DOWNSIZE RRESP | 1 (OR) | Propagate any error response to wide beat |

### Choosing SB_BROADCAST (axi_data_dnsize)

| Use Case | SB_BROADCAST | Rationale |
|----------|--------------|-----------|
| Write DOWNSIZE WSTRB | 0 (slice) | Extract appropriate WSTRB bits for each narrow beat |
| Read UPSIZE RRESP | 1 (broadcast) | All narrow beats get same response |

### Choosing TRACK_BURSTS (axi_data_dnsize)

| Use Case | TRACK_BURSTS | Rationale |
|----------|--------------|-----------|
| Write DOWNSIZE | 0 (simple) | Use wide_last directly for narrow_last |
| Read UPSIZE | 1 (tracking) | Generate correct RLAST based on ARLEN |

---

## Simulation Assertions

Both modules include comprehensive assertions for protocol checking:

1. **Valid stability**: Valid must not drop before ready asserted
2. **Pointer bounds**: Beat pointer must stay within valid range
3. **Burst tracking**: Beat count must not exceed total beats (dnsize only)
4. **Parameter constraints**: Verify WIDTH_RATIO >= 2, valid multiples

Enable assertions with `-D SIMULATION` compile flag.

---

## Synthesis Considerations

- **Clock domain**: Single clock domain (aclk)
- **Reset**: Active-low asynchronous reset (aresetn)
- **Combinational paths**: Minimal, only for handshake logic
- **Register count**: Scales with WIDE_WIDTH and WIDTH_RATIO
- **Timing closure**: Use gaxi_skid_buffer on module boundaries if needed

---

## Future Enhancements

Potential additions for future versions:
1. Support for non-power-of-2 width ratios
2. Partial beat support with byte enable masking
3. Performance counters (beat count, stall cycles)
4. AXI USER signal propagation

---

**Version History:**
- v1.0 (2025-10-25): Initial creation

**Author:** RTL Design Sherpa
**Last Review:** 2025-10-25
