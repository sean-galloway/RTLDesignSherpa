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

# AXI4 Write Data Width Converter

**Module:** `axi4_dwidth_converter_wr.sv`
**Location:** `rtl/amba/axi4/`
**Status:** ✅ Production Ready

---

## Overview

The AXI4 Write Data Width Converter provides data width conversion for write-only AXI4 interfaces (AW, W, and B channels only). This specialized converter is optimized for unidirectional bridges where the read and write paths are separate, using skid buffers for timing closure and reducing resource usage compared to the full bidirectional converter.

### Key Features

- ✅ **Write-Only:** AW, W, and B channels only (no read channels)
- ✅ **Bidirectional Conversion:** Supports both upsize and downsize
- ✅ **Timing Closure:** Uses gaxi_skid_buffer on all channels
- ✅ **Resource Optimized:** Smaller than bidirectional converter
- ✅ **Burst Preservation:** Maintains burst semantics across conversion
- ✅ **WSTRB Handling:** Correct packing/unpacking of write strobes
- ✅ **Error Propagation:** Correctly forwards BRESP codes
- ✅ **Elastic Buffering:** Configurable skid buffer depths

---

## Module Architecture

### Upsize Mode (Narrow → Wide Writes)

```
Slave (Narrow)      Address       Write Path         Master (Wide)
   32-bit          Converter      Converter             128-bit
                 ┌────────────┐  ┌────────────┐
  s_axi_aw* ────►│ AW Skid    │  │            │
                 │ Buffer     ├─►│ WR Upsize  ├───────► m_axi_aw*
                 │            │  │            │
  s_axi_w*  ────►│ W Skid     │  │ - Pack 4→1 │
                 │ Buffer     ├─►│ - AWLEN/4  ├───────► m_axi_w*
                 │            │  │ - WSTRB    │
  s_axi_b*  ◄────│ B Skid     │  │            │
                 │ Buffer     │◄─┤            │◄──────── m_axi_b*
                 └────────────┘  └────────────┘

Example: 16 narrow W beats (32-bit) → 4 wide W beats (128-bit)
```

### Downsize Mode (Wide → Narrow Writes)

```
Slave (Wide)       Address       Write Path         Master (Narrow)
   128-bit        Converter      Converter              32-bit
                 ┌────────────┐  ┌────────────┐
  s_axi_aw* ────►│ AW Skid    │  │            │
                 │ Buffer     ├─►│ WR Downsize├───────► m_axi_aw*
                 │            │  │            │
  s_axi_w*  ────►│ W Skid     │  │ - Unpack   │
                 │ Buffer     ├─►│ - AWLEN×4  ├───────► m_axi_w*
                 │            │  │ - WSTRB    │
  s_axi_b*  ◄────│ B Skid     │  │            │
                 │ Buffer     │◄─┤            │◄──────── m_axi_b*
                 └────────────┘  └────────────┘

Example: 4 wide W beats (128-bit) → 16 narrow W beats (32-bit)
```

---

## Parameters

### Width Configuration

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| `S_AXI_DATA_WIDTH` | int | 32 | 32-256 | Slave interface data width (power of 2) |
| `M_AXI_DATA_WIDTH` | int | 128 | 32-256 | Master interface data width (power of 2) |
| `AXI_ID_WIDTH` | int | 8 | 1-16 | Transaction ID width |
| `AXI_ADDR_WIDTH` | int | 32 | 12-64 | Address bus width |
| `AXI_USER_WIDTH` | int | 1 | 0-1024 | User signal width |

### Skid Buffer Depths

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| `SKID_DEPTH_AW` | int | 2 | 2-8 | AW channel skid buffer depth |
| `SKID_DEPTH_W` | int | 4 | 2-8 | W channel skid buffer depth |
| `SKID_DEPTH_B` | int | 2 | 2-8 | B channel skid buffer depth |

### Calculated Parameters (Auto)

| Parameter | Calculation | Description |
|-----------|-------------|-------------|
| `S_STRB_WIDTH` | `S_AXI_DATA_WIDTH / 8` | Slave write strobe width |
| `M_STRB_WIDTH` | `M_AXI_DATA_WIDTH / 8` | Master write strobe width |
| `WIDTH_RATIO` | `MAX / MIN` | Data width ratio (2-16) |
| `UPSIZE` | `S < M` | 1 if upsizing, 0 if downsizing |
| `DOWNSIZE` | `S > M` | 1 if downsizing, 0 if upsizing |
| `PTR_WIDTH` | `$clog2(WIDTH_RATIO)` | Beat pointer width |

---

## Port Groups

### AXI4 Slave Write Interface

**Write Address Channel (AW):**
- `s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos, s_axi_awregion, s_axi_awuser, s_axi_awvalid, s_axi_awready`

**Write Data Channel (W):**
- `s_axi_wdata[S_AXI_DATA_WIDTH], s_axi_wstrb[S_STRB_WIDTH], s_axi_wlast, s_axi_wuser, s_axi_wvalid, s_axi_wready`

**Write Response Channel (B):**
- `s_axi_bid, s_axi_bresp, s_axi_buser, s_axi_bvalid, s_axi_bready`

### AXI4 Master Write Interface

**Write Address Channel (AW):**
- `m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst, m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos, m_axi_awregion, m_axi_awuser, m_axi_awvalid, m_axi_awready`

**Write Data Channel (W):**
- `m_axi_wdata[M_AXI_DATA_WIDTH], m_axi_wstrb[M_STRB_WIDTH], m_axi_wlast, m_axi_wuser, m_axi_wvalid, m_axi_wready`

**Write Response Channel (B):**
- `m_axi_bid, m_axi_bresp, m_axi_buser, m_axi_bvalid, m_axi_bready`

---

## Write Conversion Mechanics

### Upsize Write (Narrow → Wide)

```
Example: 32-bit → 128-bit (WIDTH_RATIO = 4)

Slave Write:                   Master Write:
AWLEN = 15 (16 beats)          AWLEN = 3 (4 beats)
AWSIZE = 3'b010 (4 bytes)      AWSIZE = 3'b100 (16 bytes)
AWADDR = 0x1000                AWADDR = 0x1000 (aligned)

W beats (32-bit):              W beats (128-bit):
Beat 0: wdata[31:0],   ───┐
        wstrb[3:0]         │
Beat 1: wdata[31:0],   ───┤
        wstrb[3:0]         ├──► Beat 0: wdata{b3,b2,b1,b0}
Beat 2: wdata[31:0],   ───┤             wstrb{s3,s2,s1,s0}
        wstrb[3:0]         │
Beat 3: wdata[31:0],   ───┘
        wstrb[3:0], WLAST=0

Beat 4-7: ...          ───┐
                           ├──► Beat 1: ...
Beat 8-11: ...         ───┤
                           ├──► Beat 2: ...
Beat 12-15: ...        ───┘
        WLAST=1 (beat 15)  ──► Beat 3: WLAST=1

BRESP: Single response from master → slave
```

### Downsize Write (Wide → Narrow)

```
Example: 128-bit → 32-bit (WIDTH_RATIO = 4)

Slave Write:                   Master Write:
AWLEN = 3 (4 beats)            AWLEN = 15 (16 beats)
AWSIZE = 3'b100 (16 bytes)     AWSIZE = 3'b010 (4 bytes)
AWADDR = 0x3000                AWADDR = 0x3000 (aligned)

W beats (128-bit):             W beats (32-bit):
Beat 0: wdata[127:0],  ───────► Beat 0: [31:0],   wstrb[3:0]
        wstrb[15:0]             Beat 1: [63:32],  wstrb[7:4]
                                Beat 2: [95:64],  wstrb[11:8]
                                Beat 3: [127:96], wstrb[15:12]

Beat 1: wdata[127:0],  ───────► Beat 4-7: ...
        wstrb[15:0]
Beat 2: wdata[127:0]   ───────► Beat 8-11: ...
Beat 3: wdata[127:0],  ───────► Beat 12-15: ...
        WLAST=1                         WLAST=1 (beat 15)

BRESP: Single response from master → slave
```

### WSTRB Handling

**Upsize:** Packs narrow WSTRB beats into wide WSTRB
```
32-bit WSTRB (4 beats):
Beat 0: 4'b1111  ────┐
Beat 1: 4'b1111  ────┤
Beat 2: 4'b0011  ────┼──► 128-bit WSTRB: 16'b1111_1111_1111_0011
Beat 3: 4'b1100  ────┘
```

**Downsize:** Unpacks wide WSTRB into narrow WSTRB beats
```
128-bit WSTRB: 16'b1111_0000_1111_0000
                    ↓
32-bit WSTRB (4 beats):
Beat 0: 4'b0000  (bits [3:0])
Beat 1: 4'b1111  (bits [7:4])
Beat 2: 4'b0000  (bits [11:8])
Beat 3: 4'b1111  (bits [15:12])
```

### BRESP Propagation

**Both Modes:** Single B channel response is forwarded unchanged
```
Master BRESP: OKAY → Slave BRESP: OKAY
Master BRESP: SLVERR → Slave BRESP: SLVERR
Master BRESP: DECERR → Slave BRESP: DECERR
```

---

## Usage Example

### Basic Write Upsize Converter (32-bit → 128-bit)

```systemverilog
axi4_dwidth_converter_wr #(
    // Width configuration
    .S_AXI_DATA_WIDTH   (32),     // Narrow slave
    .M_AXI_DATA_WIDTH   (128),    // Wide master
    .AXI_ID_WIDTH       (4),
    .AXI_ADDR_WIDTH     (32),
    .AXI_USER_WIDTH     (1),

    // Skid buffer depths
    .SKID_DEPTH_AW      (2),
    .SKID_DEPTH_W       (4),      // Moderate for burst accumulation
    .SKID_DEPTH_B       (2)
) u_wr_upsize (
    .aclk               (axi_clk),
    .aresetn            (axi_resetn),

    // Slave (narrow) interface
    .s_axi_awid         (cpu_awid),
    .s_axi_awaddr       (cpu_awaddr),
    .s_axi_awlen        (cpu_awlen),     // e.g., 15 (16 beats)
    .s_axi_awsize       (cpu_awsize),    // e.g., 3'b010 (4 bytes)
    .s_axi_awvalid      (cpu_awvalid),
    .s_axi_awready      (cpu_awready),
    // ... rest of AW signals

    .s_axi_wdata        (cpu_wdata),     // 32-bit
    .s_axi_wstrb        (cpu_wstrb),     // 4-bit
    .s_axi_wlast        (cpu_wlast),
    .s_axi_wvalid       (cpu_wvalid),
    .s_axi_wready       (cpu_wready),
    // ... rest of W signals

    .s_axi_bid          (cpu_bid),
    .s_axi_bresp        (cpu_bresp),
    .s_axi_bvalid       (cpu_bvalid),
    .s_axi_bready       (cpu_bready),

    // Master (wide) interface
    .m_axi_awid         (mem_awid),
    .m_axi_awaddr       (mem_awaddr),
    .m_axi_awlen        (mem_awlen),     // e.g., 3 (4 beats)
    .m_axi_awsize       (mem_awsize),    // e.g., 3'b100 (16 bytes)
    .m_axi_awvalid      (mem_awvalid),
    .m_axi_awready      (mem_awready),
    // ... rest of AW signals

    .m_axi_wdata        (mem_wdata),     // 128-bit
    .m_axi_wstrb        (mem_wstrb),     // 16-bit
    .m_axi_wlast        (mem_wlast),
    .m_axi_wvalid       (mem_wvalid),
    .m_axi_wready       (mem_wready),
    // ... rest of W signals

    .m_axi_bid          (mem_bid),
    .m_axi_bresp        (mem_bresp),
    .m_axi_bvalid       (mem_bvalid),
    .m_axi_bready       (mem_bready)
);

// Use case: CPU (32-bit write) → Memory controller (128-bit interface)
```

### Basic Write Downsize Converter (128-bit → 32-bit)

```systemverilog
axi4_dwidth_converter_wr #(
    // Width configuration
    .S_AXI_DATA_WIDTH   (128),    // Wide slave
    .M_AXI_DATA_WIDTH   (32),     // Narrow master
    .AXI_ID_WIDTH       (4),
    .AXI_ADDR_WIDTH     (32),

    // Skid buffer depths
    .SKID_DEPTH_AW      (2),
    .SKID_DEPTH_W       (4),      // Moderate for unpacking
    .SKID_DEPTH_B       (2)
) u_wr_downsize (
    .aclk               (axi_clk),
    .aresetn            (axi_resetn),

    // Slave (wide) interface
    .s_axi_awid         (wide_awid),
    .s_axi_awaddr       (wide_awaddr),
    .s_axi_awlen        (wide_awlen),     // e.g., 3 (4 beats)
    .s_axi_awsize       (wide_awsize),    // e.g., 3'b100 (16 bytes)
    // ... rest of slave signals

    .s_axi_wdata        (wide_wdata),     // 128-bit
    .s_axi_wstrb        (wide_wstrb),     // 16-bit
    // ... rest of slave W signals

    // Master (narrow) interface
    .m_axi_awid         (periph_awid),
    .m_axi_awaddr       (periph_awaddr),
    .m_axi_awlen        (periph_awlen),   // e.g., 15 (16 beats)
    .m_axi_awsize       (periph_awsize),  // e.g., 3'b010 (4 bytes)
    // ... rest of master signals

    .m_axi_wdata        (periph_wdata),   // 32-bit
    .m_axi_wstrb        (periph_wstrb),   // 4-bit
    // ... rest of master W signals
);

// Use case: Interconnect (128-bit) → Peripheral (32-bit write-only)
```

---

## Design Notes

### Write-Only Use Cases

**When to Use Write-Only Converter:**
- Unidirectional write-only bridges
- Separate read and write data paths
- Write-through caches
- Write-only peripherals (configuration registers, command FIFOs)

**Resource Savings vs. Full Converter:**
- No AR/R channel buffers (saves ~40% resources)
- Simpler control logic
- Lower latency (no read path dependencies)

### Skid Buffer vs. FIFO

**Why Skid Buffers:**
- Optimized for timing closure (single-cycle latency)
- Smaller area than FIFOs for shallow depths
- Sufficient for write path elasticity

**Depth Guidelines:**
- **SKID_DEPTH_AW:** 2 (default) - sufficient for most cases
- **SKID_DEPTH_W:** 4 (default) - handles moderate bursts
- **SKID_DEPTH_B:** 2 (default) - single-beat responses

**Increase SKID_DEPTH_W for:**
- Large burst lengths (AWLEN > 16)
- High backpressure from master
- Width ratio > 4

### Address Alignment

Same alignment requirements as [axi4_dwidth_converter](axi4_dwidth_converter.md):

**Upsize:** Slave addresses must be aligned to master data width
```
32→128 upsize: AWADDR must be 16-byte aligned (bottom 4 bits = 0)
```

**Downsize:** No alignment restrictions

### Burst Length Calculation

**Upsize:**
```
Master AWLEN = (Slave AWLEN + 1) / WIDTH_RATIO - 1
Master AWSIZE = Slave AWSIZE + $clog2(WIDTH_RATIO)
```

**Downsize:**
```
Master AWLEN = (Slave AWLEN + 1) * WIDTH_RATIO - 1
Master AWSIZE = Slave AWSIZE - $clog2(WIDTH_RATIO)
```

See [axi4_dwidth_converter](axi4_dwidth_converter.md) for detailed examples.

### Performance Characteristics

**Throughput (Upsize):**
- Accumulation latency: WIDTH_RATIO-1 cycles per wide beat
- Example (WIDTH_RATIO=4): 3-cycle latency for first wide W beat

**Throughput (Downsize):**
- Unpacking latency: 1 cycle per narrow beat
- Full wide beat unpacked in consecutive cycles

**Comparison to Full Converter:**
- ~20-30% lower latency (no read path overhead)
- ~40% resource savings (no read channel buffers)

### WSTRB Validation

**Critical:** Ensure WSTRB is valid for all write beats
```systemverilog
// Upsize: Each narrow beat must have valid WSTRB
always_comb begin
    if (s_axi_wvalid) begin
        assert (s_axi_wstrb != '0) else
            $error("WSTRB cannot be all-zeros when WVALID=1");
    end
end
```

**Partial Writes:** WSTRB controls byte lane enables
```
32-bit write with WSTRB=4'b0011:
  - Byte lanes [1:0] written
  - Byte lanes [3:2] unchanged
```

---

## Related Modules

### Companion Converters
- **[axi4_dwidth_converter](axi4_dwidth_converter.md)** - Full bidirectional converter (AW/W/B/AR/R)
- **[axi4_dwidth_converter_rd](axi4_dwidth_converter_rd.md)** - Read-only data width conversion

### Core Modules
- **[axi4_master_wr](axi4_master_wr.md)** - AXI4 write master
- **[axi4_slave_wr](axi4_slave_wr.md)** - AXI4 write slave

### Used Components
- **[gaxi_skid_buffer](../gaxi/gaxi_skid_buffer.md)** - Elastic buffering with timing closure

---

## References

### Specifications
- ARM IHI 0022E: AMBA AXI Protocol Specification (AXI4)
- Chapter 11: Data Width Conversion

### Source Code
- RTL: `rtl/amba/axi4/axi4_dwidth_converter_wr.sv`
- Tests: `val/amba/test_axi4_dwidth_converter_wr.py`
- Framework: `bin/CocoTBFramework/components/axi4/`

### Documentation
- Architecture: [RTLAmba Overview](../overview.md)
- AXI4 Index: [README.md](README.md)

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXI4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
