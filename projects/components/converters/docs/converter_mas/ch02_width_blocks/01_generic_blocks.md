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

# 2.1 Generic Building Blocks

The Converters component provides two generic building blocks for data width conversion: **axi_data_upsize** (narrow-to-wide) and **axi_data_dnsize** (wide-to-narrow). These modules are protocol-agnostic and can be composed into full AXI4 converters or used directly in custom designs.

## 2.1.1 Module Hierarchy

```
Generic Building Blocks
|
+-- axi_data_upsize.sv      # Narrow-to-Wide accumulator
|   +-- Accumulator buffer
|   +-- Beat counter
|   +-- Sideband packing
|
+-- axi_data_dnsize.sv      # Wide-to-Narrow splitter
    +-- Data buffer (single or dual)
    +-- Beat counter
    +-- Sideband extraction
    +-- Optional burst tracking
```

## 2.1.2 Design Philosophy

### Separation of Concerns

The generic blocks handle **only data manipulation**:
- Data packing/unpacking
- Sideband signal handling
- Valid/ready handshaking

They do **not** handle:
- Address manipulation
- Burst length adjustment
- ID tracking
- Protocol-specific signals (ARLEN, AWLEN, etc.)

This separation enables:
- Reuse in multiple contexts
- Simpler verification
- Cleaner composition into full converters

### Interface Pattern

Both modules use a consistent valid/ready interface:

```systemverilog
// Input (narrow for upsize, wide for dnsize)
input  logic                    i_valid,
output logic                    o_ready,
input  logic [DATA_WIDTH-1:0]   i_data,
input  logic [SB_WIDTH-1:0]     i_sideband,
input  logic                    i_last,      // Optional

// Output (wide for upsize, narrow for dnsize)
output logic                    o_valid,
input  logic                    i_ready,
output logic [DATA_WIDTH-1:0]   o_data,
output logic [SB_WIDTH-1:0]     o_sideband,
output logic                    o_last       // Optional
```

## 2.1.3 Width Ratio Calculation

Both modules calculate the width ratio at elaboration time:

```systemverilog
localparam int RATIO = WIDE_WIDTH / NARROW_WIDTH;
localparam int RATIO_LOG2 = $clog2(RATIO);

// Example: 64-bit to 512-bit
// RATIO = 512 / 64 = 8
// RATIO_LOG2 = 3
```

**Constraints:**
- `WIDE_WIDTH` must be an integer multiple of `NARROW_WIDTH`
- Minimum ratio: 2
- Maximum ratio: Typically 16 (limited by timing)

## 2.1.4 Sideband Modes

### Upsize Sideband Modes

| Mode | Parameter | Behavior | Use Case |
|------|-----------|----------|----------|
| Concatenate | `SB_OR_MODE=0` | Pack N narrow sidebands | WSTRB packing |
| OR | `SB_OR_MODE=1` | OR all narrow sidebands | Error aggregation |

: Table 2.1: Upsize Sideband Modes

**Concatenate Example (WSTRB):**
```
8 beats of 8-bit WSTRB → 1 beat of 64-bit WSTRB
[0]: 0xFF → output[7:0]   = 0xFF
[1]: 0xF0 → output[15:8]  = 0xF0
...
[7]: 0x0F → output[63:56] = 0x0F
```

**OR Example (Error flags):**
```
8 beats of error flags → 1 beat with any error
[0]: 0 → output = 0
[1]: 1 → output = 1 (error detected)
...
[7]: 0 → output remains 1
```

### Downsize Sideband Modes

| Mode | Parameter | Behavior | Use Case |
|------|-----------|----------|----------|
| Slice | `SB_BROADCAST=0` | Extract slice per beat | WSTRB extraction |
| Broadcast | `SB_BROADCAST=1` | Repeat full value | RRESP broadcast |

: Table 2.2: Downsize Sideband Modes

**Slice Example (WSTRB):**
```
1 beat of 64-bit WSTRB → 8 beats of 8-bit WSTRB
input = 0xFF_F0_..._0F
[0]: output = 0xFF (bits [7:0])
[1]: output = 0xF0 (bits [15:8])
...
[7]: output = 0x0F (bits [63:56])
```

**Broadcast Example (RRESP):**
```
1 beat of 2-bit RRESP → 8 beats of 2-bit RRESP
input = OKAY (2'b00)
[0-7]: output = OKAY (all beats get same response)
```

## 2.1.5 Performance Comparison

### Figure 2.1: Performance Comparison

![Performance Comparison](../assets/mermaid/performance_comparison.png)

| Module | Mode | Throughput | Latency | Area |
|--------|------|------------|---------|------|
| axi_data_upsize | Single | 100% | N cycles | 1x |
| axi_data_dnsize | Single | 80% | 1 cycle | 1x |
| axi_data_dnsize | Dual | 100% | 1 cycle | 2x |

: Table 2.3: Performance Comparison

**Why 80% for single-buffer downsize?**
- Single buffer requires one cycle gap between wide beats
- Wide beat loaded → N narrow beats output → gap → next wide beat
- Gap cycle = 1/(N+1) throughput loss
- For large N, approaches 100% but never reaches it

**Why 100% for dual-buffer downsize?**
- Ping-pong between two buffers
- While one buffer outputs, other loads
- No gap cycles required

## 2.1.6 Resource Utilization

### Upsize Resources (NARROW=64, WIDE=512)

```
Accumulator buffer:   512 bits (output register)
Beat counter:         3 bits (clog2(8))
Sideband accumulator: 64 bits (WSTRB)
Control logic:        ~50 LEs

Total: ~70-100 LEs, ~580 registers
```

### Downsize Resources (WIDE=512, NARROW=64)

**Single Buffer:**
```
Data buffer:          512 bits
Beat counter:         3 bits
Sideband logic:       ~20 LEs
Control logic:        ~50 LEs

Total: ~70-100 LEs, ~520 registers
```

**Dual Buffer:**
```
Data buffers (2x):    1024 bits
Beat counters (2x):   6 bits
Sideband logic:       ~40 LEs
Control logic:        ~100 LEs (ping-pong FSM)

Total: ~140-180 LEs, ~1040 registers
```

## 2.1.7 Integration Guidelines

### When to Use Generic Blocks

**Use directly when:**
- Building custom data pipelines
- Data width conversion without AXI4 protocol
- Simple valid/ready streaming interfaces

**Use full converters when:**
- Need AXI4 channel management (AW, W, B, AR, R)
- Burst length adjustment required
- ID tracking needed

### Composition Example

```systemverilog
// Full AXI4 write path composition
axi4_dwidth_converter_wr #(.S_DATA_WIDTH(64), .M_DATA_WIDTH(512)) u_wr (
    // This module internally instantiates:
    // 1. Address phase skid buffer
    // 2. axi_data_upsize for write data
    // 3. Response path passthrough
    // 4. Burst length adjustment logic
);
```

---

**Next:** [axi_data_upsize Module](02_axi_data_upsize.md)
