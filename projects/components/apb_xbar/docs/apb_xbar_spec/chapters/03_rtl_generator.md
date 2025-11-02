# APB Crossbar RTL Generator

**Component:** APB Crossbar (MxN Interconnect)
**Version:** 1.0
**Status:** Production Ready

---

## Overview

The APB Crossbar uses **parametric RTL generation** to create custom MxN configurations. While several pre-generated variants exist (1to1, 2to1, 1to4, 2to4, thin), the Python-based generator enables creation of any arbitrary MxN crossbar up to 16x16.

**Philosophy:**
- Pre-generated variants for common use cases (fast integration)
- Python generator for custom configurations (flexibility)
- Template-based code generation (consistency)
- Built from proven components (quality)

---

## Generator Architecture

### Two-Level Structure

```
projects/components/apb_xbar/
├── bin/
│   └── generate_xbars.py              ← Convenience wrapper script
│
└── (repo root)/bin/rtl_generators/amba/
    └── apb_xbar_generator.py          ← Core generator engine
```

**Why Two Files?**
1. **Core Generator** (`apb_xbar_generator.py`): Reusable library function
   - Can be imported by other scripts
   - Contains `generate_apb_xbar()` function
   - Located in central `bin/rtl_generators/` directory

2. **Convenience Wrapper** (`generate_xbars.py`): Project-specific script
   - Easy command-line interface
   - Pre-configured for standard variants
   - Located in project `bin/` directory

---

## Quick Start

### Generate Standard Variants (1:1, 2:1, 1:4, 2:4)

```bash
cd projects/components/apb_xbar/bin/
python generate_xbars.py
```

**Output:**
```
Generating 1-to-1 crossbar...
  ✅ apb_xbar_1to1.sv
Generating 2-to-1 crossbar...
  ✅ apb_xbar_2to1.sv
Generating 1-to-4 crossbar...
  ✅ apb_xbar_1to4.sv
Generating 2-to-4 crossbar...
  ✅ apb_xbar_2to4.sv

✅ Generated 4 crossbar variants
```

### Generate Custom Variant

```bash
cd projects/components/apb_xbar/bin/
python generate_xbars.py --masters 3 --slaves 6
```

**Output:**
```
Generating 3-to-6 crossbar...
✅ Generated apb_xbar_3to6.sv
```

### Generate with Custom Base Address

```bash
cd projects/components/apb_xbar/bin/
python generate_xbars.py --masters 4 --slaves 8 --base-addr 0x80000000
```

**Output:**
```
Generating 4-to-8 crossbar...
✅ Generated apb_xbar_4to8.sv

Address Map:
  Slave 0: [0x80000000, 0x8000FFFF]
  Slave 1: [0x80010000, 0x8001FFFF]
  Slave 2: [0x80020000, 0x8002FFFF]
  ...
  Slave 7: [0x80070000, 0x8007FFFF]
```

---

## Command-Line Interface

### Full Options

```bash
python generate_xbars.py [OPTIONS]
```

**Options:**

| Option | Short | Type | Default | Description |
|--------|-------|------|---------|-------------|
| `--masters` | `-m` | int | None | Number of master interfaces (1-16) |
| `--slaves` | `-s` | int | None | Number of slave interfaces (1-16) |
| `--base-addr` | `-b` | hex | 0x10000000 | Base address for slave address map |
| `--help` | `-h` | - | - | Show help message |

**Rules:**
- If neither `--masters` nor `--slaves` specified → Generate all standard variants
- If only one specified → Error (must specify both)
- If both specified → Generate custom variant

### Examples

**Example 1: Generate All Standard Variants**
```bash
python generate_xbars.py
```

**Example 2: Generate 3x6 Crossbar**
```bash
python generate_xbars.py --masters 3 --slaves 6
```

**Example 3: Generate 5x10 Crossbar with Custom Base**
```bash
python generate_xbars.py -m 5 -s 10 -b 0xA0000000
```

**Example 4: Show Help**
```bash
python generate_xbars.py --help
```

---

## Generated Code Structure

### Template Components

The generator creates a complete SystemVerilog module with:

1. **Header with Address Map**
```systemverilog
// 3-to-6 APB crossbar with address decoding and arbitration
// 3 masters to 6 slaves using apb_slave and apb_master modules
//
// Address Map (same for all masters):
//   Slave 0: [0x10000000, 0x1000FFFF]
//   Slave 1: [0x10010000, 0x1001FFFF]
//   Slave 2: [0x10020000, 0x1002FFFF]
//   Slave 3: [0x10030000, 0x1003FFFF]
//   Slave 4: [0x10040000, 0x1004FFFF]
//   Slave 5: [0x10050000, 0x1005FFFF]
```

2. **Module Declaration with Parameters**
```systemverilog
module apb_xbar_3to6 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'h10000000
) (
    // Clock and Reset
    input  logic                  pclk,
    input  logic                  presetn,

    // Master 0-2 APB interfaces
    // Slave 0-5 APB interfaces
);
```

3. **Internal Signal Declarations**
```systemverilog
    // Command/Response interfaces for master 0-2 apb_slave
    logic m0_cmd_valid, m0_cmd_ready, m0_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] m0_cmd_paddr;
    // ... (full cmd/rsp bus for each master)

    // Command/Response interfaces for slave 0-5 apb_master
    logic s0_cmd_valid, s0_cmd_ready, s0_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] s0_cmd_paddr;
    // ... (full cmd/rsp bus for each slave)
```

4. **Master-Side apb_slave Instantiations**
```systemverilog
    // Master 0 apb_slave
    apb_slave #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_m0_slave (
        .pclk(pclk),
        .presetn(presetn),
        // APB interface
        .apb_PSEL(m0_apb_PSEL),
        .apb_PENABLE(m0_apb_PENABLE),
        // ... (full APB connections)
        // cmd/rsp interface
        .cmd_valid(m0_cmd_valid),
        .cmd_ready(m0_cmd_ready),
        // ... (full cmd/rsp connections)
    );

    // Master 1, 2 apb_slave instances...
```

5. **Address Decode Logic**
```systemverilog
    // Address decode for each master
    logic [M-1:0][N-1:0] m_to_s_req;  // Request matrix

    // Master 0 address decode
    always_comb begin
        m_to_s_req[0] = '0;
        if (m0_cmd_valid) begin
            logic [ADDR_WIDTH-1:0] offset = m0_cmd_paddr - BASE_ADDR;
            logic [3:0] slave_idx = offset[19:16];
            case (slave_idx)
                4'd0: m_to_s_req[0][0] = 1'b1;
                4'd1: m_to_s_req[0][1] = 1'b1;
                // ... (case for each slave)
            endcase
        end
    end

    // Master 1, 2 address decode...
```

6. **Per-Slave Arbitration Logic**
```systemverilog
    // Arbitration for each slave
    logic [N-1:0][M-1:0] s_grant;  // Grant matrix
    logic [N-1:0][$clog2(M)-1:0] s_arb_priority;  // Round-robin priority

    // Slave 0 arbiter (round-robin among M masters)
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            s_arb_priority[0] <= '0;
            s_grant[0] <= '0;
        end else begin
            // Round-robin arbitration logic
            // Priority rotation after each grant
        end
    end

    // Slave 1-5 arbiters...
```

7. **Response Routing Logic**
```systemverilog
    // Route responses back to requesting masters
    always_comb begin
        // Track which master initiated each transaction
        // Route PRDATA/PSLVERR back to correct master
    end
```

8. **Slave-Side apb_master Instantiations**
```systemverilog
    // Slave 0 apb_master
    apb_master #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_s0_master (
        .pclk(pclk),
        .presetn(presetn),
        // cmd/rsp interface
        .cmd_valid(s0_cmd_valid),
        .cmd_ready(s0_cmd_ready),
        // ... (full cmd/rsp connections)
        // APB interface
        .apb_PSEL(s0_apb_PSEL),
        .apb_PENABLE(s0_apb_PENABLE),
        // ... (full APB connections)
    );

    // Slave 1-5 apb_master instances...
```

9. **Module End**
```systemverilog
endmodule : apb_xbar_3to6
```

---

## Generator Algorithm

### Step-by-Step Process

**1. Validate Parameters**
```python
if M < 1 or M > 16:
    raise ValueError(f"Number of masters must be 1-16, got {M}")
if N < 1 or N > 16:
    raise ValueError(f"Number of slaves must be 1-16, got {N}")
```

**2. Calculate Derived Parameters**
```python
slave_addr_bits = max(1, math.ceil(math.log2(N)))  # Bits for slave index
strb_width = data_width // 8                        # Byte strobe width
module_name = f"apb_xbar_{M}to{N}"                 # Module name
```

**3. Generate Address Map Documentation**
```python
for s in range(N):
    addr_offset = s * 0x10000  # 64KB per slave
    addr_start = base_addr + addr_offset
    addr_end = addr_start + 0xFFFF
    # Generate comment: Slave S: [START, END]
```

**4. Generate Module Declaration**
- Parameters: ADDR_WIDTH, DATA_WIDTH, STRB_WIDTH, BASE_ADDR
- Ports: Clock, reset
- Master interfaces: M × full APB interface
- Slave interfaces: N × full APB interface

**5. Generate Internal Signals**
- Master cmd/rsp buses: M sets
- Slave cmd/rsp buses: N sets
- Request matrix: [M][N]
- Grant matrix: [N][M]
- Priority counters: [N]

**6. Instantiate Master-Side Components**
```python
for m in range(M):
    # Generate apb_slave instance
    # Connect APB interface to external master m
    # Connect cmd/rsp to internal buses
```

**7. Generate Address Decode Logic**
```python
for m in range(M):
    # For each master, decode address to slave index
    # offset = paddr - BASE_ADDR
    # slave_idx = offset[19:16]  # Upper 4 bits
    # Set m_to_s_req[m][slave_idx] = 1
```

**8. Generate Arbitration Logic**
```python
for s in range(N):
    # For each slave, arbitrate among M masters
    # Round-robin: priority rotates after each grant
    # Grant persistence: hold until transaction completes
```

**9. Generate Response Routing**
```python
# Track transaction source (which master)
# Route responses back to originating master
```

**10. Instantiate Slave-Side Components**
```python
for s in range(N):
    # Generate apb_master instance
    # Connect cmd/rsp from internal buses
    # Connect APB interface to external slave s
```

**11. Write Generated Code**
```python
with open(output_file, 'w') as f:
    f.write(generated_code)
```

---

## Code Generation Patterns

### Loop-Based Generation

**Master Interfaces:**
```python
for m in range(M):
    code += f"    // Master {m} APB interface\n"
    code += f"    input  logic m{m}_apb_PSEL,\n"
    code += f"    input  logic m{m}_apb_PENABLE,\n"
    # ... (all APB signals for master m)
```

**Slave Interfaces:**
```python
for s in range(N):
    code += f"    // Slave {s} APB interface\n"
    code += f"    output logic s{s}_apb_PSEL,\n"
    code += f"    output logic s{s}_apb_PENABLE,\n"
    # ... (all APB signals for slave s)
```

### String Formatting

**Hex Values:**
```python
code += f"    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = {addr_width}'h{base_addr:08X}\n"
# Example: 32'h10000000
```

**Address Map Comments:**
```python
addr_start = base_addr + (s * 0x10000)
code += f"//   Slave {s}: [0x{addr_start:08X}, 0x{addr_start + 0xFFFF:08X}]\n"
# Example: Slave 2: [0x10020000, 0x1002FFFF]
```

---

## Customization Examples

### Example 1: Large SoC with 10 Peripherals

**Scenario:** CPU + DMA need to access 10 peripherals

**Command:**
```bash
python generate_xbars.py --masters 2 --slaves 10
```

**Generated File:** `apb_xbar_2to10.sv`

**Address Map:**
```
Slave 0:  0x10000000 - 0x1000FFFF (UART0)
Slave 1:  0x10010000 - 0x1001FFFF (UART1)
Slave 2:  0x10020000 - 0x1002FFFF (GPIO)
Slave 3:  0x10030000 - 0x1003FFFF (I2C)
Slave 4:  0x10040000 - 0x1004FFFF (SPI)
Slave 5:  0x10050000 - 0x1005FFFF (Timer0)
Slave 6:  0x10060000 - 0x1006FFFF (Timer1)
Slave 7:  0x10070000 - 0x1007FFFF (PWM)
Slave 8:  0x10080000 - 0x1008FFFF (ADC)
Slave 9:  0x10090000 - 0x1009FFFF (Watchdog)
```

**LOC:** ~2500 lines (estimated)

### Example 2: Multi-CPU System

**Scenario:** 4 CPUs accessing shared peripheral bus with 4 slaves

**Command:**
```bash
python generate_xbars.py --masters 4 --slaves 4
```

**Generated File:** `apb_xbar_4to4.sv`

**Benefits:**
- Fair arbitration among 4 CPUs
- Each slave independently arbitrated
- Maximum throughput when CPUs access different slaves

**LOC:** ~1600 lines (estimated)

### Example 3: Memory-Mapped I/O Region

**Scenario:** Single master accessing I/O region at 0xA0000000

**Command:**
```bash
python generate_xbars.py --masters 1 --slaves 8 --base-addr 0xA0000000
```

**Generated File:** `apb_xbar_1to8.sv`

**Address Map:**
```
Slave 0:  0xA0000000 - 0xA000FFFF
Slave 1:  0xA0010000 - 0xA001FFFF
...
Slave 7:  0xA0070000 - 0xA007FFFF
```

---

## Using Generated Modules

### Integration Example

```systemverilog
// Generated file: apb_xbar_3to6.sv

module my_soc (
    input  logic clk,
    input  logic rst_n,
    // ... other interfaces
);

    // Instantiate 3x6 crossbar
    apb_xbar_3to6 #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .BASE_ADDR(32'h10000000)  // Can override at instantiation
    ) u_periph_xbar (
        .pclk(clk),
        .presetn(rst_n),

        // Connect 3 masters (CPU, DMA, Debug)
        .m0_apb_PSEL(cpu_apb_psel),
        .m0_apb_PENABLE(cpu_apb_penable),
        // ... (full CPU APB interface)

        .m1_apb_PSEL(dma_apb_psel),
        .m1_apb_PENABLE(dma_apb_penable),
        // ... (full DMA APB interface)

        .m2_apb_PSEL(debug_apb_psel),
        .m2_apb_PENABLE(debug_apb_penable),
        // ... (full Debug APB interface)

        // Connect 6 slaves (UART, GPIO, Timer, SPI, I2C, ADC)
        .s0_apb_PSEL(uart_psel),
        .s0_apb_PENABLE(uart_penable),
        // ... (full UART APB interface)

        .s1_apb_PSEL(gpio_psel),
        // ... (remaining slaves)
    );

endmodule : my_soc
```

### Parameter Override

```systemverilog
// Use different base address at instantiation
apb_xbar_3to6 #(
    .BASE_ADDR(32'h80000000)  // Override default 0x10000000
) u_mmio_xbar (
    // ... connections
);
// Slaves now at: 0x80000000, 0x80010000, 0x80020000, ...
```

---

## Generator Limitations and Future Work

### Current Limitations

1. **Fixed 64KB Per Slave**
   - Cannot customize individual slave region sizes
   - Workaround: Use multiple crossbars with different BASE_ADDR

2. **Max 16x16 Configuration**
   - Practical limit due to arbitration complexity
   - Workaround: Hierarchical crossbars

3. **Single Address Map**
   - All masters see same slave address map
   - Workaround: Address translation before crossbar

4. **No Priority Levels**
   - Round-robin only, no fixed priority or weighted arbitration
   - Workaround: External priority arbitration before crossbar

### Future Enhancements

**1. Variable Slave Sizes**
```python
# Potential future API
generate_apb_xbar(
    num_masters=2,
    slave_sizes=[4096, 65536, 1024, 16384],  # Custom sizes per slave
    base_addr=0x10000000
)
```

**2. Arbitration Policies**
```python
# Potential future API
generate_apb_xbar(
    num_masters=4,
    num_slaves=4,
    arbitration="weighted",  # "round-robin", "fixed-priority", "weighted"
    weights=[4, 2, 1, 1]     # Master 0 gets 4x priority
)
```

**3. Address Translation**
```python
# Potential future API
generate_apb_xbar(
    num_masters=2,
    num_slaves=4,
    master_views=[
        {"base": 0x00000000, "remap": True},   # Master 0 sees 0x0
        {"base": 0x10000000, "remap": False}   # Master 1 sees 0x1000_0000
    ]
)
```

---

## Testing Generated Code

### Verification Flow

**1. Generate Crossbar**
```bash
python generate_xbars.py --masters 2 --slaves 4
```

**2. Lint Generated RTL**
```bash
cd ../../rtl/
verilator --lint-only apb_xbar_2to4.sv
```

**3. Run Functional Tests**
```bash
cd ../../dv/tests/
pytest test_apb_xbar_2to4.py -v
```

**4. View Waveforms (If Test Fails)**
```bash
gtkwave waves.vcd
```

### Recommended Test Cases

1. **Single Master Access** - Verify basic routing
2. **Multi-Master Contention** - Verify arbitration
3. **Back-to-Back Transactions** - Verify zero-bubble throughput
4. **Address Decode Boundary** - Verify slave selection at boundaries
5. **Error Response Propagation** - Verify PSLVERR routing

---

## Advanced Usage

### Using as Python Library

```python
# Import generator function
from bin.rtl_generators.amba.apb_xbar_generator import generate_apb_xbar

# Generate crossbar programmatically
code = generate_apb_xbar(
    num_masters=3,
    num_slaves=8,
    base_addr=0xA0000000,
    addr_width=32,
    data_width=32,
    output_file="my_custom_xbar.sv"
)

# Generated code is returned as string
print(f"Generated {len(code)} bytes of SystemVerilog code")

# Can also write to file manually
with open("custom_output.sv", "w") as f:
    f.write(code)
```

### Batch Generation

```python
# Generate multiple variants in one script
variants = [
    (1, 4, 0x10000000),
    (2, 4, 0x20000000),
    (3, 6, 0x30000000),
    (4, 8, 0x40000000),
]

for masters, slaves, base_addr in variants:
    code = generate_apb_xbar(
        num_masters=masters,
        num_slaves=slaves,
        base_addr=base_addr,
        output_file=f"xbar_{masters}to{slaves}_0x{base_addr:08X}.sv"
    )
    print(f"✅ Generated xbar_{masters}to{slaves}_0x{base_addr:08X}.sv")
```

---

## Troubleshooting

### Issue: "ModuleNotFoundError: No module named 'amba.apb_xbar_generator'"

**Cause:** Python can't find the core generator module

**Solution:**
```bash
# Verify generator exists
ls -la bin/apb_xbar_generator.py

# Run from bin directory
cd projects/components/apb_xbar/bin/
python generate_xbars.py
```

### Issue: Generated Code Won't Lint

**Cause:** Generator bug or unsupported configuration

**Solution:**
1. Check parameter ranges (1-16 for M and N)
2. Verify base address alignment (should be aligned to 64KB × N)
3. Report bug with command that caused issue

### Issue: Generated Code Too Large

**Cause:** Very large MxN configuration (e.g., 16x16)

**Expected Behavior:**
- 1x1: ~200 LOC
- 2x4: ~1000 LOC
- 16x16: ~25,000 LOC (practical limit)

**Solution:**
- Consider hierarchical approach (multiple smaller crossbars)
- Or use different interconnect topology (bus, tree, etc.)

---

## References

- [Architecture Overview](01_architecture.md)
- [Address Decode and Arbitration](02_address_and_arbitration.md)
- [PRD.md](../../PRD.md) - Complete specification
- [CLAUDE.md](../../CLAUDE.md) - Integration guidance
- [README.md](../../README.md) - Quick start guide

---

**Version:** 1.0
**Last Updated:** 2025-10-25
**Maintained By:** RTL Design Sherpa Project
