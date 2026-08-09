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

# Claude Code Guide: APB Crossbar Component

**Version:** 1.0
**Last Updated:** 2025-10-19
**Purpose:** AI-specific guidance for working with APB Crossbar component

---

## Quick Context

**What:** APB Crossbar Generator - Parametric APB interconnect for connecting M masters to N slaves
**Status:** ✅ Production Ready (all tests passing)
**Your Role:** Help users generate, integrate, and customize APB crossbars

**📖 Complete Specification:** `projects/components/apb4_xbar/PRD.md` ← **Always reference this for technical details**

---

## Critical Rules for This Component

### Rule #0: This is a GENERATOR, Not Just Modules

**IMPORTANT:** APB Crossbar is both:
1. **Pre-generated modules** (1to1, 2to1, 1to4, 2to4, thin) in `rtl/`
2. **Python generator** (`bin/generate_xbars.py`) for custom configurations

**When users ask for crossbar:**
- ✅ **Check if pre-generated variant exists first**
- ✅ **Only suggest generation if custom size needed**

**Decision Tree:**
```
User needs crossbar?
├─ 1x1, 2x1, 1x4, 2x4? → Use pre-generated module
├─ Thin/minimal? → Use apb4_xbar_thin
└─ Custom MxN? → Run generator script
```

### Rule #1: Address Map is Fixed Per-Slave

**Each slave occupies 64KB region:**
```
Slave 0: BASE_ADDR + 0x0000_0000 → 0x0000_FFFF
Slave 1: BASE_ADDR + 0x0001_0000 → 0x0001_FFFF
Slave 2: BASE_ADDR + 0x0002_0000 → 0x0002_FFFF
...
```

**Users CANNOT change per-slave size** (current limitation)

**If user asks for different sizes:**
```
❌ WRONG: "Let me modify the generator to support custom sizes per slave"

✅ CORRECT: "Current design uses fixed 64KB per slave. You can:
1. Use BASE_ADDR parameter to shift entire map
2. For custom sizes, modify generator's addr_offset calculation
3. Or use multiple crossbars with different BASE_ADDR values"
```

### Rule #2: Know the Pre-Generated Variants

**Available in `rtl/` directory:**

| Module | M×N | Use Case | When to Recommend |
|--------|-----|----------|-------------------|
| **apb4_xbar_1to1** | 1×1 | Passthrough | Protocol conversion, testing |
| **apb4_xbar_2to1** | 2×1 | Arbitration | Multi-master to single peripheral |
| **apb4_xbar_1to4** | 1×4 | Decode | Single CPU to multiple peripherals |
| **apb4_xbar_2to4** | 2×4 | Full crossbar | CPU + DMA to peripherals |
| **apb4_xbar_thin** | 1×1 | Minimal | Low-overhead passthrough |

**Always suggest pre-generated first!**

### Rule #3: Generator Syntax

**Generate custom crossbar:**
```bash
cd projects/components/apb4_xbar/bin/
python generate_xbars.py --masters 3 --slaves 6
```

**Options:**
```bash
--masters M         Number of masters (1-16)
--slaves N          Number of slaves (1-16)
--base-addr ADDR    Base address (default: 0x10000000)
--output FILE       Output file path
--thin              Generate thin variant (minimal logic)
```

**Example:**
```bash
# Generate 3x8 crossbar with custom base
python generate_xbars.py --masters 3 --slaves 8 --base-addr 0x80000000

# Generate thin 5x5 variant
python generate_xbars.py --masters 5 --slaves 5 --thin
```

---

## Architecture Quick Reference

### Module Organization

```
projects/components/apb4_xbar/
├── rtl/
│   ├── apb4_xbar_1to1.sv        Core crossbar modules
│   ├── apb4_xbar_2to1.sv
│   ├── apb4_xbar_1to4.sv
│   ├── apb4_xbar_2to4.sv
│   ├── apb4_xbar_thin.sv
│   └── wrappers/               Pre-configured wrappers
│       ├── apb4_xbar_1to1_wrap.sv
│       ├── apb4_xbar_2to1_wrap.sv
│       ├── apb4_xbar_1to4_wrap.sv
│       ├── apb4_xbar_2to4_wrap.sv
│       ├── apb4_xbar_wrap.sv
│       ├── apb4_xbar_wrap_m10_s10.sv
│       └── apb4_xbar_thin_wrap_m10_s10.sv
├── bin/
│   └── generate_xbars.py       Generator script
├── dv/
│   └── tests/
│       ├── test_apb4_xbar_1to1.py
│       ├── test_apb4_xbar_2to1.py
│       ├── test_apb4_xbar_1to4.py
│       ├── test_apb4_xbar_2to4.py
│       └── GTKW/                Waveform configs
├── PRD.md                       Complete specification
├── CLAUDE.md                    This file
└── README.md                    Quick start guide
```

### Block Diagram (2×4 Example)

```
           Master 0      Master 1
               │             │
               ▼             ▼
         ┌─────────────────────┐
         │  APB Slaves (M-side) │
         └──────────┬────────────┘
                    │
         ┌──────────┴────────────┐
         │ Address Decode        │
         │ + Arbitration         │
         │ + Response Routing    │
         └──────────┬────────────┘
                    │
         ┌──────────┴────────────┐
         │  APB Masters (S-side) │
         └──────┬────────┬───────┘
                │        │   (more)
           Slave 0   Slave 1 ... Slave 3
```

---

## Common User Questions and Responses

### Q: "How do I connect a CPU to 4 peripherals?"

**A: Use the pre-generated 1to4 crossbar:**

```systemverilog
apb4_xbar_1to4 #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .BASE_ADDR(32'h1000_0000)  // Start of peripheral space
) u_peripheral_xbar (
    .pclk(apb_clk),
    .presetn(apb_rst_n),

    // CPU connection (master 0)
    .m0_apb_PSEL(cpu_psel),
    .m0_apb_PENABLE(cpu_penable),
    .m0_apb_PADDR(cpu_paddr),
    .m0_apb_PWRITE(cpu_pwrite),
    .m0_apb_PWDATA(cpu_pwdata),
    .m0_apb_PSTRB(cpu_pstrb),
    .m0_apb_PPROT(cpu_pprot),
    .m0_apb_PRDATA(cpu_prdata),
    .m0_apb_PSLVERR(cpu_pslverr),
    .m0_apb_PREADY(cpu_pready),

    // Peripheral 0: UART @ 0x1000_0000
    .s0_apb_PSEL(uart_psel),
    .s0_apb_PENABLE(uart_penable),
    // ... (full interface)

    // Peripheral 1: GPIO @ 0x1001_0000
    // Peripheral 2: Timer @ 0x1002_0000
    // Peripheral 3: SPI @ 0x1003_0000
);
```

**Address map:**
- UART: 0x1000_0000 - 0x1000_FFFF
- GPIO: 0x1001_0000 - 0x1001_FFFF
- Timer: 0x1002_0000 - 0x1002_FFFF
- SPI: 0x1003_0000 - 0x1003_FFFF

**📖 See:** `PRD.md` Section 11.1

### Q: "I need CPU and DMA to access peripherals. Which crossbar?"

**A: Use the 2to4 crossbar:**

```systemverilog
apb4_xbar_2to4 #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .BASE_ADDR(32'h1000_0000)
) u_soc_xbar (
    .pclk(apb_clk),
    .presetn(apb_rst_n),

    // Master 0: CPU
    .m0_apb_PSEL(cpu_psel),
    // ... (full interface)

    // Master 1: DMA
    .m1_apb_PSEL(dma_psel),
    // ... (full interface)

    // Slaves 0-3: Peripherals
    // ... (slave connections)
);
```

**Key feature:** Round-robin arbitration per slave ensures fair access between CPU and DMA.

**📖 See:** `PRD.md` Section 11.2

### Q: "What if I need 3 masters and 8 slaves?"

**A: Generate custom crossbar:**

```bash
cd projects/components/apb4_xbar/bin/
python generate_xbars.py --masters 3 --slaves 8   # writes apb4_xbar_3to8.sv next to the script

# Check generated file, then move it into rtl/
ls -lh apb4_xbar_3to8.sv
mv apb4_xbar_3to8.sv ../rtl/
```

Then instantiate like any other crossbar:
```systemverilog
apb4_xbar_3to8 #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .BASE_ADDR(32'h1000_0000)
) u_custom_xbar (
    // ... connections for 3 masters and 8 slaves
);
```

**📖 See:** `PRD.md` Section 8

### Q: "How does arbitration work?"

**A: Per-slave round-robin:**

Each slave has its own arbiter that rotates master priority:

```
Example with 2 masters accessing Slave 0:

Transaction 1: M0 requests → M0 granted
Transaction 2: M0 and M1 request → M1 granted (rotated)
Transaction 3: M1 requests → M1 granted
Transaction 4: M0 and M1 request → M0 granted (rotated)
```

**Key points:**
- **Independent per slave:** Each slave arbitrates independently
- **Fair:** No master can starve another
- **Grant persistence:** Once granted, master holds slave until response completes
- **Zero-bubble:** Back-to-back transactions supported

**📖 See:** `PRD.md` Section 3.3

### Q: "Can I change the address map?"

**A: BASE_ADDR parameter shifts entire map, but per-slave size is fixed:**

```systemverilog
// Default: 0x1000_0000
apb4_xbar_1to4 #(.BASE_ADDR(32'h1000_0000)) u_xbar1 (...);
// Slaves at: 0x1000_0000, 0x1001_0000, 0x1002_0000, 0x1003_0000

// Shifted: 0x8000_0000
apb4_xbar_1to4 #(.BASE_ADDR(32'h8000_0000)) u_xbar2 (...);
// Slaves at: 0x8000_0000, 0x8001_0000, 0x8002_0000, 0x8003_0000
```

**Limitation:** Each slave always occupies 64KB (0x10000 bytes)

**Workaround for different sizes:**
1. Use multiple crossbars with different BASE_ADDR
2. Modify generator's `addr_offset` calculation
3. Use address masking in slaves

**📖 See:** `PRD.md` Section 3.2

### Q: "How do I run tests?"

**A: Use pytest:**

```bash
cd projects/components/apb4_xbar/dv/tests/

# Run specific test
pytest test_apb4_xbar_1to4.py -v

# Run all tests
pytest test_apb4_xbar_*.py -v

# Run with waveforms
pytest test_apb4_xbar_2to4.py --vcd=waves.vcd
gtkwave waves.vcd
```

**Test coverage:**
- **test_apb4_xbar_1to1**: 100+ transactions (passthrough)
- **test_apb4_xbar_2to1**: 130+ transactions (arbitration)
- **test_apb4_xbar_1to4**: 200+ transactions (address decode)
- **test_apb4_xbar_2to4**: 350+ transactions (full stress)

**All tests passing ✅**

**📖 See:** `PRD.md` Section 10

### Q: "What's the thin variant for?"

**A: Minimal overhead passthrough:**

```systemverilog
apb4_xbar_thin #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_thin_xbar (
    // ... 1×1 connection
);
```

**Use cases:**
- Protocol conversion
- Timing boundary
- Clock domain crossing preparation
- Testing/debugging

**Difference from apb4_xbar_1to1:**
- Fewer internal registers
- Lower latency
- Smaller area (~30% reduction)
- No arbitration overhead

**📖 See:** `README.md` and `PRD.md` Section 4

---

## Integration Patterns

### Pattern 1: Simple Peripheral Interconnect

```systemverilog
// CPU to 4 peripherals
apb4_xbar_1to4 #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .BASE_ADDR(32'h1000_0000)
) u_periph_xbar (
    .pclk(sys_clk),
    .presetn(sys_rst_n),

    // CPU side
    .m0_apb_PSEL(cpu_apb_psel),
    .m0_apb_PENABLE(cpu_apb_penable),
    .m0_apb_PADDR(cpu_apb_paddr),
    .m0_apb_PWRITE(cpu_apb_pwrite),
    .m0_apb_PWDATA(cpu_apb_pwdata),
    .m0_apb_PSTRB(cpu_apb_pstrb),
    .m0_apb_PPROT(cpu_apb_pprot),
    .m0_apb_PRDATA(cpu_apb_prdata),
    .m0_apb_PSLVERR(cpu_apb_pslverr),
    .m0_apb_PREADY(cpu_apb_pready),

    // Peripherals
    .s0_apb_PSEL(uart_psel), /* ... full interface ... */
    .s1_apb_PSEL(gpio_psel), /* ... */
    .s2_apb_PSEL(timer_psel), /* ... */
    .s3_apb_PSEL(spi_psel) /* ... */
);
```

### Pattern 2: Multi-Master System

```systemverilog
// CPU + DMA to peripherals
apb4_xbar_2to4 #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .BASE_ADDR(32'h4000_0000)
) u_soc_xbar (
    .pclk(apb_clk),
    .presetn(apb_rst_n),

    // Master 0: CPU
    .m0_apb_PSEL(cpu_psel),
    /* ... full CPU interface ... */

    // Master 1: DMA Controller
    .m1_apb_PSEL(dma_psel),
    /* ... full DMA interface ... */

    // Slave 0-3: Memory-mapped peripherals
    .s0_apb_PSEL(mem_ctrl_psel), /* ... */
    .s1_apb_PSEL(uart_psel), /* ... */
    .s2_apb_PSEL(i2c_psel), /* ... */
    .s3_apb_PSEL(adc_psel) /* ... */
);
```

### Pattern 3: Hierarchical Interconnect

```systemverilog
// Top-level crossbar
apb4_xbar_1to4 u_top_xbar (
    .m0_apb_* (cpu_apb_*),
    .s0_apb_* (periph_bus0_*),  // To sub-crossbar 0
    .s1_apb_* (periph_bus1_*),  // To sub-crossbar 1
    .s2_apb_* (mem_ctrl_*),     // Direct to memory controller
    .s3_apb_* (dma_ctrl_*)      // Direct to DMA
);

// Sub-crossbar 0 for low-speed peripherals
apb4_xbar_1to4 u_periph_xbar0 (
    .m0_apb_* (periph_bus0_*),
    .s0_apb_* (uart0_*),
    .s1_apb_* (gpio0_*),
    .s2_apb_* (i2c0_*),
    .s3_apb_* (spi0_*)
);

// Sub-crossbar 1 for high-speed peripherals
apb4_xbar_1to4 u_periph_xbar1 (
    .m0_apb_* (periph_bus1_*),
    .s0_apb_* (uart1_*),
    .s1_apb_* (timer_*),
    .s2_apb_* (pwm_*),
    .s3_apb_* (adc_*)
);
```

---

## Anti-Patterns to Catch

### ❌ Anti-Pattern 1: Generating When Pre-Generated Exists

```
❌ WRONG:
User: "I need a 2×4 crossbar"
You: "Let me generate that for you..."
python generate_xbars.py --masters 2 --slaves 4

✅ CORRECTED:
"Use the pre-generated apb4_xbar_2to4.sv in the rtl/ directory.
No generation needed!"
```

### ❌ Anti-Pattern 2: Assuming Custom Per-Slave Sizes

```
❌ WRONG:
User: "Can I make slave 0 256KB and slave 1 4KB?"
You: "Sure, let me modify the parameters..."

✅ CORRECTED:
"Current design uses fixed 64KB per slave. For custom sizes:
1. Modify generator's addr_offset calculation
2. Or use multiple crossbars with different BASE_ADDR
3. Or implement address masking in slaves"
```

### ❌ Anti-Pattern 3: Not Mentioning Address Map

```
❌ WRONG:
User: "How do I integrate the crossbar?"
You: *Shows port connections only*

✅ CORRECTED:
"Here's the integration with address map:
apb4_xbar_1to4 #(.BASE_ADDR(32'h1000_0000)) u_xbar (...);

Address map:
- Slave 0: 0x1000_0000 - 0x1000_FFFF
- Slave 1: 0x1001_0000 - 0x1001_FFFF
- Slave 2: 0x1002_0000 - 0x1002_FFFF
- Slave 3: 0x1003_0000 - 0x1003_FFFF"
```

### ❌ Anti-Pattern 4: Forgetting About Wrappers

```
❌ WRONG:
User: "I need a quick 10×10 crossbar"
You: "Run the generator with --masters 10 --slaves 10"

✅ CORRECTED:
"We have pre-configured wrappers in rtl/wrappers/:
- apb4_xbar_wrap_m10_s10.sv (full version)
- apb4_xbar_thin_wrap_m10_s10.sv (thin version)

Use those for faster integration!"
```

---

## Debugging Workflow

### Issue: Address Not Routing Correctly

**Check in order:**
1. ✅ BASE_ADDR parameter set correctly?
2. ✅ Address within slave's 64KB region?
3. ✅ PSEL signal asserted by master?
4. ✅ All APB signals properly connected?

**Calculate expected slave:**
```
slave_index = (address - BASE_ADDR) >> 16  // Divide by 64KB
```

**Debug commands:**
```bash
pytest dv/tests/test_apb4_xbar_1to4.py --vcd=debug.vcd -v
gtkwave debug.vcd  # Check address decode logic
```

### Issue: Arbitration Not Fair

**Symptoms:**
- One master dominates
- Other masters starved

**Check:**
1. ✅ Arbiters instantiated per slave?
2. ✅ Round-robin logic correct?
3. ✅ Grant persistence working?

**Verify with tests:**
```bash
pytest dv/tests/test_apb4_xbar_2to1.py -v  # Arbitration stress test
```

### Issue: Back-to-Back Transactions Stalling

**Check:**
1. ✅ Grant persistence enabled?
2. ✅ Slaves responding with PREADY?
3. ✅ No unintended pipeline bubbles?

**View waveforms:**
```bash
pytest dv/tests/test_apb4_xbar_2to4.py --vcd=perf.vcd
gtkwave perf.vcd  # Check for idle cycles
```

---

## Quick Commands

```bash
# List available crossbars
ls projects/components/apb4_xbar/rtl/*.sv

# Generate custom crossbar
cd projects/components/apb4_xbar/bin/
python generate_xbars.py --masters 3 --slaves 6

# Run all tests
cd projects/components/apb4_xbar/dv/tests/
pytest test_apb4_xbar_*.py -v

# Run specific test with waveforms
pytest test_apb4_xbar_2to4.py --vcd=debug.vcd -v

# View waveforms
gtkwave debug.vcd

# Check documentation
cat projects/components/apb4_xbar/PRD.md
cat projects/components/apb4_xbar/README.md
```

---

## Remember

1. 🔍 **Check pre-generated first** - Don't generate unnecessarily
2. 📍 **Address map matters** - Always mention BASE_ADDR + 64KB regions
3. ⚖️ **Fair arbitration** - Round-robin per slave
4. 🔗 **Complete connections** - All APB signals must be wired
5. ✅ **Tests available** - 100% passing, comprehensive coverage
6. 📚 **Wrappers exist** - Check rtl/wrappers/ for common configs
7. 🎯 **Generator limits** - Up to 16×16 (configurable)

---

**Version:** 1.0
**Last Updated:** 2025-10-19
**Maintained By:** RTL Design Sherpa Project
