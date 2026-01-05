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

# 8254 PIT Design Sketch

**Component:** APB 8254 Programmable Interval Timer
**Version:** 0.1 (Design Sketch)
**Status:** 📋 Planning Phase
**Date:** 2025-11-06
**Based On:** HPET microarchitecture and design patterns

---

## Executive Summary

The APB 8254 PIT provides a production-quality implementation of the Intel 8254 Programmable Interval Timer with AMBA APB4 interface. Following HPET's proven design patterns, the PIT implements 3 independent 16-bit counters with 6 programmable modes for system timing, square wave generation, and event counting.

**Design Philosophy:** Leverage HPET's successful patterns while adapting for 8254's specific requirements.

---

## 1. Architecture Overview

### 1.1 High-Level Block Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                          APB_PIT_8254                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────┐    │
│  │  APB Slave   │────▶│ Config Regs  │────▶│  PIT Core    │    │
│  │  (Optional   │     │ (PeakRDL)    │     │              │    │
│  │   CDC)       │     │              │     │ - Counter 0  │    │
│  └──────────────┘     └──────────────┘     │ - Counter 1  │    │
│                                             │ - Counter 2  │    │
│       APB Clock Domain                      │              │    │
│                                             └──────────────┘    │
│                                                    │             │
│                       PIT Clock Domain       Gate[2:0]          │
│                                              Out[2:0]           │
│                                              (Interrupts/       │
│                                               Square Waves)     │
└─────────────────────────────────────────────────────────────────┘
```

**Follows HPET Pattern:**
- APB Slave + Config Regs + Core (3-layer architecture)
- Optional CDC for clock domain separation
- PeakRDL register generation
- Clean interface separation

### 1.2 Module Hierarchy

```
apb_pit_8254.sv              # Top-level wrapper (like apb_hpet.sv)
├── apb_slave_cdc.sv         # CDC wrapper (conditional instantiation)
├── pit_config_regs.sv       # Register wrapper (like hpet_config_regs.sv)
│   ├── peakrdl_to_cmdrsp.sv # PeakRDL adapter
│   └── pit_regs.sv          # PeakRDL generated (from pit_regs.rdl)
└── pit_core.sv              # Core timer logic (like hpet_core.sv)
    ├── pit_counter.sv       # Single counter instance (reusable)
    └── pit_mode_fsm.sv      # Per-counter mode FSM
```

**Reuses HPET Modules:**
- `apb_slave_cdc.sv` - Identical to HPET
- `peakrdl_to_cmdrsp.sv` - Identical to HPET
- Edge detection, synchronizers - From common library

---

## 2. Key Differences from HPET

### 2.1 Counter Architecture

| Feature | HPET | 8254 PIT |
|---------|------|----------|
| **Counter Size** | 64-bit | 16-bit |
| **Counter Direction** | Up-counting | Down-counting |
| **Counter Count** | 1 main counter | 3 independent counters |
| **Comparator** | 64-bit per timer | N/A (terminal count = 0) |
| **Operating Modes** | 2 (one-shot, periodic) | 6 (modes 0-5) |
| **Number Format** | Binary only | Binary or BCD |
| **Read-Back** | Simple read | Special read-back command |

### 2.2 Register Interface

**HPET Approach:**
- Global config + per-timer registers
- 64-bit counter split into LO/HI
- W1C interrupt status

**8254 PIT Approach:**
- Shared control word register
- 3 counter registers (8-bit access to 16-bit counter)
- Read-back command for latch and status
- No interrupt status register (use counter OUT signals)

### 2.3 Clock/Gate Interface

**HPET:**
- Single clock input
- Always counting (when enabled)

**8254 PIT:**
- Per-counter GATE input (enables/triggers counting)
- Per-counter CLK input (could share common clock)
- Per-counter OUT output (interrupt/square wave)

---

## 3. Register Map (Following HPET Pattern)

### 3.1 Address Map

Following HPET's clean addressing and PeakRDL generation:

```
0x000-0x0FF: Configuration and Status Registers
0x100-0x1FF: Reserved for expansion
0x200-0xFFF: Reserved (4KB window like HPET)

Specific Registers:
0x000: PIT_CONFIG     - Global configuration (RW)
0x004: PIT_CONTROL    - Counter control word (WO, like 8254 port 0x43)
0x008: PIT_STATUS     - Read-back status (RO)
0x00C: RESERVED
0x010: COUNTER0_DATA  - Counter 0 value (RW, like 8254 port 0x40)
0x014: COUNTER1_DATA  - Counter 1 value (RW, like 8254 port 0x41)
0x018: COUNTER2_DATA  - Counter 2 value (RW, like 8254 port 0x42)
0x01C: RESERVED
```

**HPET Inspiration:**
- Clean 4KB address space
- Reserved registers for future expansion
- PeakRDL-friendly layout (not cramped like original 8254 I/O ports)

### 3.2 Register Definitions (SystemRDL)

**pit_regs.rdl** (following hpet_regs.rdl pattern):

```systemverilog
addrmap pit_regs #(
    longint NUM_COUNTERS = 3  // Always 3 for 8254 compatibility
) {
    name = "PIT 8254 Configuration Registers";
    desc = "Programmable Interval Timer register file";

    default regwidth = 32;
    default accesswidth = 32;

    //========================================
    // Global Configuration
    //========================================
    reg {
        name = "PIT Configuration Register";
        desc = "Global PIT configuration and control";

        field {
            name = "PIT Enable";
            desc = "Enable all counters (master enable)";
            sw = rw;
            hw = r;
        } pit_enable[0:0] = 1'b0;

        field {
            name = "Clock Select";
            desc = "0=external clock, 1=APB clock";
            sw = rw;
            hw = r;
        } clock_select[1:1] = 1'b0;

        field {
            name = "Reserved";
            sw = r;
            hw = na;
        } reserved[31:2] = 30'h0;

    } PIT_CONFIG @ 0x000;

    //========================================
    // Control Word Register
    //========================================
    reg {
        name = "PIT Control Word";
        desc = "8254-compatible control word (write-only)";

        field {
            name = "BCD/Binary";
            desc = "0=binary, 1=BCD";
            sw = w;
            hw = r;
            onwrite = woset;
        } bcd[0:0] = 1'b0;

        field {
            name = "Mode";
            desc = "Counter mode (0-5)";
            sw = w;
            hw = r;
            onwrite = woset;
        } mode[3:1] = 3'h0;

        field {
            name = "Read/Load";
            desc = "0=latch, 1=LSB, 2=MSB, 3=LSB/MSB";
            sw = w;
            hw = r;
            onwrite = woset;
        } rw_mode[5:4] = 2'h0;

        field {
            name = "Counter Select";
            desc = "0=counter0, 1=counter1, 2=counter2, 3=read-back";
            sw = w;
            hw = r;
            onwrite = woset;
        } counter_select[7:6] = 2'h0;

        field {
            name = "Reserved";
            sw = r;
            hw = na;
        } reserved[31:8] = 24'h0;

    } PIT_CONTROL @ 0x004;

    //========================================
    // Status Register (Read-Back)
    //========================================
    reg {
        name = "PIT Status Register";
        desc = "Counter status from read-back command";

        field {
            name = "Counter 0 Status";
            desc = "Status byte from counter 0";
            sw = r;
            hw = w;
        } counter0_status[7:0];

        field {
            name = "Counter 1 Status";
            desc = "Status byte from counter 1";
            sw = r;
            hw = w;
        } counter1_status[15:8];

        field {
            name = "Counter 2 Status";
            desc = "Status byte from counter 2";
            sw = r;
            hw = w;
        } counter2_status[23:16];

        field {
            name = "Reserved";
            sw = r;
            hw = na;
        } reserved[31:24] = 8'h0;

    } PIT_STATUS @ 0x008;

    //========================================
    // Counter Data Registers
    //========================================
    reg {
        name = "Counter 0 Data";
        desc = "Counter 0 count value (16-bit via LSB/MSB access)";

        field {
            name = "Counter 0 Value";
            desc = "16-bit counter value";
            sw = rw;
            hw = rw;
        } counter0_data[15:0] = 16'h0;

        field {
            name = "Reserved";
            sw = r;
            hw = na;
        } reserved[31:16] = 16'h0;

    } COUNTER0_DATA @ 0x010;

    reg {
        name = "Counter 1 Data";
        desc = "Counter 1 count value (16-bit via LSB/MSB access)";

        field {
            name = "Counter 1 Value";
            desc = "16-bit counter value";
            sw = rw;
            hw = rw;
        } counter1_data[15:0] = 16'h0;

        field {
            name = "Reserved";
            sw = r;
            hw = na;
        } reserved[31:16] = 16'h0;

    } COUNTER1_DATA @ 0x014;

    reg {
        name = "Counter 2 Data";
        desc = "Counter 2 count value (16-bit via LSB/MSB access)";

        field {
            name = "Counter 2 Value";
            desc = "16-bit counter value";
            sw = rw;
            hw = rw;
        } counter2_data[15:0] = 16'h0;

        field {
            name = "Reserved";
            sw = r;
            hw = na;
        } reserved[31:16] = 16'h0;

    } COUNTER2_DATA @ 0x018;

};
```

---

## 4. Core Logic Design (pit_core.sv)

### 4.1 Following HPET Pattern

**HPET Core Structure:**
```systemverilog
module hpet_core #(NUM_TIMERS = 2) (
    input  logic hpet_clk, hpet_rst_n,
    input  logic hpet_enable,
    input  logic [63:0] counter_write_data,
    output logic [63:0] counter_value,
    // Per-timer signals
    input  logic [NUM_TIMERS-1:0] timer_enable,
    output logic [NUM_TIMERS-1:0] timer_fired
);
```

**PIT Core Structure (Similar):**
```systemverilog
module pit_core #(
    parameter int NUM_COUNTERS = 3
) (
    input  logic                    pit_clk,
    input  logic                    pit_rst_n,

    // Global control
    input  logic                    pit_enable,
    input  logic                    clock_select,  // 0=ext, 1=APB

    // Per-counter configuration
    input  logic [NUM_COUNTERS-1:0] counter_enable,
    input  logic [2:0]              counter_mode [NUM_COUNTERS],
    input  logic [NUM_COUNTERS-1:0] counter_bcd,
    input  logic [1:0]              counter_rw_mode [NUM_COUNTERS],

    // Per-counter load/latch
    input  logic [NUM_COUNTERS-1:0] counter_load,
    input  logic [15:0]             counter_load_data [NUM_COUNTERS],
    input  logic [NUM_COUNTERS-1:0] counter_latch,

    // Per-counter status
    output logic [15:0]             counter_value [NUM_COUNTERS],
    output logic [7:0]              counter_status [NUM_COUNTERS],

    // External counter signals
    input  logic [NUM_COUNTERS-1:0] gate_in,
    input  logic [NUM_COUNTERS-1:0] clk_in,
    output logic [NUM_COUNTERS-1:0] out_signal
);
```

### 4.2 Per-Counter Instance

**Following HPET's per-timer pattern:**

```systemverilog
module pit_counter (
    input  logic        clk,
    input  logic        rst_n,

    // Configuration
    input  logic        enable,
    input  logic [2:0]  mode,         // 0-5
    input  logic        bcd_mode,     // 0=binary, 1=BCD
    input  logic [1:0]  rw_mode,      // LSB/MSB/LSB+MSB

    // Load/Latch control
    input  logic        load,
    input  logic [15:0] load_data,
    input  logic        latch,

    // External signals
    input  logic        gate,
    input  logic        counter_clk,

    // Status outputs
    output logic [15:0] counter_value,
    output logic [7:0]  status_byte,
    output logic        out
);

    // Internal counter (16-bit)
    logic [15:0] r_counter;
    logic [15:0] r_counter_latch;
    logic [15:0] r_reload_value;
    logic        r_latched;

    // Mode-specific FSM
    pit_mode_fsm u_fsm (
        .clk          (clk),
        .rst_n        (rst_n),
        .mode         (mode),
        .gate         (gate),
        .counter_clk  (counter_clk),
        .counter      (r_counter),
        .reload_value (r_reload_value),
        .bcd_mode     (bcd_mode),
        // FSM outputs
        .decrement    (w_decrement),
        .reload       (w_reload),
        .out          (out)
    );

    // Counter logic (down-counting like 8254)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 16'h0;
            r_reload_value <= 16'hFFFF;
        end else if (load) begin
            r_reload_value <= load_data;
            r_counter <= load_data;
        end else if (w_reload) begin
            r_counter <= r_reload_value;
        end else if (w_decrement) begin
            if (bcd_mode)
                r_counter <= bcd_decrement(r_counter);
            else
                r_counter <= r_counter - 16'h1;
        end
    end

    // Latch logic (for read-back)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter_latch <= 16'h0;
            r_latched <= 1'b0;
        end else if (latch) begin
            r_counter_latch <= r_counter;
            r_latched <= 1'b1;
        end else if (/* counter read */) begin
            r_latched <= 1'b0;
        end
    end

    // Status byte generation (like 8254)
    assign status_byte = {
        out,           // bit 7: OUT pin state
        r_latched,     // bit 6: null count flag
        rw_mode,       // bits 5:4: RW mode
        mode,          // bits 3:1: counter mode
        bcd_mode       // bit 0: BCD mode
    };

    assign counter_value = r_latched ? r_counter_latch : r_counter;

endmodule
```

---

## 5. Counter Modes Implementation

### 5.1 Mode Descriptions (from 8254 spec)

Following HPET's state machine pattern but for 6 modes:

**Mode 0: Interrupt on Terminal Count**
- Load count, decrement on each CLK
- OUT goes high when count = 0
- Similar to HPET one-shot

**Mode 1: Hardware Retriggerable One-Shot**
- Triggered by GATE rising edge
- Decrement, OUT goes high when count = 0
- GATE retriggers

**Mode 2: Rate Generator**
- Divide-by-N counter
- OUT pulses low for 1 CLK cycle when count = 1
- Auto-reloads
- Similar to HPET periodic

**Mode 3: Square Wave Mode**
- Symmetric square wave output
- OUT toggles at count/2
- Auto-reloads

**Mode 4: Software Triggered Strobe**
- Decrement on CLK
- OUT pulses low for 1 CLK at count = 0
- No auto-reload

**Mode 5: Hardware Triggered Strobe**
- GATE rising edge triggers
- Like Mode 4 but hardware triggered

### 5.2 Mode FSM (pit_mode_fsm.sv)

**Following HPET's FSM pattern:**

```systemverilog
module pit_mode_fsm (
    input  logic        clk,
    input  logic        rst_n,

    // Configuration
    input  logic [2:0]  mode,
    input  logic        gate,
    input  logic        counter_clk,
    input  logic [15:0] counter,
    input  logic [15:0] reload_value,
    input  logic        bcd_mode,

    // FSM outputs
    output logic        decrement,
    output logic        reload,
    output logic        out
);

    // Edge detection for GATE and CLK
    logic r_gate_prev, r_clk_prev;
    logic w_gate_rising, w_clk_rising;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_gate_prev <= 1'b0;
            r_clk_prev <= 1'b0;
        end else begin
            r_gate_prev <= gate;
            r_clk_prev <= counter_clk;
        end
    end

    assign w_gate_rising = gate && !r_gate_prev;
    assign w_clk_rising = counter_clk && !r_clk_prev;

    // Mode-specific logic
    always_comb begin
        decrement = 1'b0;
        reload = 1'b0;
        out = 1'b0;

        case (mode)
            3'd0: begin  // Mode 0: Interrupt on terminal count
                if (w_clk_rising && gate && counter != 16'h0)
                    decrement = 1'b1;
                out = (counter == 16'h0);
            end

            3'd1: begin  // Mode 1: Hardware retriggerable one-shot
                if (w_gate_rising)
                    reload = 1'b1;
                else if (w_clk_rising && counter != 16'h0)
                    decrement = 1'b1;
                out = (counter == 16'h0);
            end

            3'd2: begin  // Mode 2: Rate generator
                if (w_clk_rising && gate) begin
                    if (counter == 16'h1) begin
                        reload = 1'b1;
                        out = 1'b1;  // Pulse low (active low in 8254)
                    end else begin
                        decrement = 1'b1;
                    end
                end
            end

            3'd3: begin  // Mode 3: Square wave
                if (w_clk_rising && gate) begin
                    if (counter == 16'h0)
                        reload = 1'b1;
                    else
                        decrement = 1'b1;
                end
                // OUT toggles based on counter half-period
                out = (counter > (reload_value >> 1));
            end

            3'd4: begin  // Mode 4: Software triggered strobe
                if (w_clk_rising && counter != 16'h0)
                    decrement = 1'b1;
                out = (counter == 16'h0);  // Pulse low at zero
            end

            3'd5: begin  // Mode 5: Hardware triggered strobe
                if (w_gate_rising)
                    reload = 1'b1;
                else if (w_clk_rising && counter != 16'h0)
                    decrement = 1'b1;
                out = (counter == 16'h0);
            end

            default: begin
                out = 1'b1;
            end
        endcase
    end

endmodule
```

---

## 6. Test Strategy (Following HPET Pattern)

### 6.1 Test Structure

**Following HPET's 3-level test hierarchy:**

```
dv/tbclasses/pit_8254/
├── pit_8254_tb.py           # Main testbench class
├── pit_8254_tests_basic.py  # Basic test suite
├── pit_8254_tests_medium.py # Medium test suite
└── pit_8254_tests_full.py   # Full test suite

dv/tests/pit_8254/
├── test_apb_pit_8254.py     # Test runner
└── conftest.py              # Pytest configuration
```

### 6.2 Test Levels

**Basic Tests (4-6 tests, <30s each):**
1. Register read/write access
2. Counter enable/disable
3. Mode 0 (interrupt on terminal count)
4. Simple count down verification
5. GATE input control
6. OUT signal generation

**Medium Tests (5-8 tests, 30-90s each):**
1. All 6 counter modes (one test per mode)
2. BCD counting mode
3. LSB/MSB/LSB+MSB read/write
4. Read-back command
5. Multiple counters concurrent operation
6. Counter latch functionality

**Full Tests (3-5 tests, 90+s each):**
1. All modes stress test (all counters, all modes)
2. CDC variants (if CDC_ENABLE supported)
3. Timing accuracy verification
4. Edge case testing (zero counts, max counts)
5. Long-duration counting

### 6.3 Testbench Class Structure

**pit_8254_tb.py** (following hpet_tb.py pattern):

```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.apb.apb_master import APBMaster

class PIT8254TB(TBBase):
    """Testbench for 8254 PIT peripheral"""

    # Register addresses (match SystemRDL)
    PIT_CONFIG = 0x000
    PIT_CONTROL = 0x004
    PIT_STATUS = 0x008
    COUNTER0_DATA = 0x010
    COUNTER1_DATA = 0x014
    COUNTER2_DATA = 0x018

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.pclk = dut.pclk
        self.presetn = dut.presetn
        self.pit_clk = dut.pit_clk
        self.pit_rst_n = dut.pit_rst_n

        # Create APB master
        self.apb = APBMaster(
            dut=dut,
            name="apb_master",
            clk=self.pclk,
            paddr=dut.s_apb_PADDR,
            psel=dut.s_apb_PSEL,
            penable=dut.s_apb_PENABLE,
            pwrite=dut.s_apb_PWRITE,
            pwdata=dut.s_apb_PWDATA,
            prdata=dut.s_apb_PRDATA,
            pready=dut.s_apb_PREADY
        )

    async def setup_clocks_and_reset(self):
        """Complete initialization - MANDATORY METHOD"""
        # Start clocks
        await self.start_clock('pclk', freq=10, units='ns')
        await self.start_clock('pit_clk', freq=5, units='ns')  # Faster PIT clock

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def assert_reset(self):
        """Assert reset - MANDATORY METHOD"""
        self.presetn.value = 0
        self.pit_rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset - MANDATORY METHOD"""
        self.presetn.value = 1
        self.pit_rst_n.value = 1

    async def configure_counter(self, counter_num, mode, bcd=False, rw_mode=3):
        """Configure counter via control word (like 8254 I/O port 0x43)"""
        control_word = (
            (counter_num << 6) |  # Counter select
            (rw_mode << 4) |      # RW mode
            (mode << 1) |         # Counter mode
            (1 if bcd else 0)     # BCD flag
        )
        await self.apb.write(self.PIT_CONTROL, control_word)

    async def load_counter(self, counter_num, value):
        """Load counter value (LSB+MSB)"""
        counter_addr = self.COUNTER0_DATA + (counter_num * 4)
        await self.apb.write(counter_addr, value & 0xFFFF)

    async def read_counter(self, counter_num):
        """Read counter value"""
        counter_addr = self.COUNTER0_DATA + (counter_num * 4)
        value = await self.apb.read(counter_addr)
        return value & 0xFFFF

    async def wait_for_out(self, counter_num, expected_state, timeout_ns=1000):
        """Wait for OUT signal to reach expected state"""
        out_signal = self.dut.out_signal[counter_num]
        start_time = cocotb.utils.get_sim_time('ns')

        while cocotb.utils.get_sim_time('ns') - start_time < timeout_ns:
            if out_signal.value == expected_state:
                return True
            await self.wait_clocks('pit_clk', 1)

        return False
```

---

## 7. Design Checklist (HPET-Derived)

### 7.1 RTL Requirements

- [ ] Use reset macros (`ALWAYS_FF_RST`) - MANDATORY
- [ ] Add FPGA synthesis attributes to any memory arrays
- [ ] Use `[DEPTH]` not `[0:DEPTH-1]` for arrays
- [ ] PeakRDL register generation from .rdl file
- [ ] Edge-triggered write strobes (not level)
- [ ] Per-counter data buses (prevent corruption like HPET fix)
- [ ] Optional CDC support (parameter-controlled)
- [ ] Clean 3-layer architecture (APB + Config + Core)

### 7.2 Documentation Requirements

- [ ] SystemRDL specification (pit_regs.rdl)
- [ ] Complete register map documentation
- [ ] Block diagrams (Graphviz, PlantUML)
- [ ] Timing diagrams (WaveDrom)
- [ ] Programming model with code examples
- [ ] Comparison with original 8254 I/O port interface
- [ ] Test results and verification status
- [ ] Known issues documentation

### 7.3 Testbench Requirements

- [ ] TB class in project area (dv/tbclasses/pit_8254/)
- [ ] Three test levels (basic/medium/full)
- [ ] Mandatory methods: setup_clocks_and_reset(), assert_reset(), deassert_reset()
- [ ] Test cleanup at end of each test
- [ ] Parameterized tests for multiple configurations
- [ ] Waveform dumps with GTKW save files
- [ ] Coverage tracking

---

## 8. Implementation Timeline

**Aggressive timeline leveraging proven HPET infrastructure:**

**HPET took 1 week. With PeakRDL flow established, 8254 PIT target: 2-3 weeks**

### Week 1: Core RTL + Basic Validation

**Days 1-2: Register Definition**
- Define pit_regs.rdl (copy HPET pattern)
- Generate with PeakRDL (30 minutes, proven)
- Create pit_config_regs.sv wrapper (copy HPET pattern, 2 hours)

**Days 3-4: Counter Core**
- Implement pit_counter.sv (single counter, mode 0 only first)
- Implement pit_core.sv (3 counter array, copy HPET multi-timer pattern)
- Basic counting test (verify down-counting works)

**Day 5: Top-Level Integration**
- Implement apb_pit_8254.sv (copy apb_hpet.sv pattern)
- Add CDC support (parameter copy from HPET)
- Create filelists
- **Deliverable:** Mode 0 working end-to-end

### Week 2: All Modes + Testing

**Days 1-3: Implement All 6 Modes**
- Add pit_mode_fsm.sv
- Mode 1: Hardware retriggerable (similar to mode 0)
- Mode 2: Rate generator (similar to HPET periodic)
- Mode 3: Square wave (toggle logic)
- Mode 4: Software strobe (similar to mode 0)
- Mode 5: Hardware strobe (combine mode 1 + 4)
- Test each mode as implemented

**Days 4-5: Testbench + Basic/Medium Tests**
- Create pit_8254_tb.py (copy hpet_tb.py pattern, 4 hours)
- Basic tests: 6 tests (one per mode, 1 hour each)
- Medium tests: BCD, read-back, multi-counter (8 hours)
- **Deliverable:** All modes tested, basic/medium 100% pass

### Week 3 (Optional): Polish + Full Tests

**Days 1-2: Documentation**
- Complete specification (copy HPET doc structure)
- Block diagrams (Graphviz from HPET templates)
- Timing diagrams (WaveDrom)

**Days 3-4: Full Test Suite**
- Stress tests (all counters, all modes concurrent)
- CDC variants
- Edge cases

**Day 5: Final Review**
- Fix any issues
- Final test runs
- Ready for production

### Aggressive Target: 2 weeks

**Rationale:**
- SystemRDL: 30 minutes (proven with HPET)
- Register wrapper: 2 hours (copy HPET pattern)
- Top-level: 2 hours (copy HPET pattern)
- Counter core: 2 days (simpler than 64-bit HPET counter)
- Mode FSM: 3 days (6 modes, but well-defined spec)
- Testbench: 4 hours (copy HPET TB pattern)
- Tests: 1-2 days (basic/medium)
- Documentation: 2 days (copy HPET structure)

**Total: 10-14 days** (2-3 weeks with buffer)

---

## 9. Success Criteria

**Following HPET's proven metrics:**

1. **Functional Correctness:**
   - ✅ All 6 counter modes implemented correctly
   - ✅ BCD and binary counting modes
   - ✅ Read-back command functional
   - ✅ GATE input control works
   - ✅ OUT signal generation accurate

2. **Test Coverage:**
   - ✅ Basic tests: 100% pass rate
   - ✅ Medium tests: 100% pass rate
   - ✅ Full tests: ≥95% pass rate
   - ✅ All 6 modes tested
   - ✅ Multiple configurations (CDC on/off)

3. **Documentation Quality:**
   - ✅ Complete register map
   - ✅ All interfaces documented
   - ✅ Programming examples provided
   - ✅ Timing diagrams present
   - ✅ Comparison with original 8254

4. **Code Quality:**
   - ✅ Passes Verilator lint
   - ✅ Reset macros used throughout
   - ✅ FPGA synthesis attributes present
   - ✅ Clean module hierarchy
   - ✅ Reusable counter instances

---

## 10. Next Steps

**Immediate Actions:**

1. Create directory structure:
   ```bash
   mkdir -p rtl/pit_8254/{peakrdl,filelists}
   mkdir -p dv/tbclasses/pit_8254
   mkdir -p dv/tests/pit_8254
   mkdir -p docs/pit_8254_spec
   ```

2. Create initial SystemRDL specification (pit_regs.rdl)

3. Implement pit_counter.sv (single counter, all modes)

4. Create basic testbench for counter verification

5. Iterate on modes until all 6 work correctly

**Ready to proceed when approved!**

---

**Design Sketch By:** Claude (AI Assistant)
**Based On:** HPET proven patterns and 8254 specification
**Date:** 2025-11-06
**Status:** Ready for implementation approval
