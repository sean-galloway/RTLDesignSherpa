### APB HPET Blocks - Overview

#### Block Hierarchy

The APB HPET component consists of four primary SystemVerilog modules organized in a hierarchical structure:

```
apb_hpet (Top Level)
+-- APB Slave Interface
|   +-- apb_slave.sv (CDC_ENABLE=0) OR
|   +-- apb_slave_cdc.sv (CDC_ENABLE=1)
|
+-- hpet_config_regs (Register Wrapper)
|   +-- hpet_regs (PeakRDL Generated)
|   |   +-- Register File Logic
|   |
|   +-- Mapping Logic
|       +-- Per-Timer Data Buses
|       +-- Edge Detection
|       +-- Counter Write Capture
|
+-- hpet_core (Timer Logic)
    +-- 64-bit Free-Running Counter
    +-- Per-Timer Comparators [NUM_TIMERS]
    +-- Fire Detection Logic [NUM_TIMERS]
    +-- Interrupt Generation [NUM_TIMERS]
```

#### Timer Operation Waveforms

**Timer Initialization Sequence:**

![Timer Initialization](../assets/waves/timer_initialization.json)

**APB Configuration Register Writes:**

![Config Register Writes](../assets/waves/config_register_write.json)

*Note: Use [WaveDrom Editor](https://wavedrom.com/editor.html) to view/edit, or generate SVG with `wavedrom-cli`*

---

#### Module Responsibilities

##### 1. apb_hpet (Top Level Integration)
**File:** `rtl/apb_hpet.sv`
**Purpose:** System integration and CDC selection

**Responsibilities:**
- Instantiates APB slave with or without CDC based on `CDC_ENABLE` parameter
- Routes signals between APB interface and configuration registers
- Exposes timer interrupts to system
- Provides unified external interface

**Key Features:**
- Conditional CDC instantiation (generate block)
- Clock domain management
- Parameter propagation to child modules
- Single-point configuration

##### 2. hpet_config_regs (Register Wrapper)
**File:** `rtl/hpet_config_regs.sv`
**Purpose:** Bridge between PeakRDL registers and HPET core

**Responsibilities:**
- Instantiates PeakRDL-generated register file
- Maps PeakRDL hardware interface to HPET core signals
- Implements per-timer dedicated data buses (corruption fix)
- Detects register write edges for control strobes
- Handles 32-bit to 64-bit register combining

**Key Features:**
- Per-timer data buses prevent configuration corruption
- Edge detection for write strobes (not level)
- Counter write capture from APB domain
- W1C interrupt clearing support

##### 3. hpet_regs (PeakRDL Generated)
**File:** `rtl/hpet_regs.sv`
**Purpose:** Auto-generated register file from SystemRDL specification

**Responsibilities:**
- Implements all HPET registers from RDL specification
- Provides CPU interface (passthrough protocol)
- Generates hardware interface structs
- Handles field access types (RO, RW, W1C)

**Key Features:**
- Single source of truth (hpet_regs.rdl)
- Regeneratable from specification
- Comprehensive field control
- Standard passthrough CPU interface

##### 4. hpet_core (Timer Logic)
**File:** `rtl/hpet_core.sv`
**Purpose:** Core timer functionality and comparison logic

**Responsibilities:**
- Implements 64-bit free-running counter
- Manages per-timer comparators and periods
- Detects counter match conditions
- Generates timer fire events and interrupts
- Handles one-shot vs periodic mode differences

**Key Features:**
- Fully synchronous timer logic
- Per-timer FSM (conceptual)
- Automatic period reload (periodic mode)
- Edge-based fire detection
- Configurable timer count (2, 3, or 8 timers)

#### Data Flow Overview

##### APB Write Transaction Flow

```
APB Master
    ↓ PSEL, PENABLE, PADDR, PWDATA
APB Slave (or APB Slave CDC)
    ↓ cmd_valid, cmd_pwrite, cmd_paddr, cmd_pwdata
peakrdl_to_cmdrsp Adapter
    ↓ regblk_req, regblk_req_is_wr, regblk_addr, regblk_wr_data
hpet_regs (PeakRDL)
    ↓ hwif_out (register values)
hpet_config_regs (Mapping)
    ↓ timer_enable, timer_comparator_wr, timer_comparator_data[i]
hpet_core (Timer Logic)
    -> Counter/Comparator update
```

##### APB Read Transaction Flow

```
APB Master
    ↓ PSEL, PENABLE, PADDR, PWRITE=0
APB Slave (or APB Slave CDC)
    ↓ cmd_valid, cmd_pwrite=0, cmd_paddr
peakrdl_to_cmdrsp Adapter
    ↓ regblk_req, regblk_req_is_wr=0, regblk_addr
hpet_regs (PeakRDL)
    ← hwif_in (live counter, status)
    ↓ regblk_rd_data
peakrdl_to_cmdrsp Adapter
    ↓ rsp_prdata
APB Slave (or APB Slave CDC)
    ↓ PRDATA
APB Master
```

##### Timer Fire Flow

```
hpet_core
    ← Counter increments
    -> Comparator match detected
    -> timer_fired[i] asserts
    -> timer_irq[i] asserts
        ↓
hpet_config_regs
    -> hwif_in.HPET_STATUS.timer_int_status (edge pulse)
        ↓
hpet_regs (PeakRDL)
    -> STATUS register bit latches (sticky)
        ↓
Software reads HPET_STATUS
Software writes W1C to clear
    ↓
hpet_config_regs
    -> timer_int_clear[i] asserts
        ↓
hpet_core
    -> timer_fired[i] clears
    -> timer_irq[i] deasserts
```

#### Clock Domain Organization

##### Synchronous Mode (CDC_ENABLE=0)

```
APB Clock Domain (pclk)
+-- apb_slave
+-- hpet_config_regs
+-- hpet_regs
+-- hpet_core

All modules use pclk
No clock domain crossing required
```

##### Asynchronous Mode (CDC_ENABLE=1)

```
APB Clock Domain (pclk)
+-- apb_slave_cdc (pclk side)
+-- [CDC boundary]

HPET Clock Domain (hpet_clk)
+-- apb_slave_cdc (hpet_clk side)
+-- hpet_config_regs
+-- hpet_regs
+-- hpet_core

CDC synchronization between pclk and hpet_clk
```

#### Module Communication

##### hpet_config_regs -> hpet_core Interface

**Control Signals (hpet_config_regs -> hpet_core):**
```systemverilog
output logic                    hpet_enable;            // Global enable
output logic                    counter_write;          // Counter write strobe
output logic [63:0]             counter_wdata;          // Counter write data
output logic [NUM_TIMERS-1:0]   timer_enable;           // Per-timer enable
output logic [NUM_TIMERS-1:0]   timer_int_enable;       // Per-timer interrupt enable
output logic [NUM_TIMERS-1:0]   timer_type;             // Per-timer mode (0=one-shot, 1=periodic)
output logic [NUM_TIMERS-1:0]   timer_size;             // Per-timer size (0=32-bit, 1=64-bit)
output logic [NUM_TIMERS-1:0]   timer_comp_write;       // Per-timer comparator write strobe
output logic [63:0]             timer_comp_wdata[NUM_TIMERS];  // Per-timer data buses
```

**Status Signals (hpet_core -> hpet_config_regs):**
```systemverilog
input  logic [63:0]             counter_rdata;          // Live counter value
input  logic [NUM_TIMERS-1:0]   timer_int_status;       // Per-timer fire status
```

**Interrupt Clearing (hpet_config_regs -> hpet_core):**
```systemverilog
output logic [NUM_TIMERS-1:0]   timer_int_clear;        // Clear fire flags
```

##### hpet_config_regs -> hpet_regs Interface

Uses PeakRDL-generated structs:
```systemverilog
// From config regs to PeakRDL
input  hpet_regs_pkg::hpet_regs__in_t  hwif_in;

// From PeakRDL to config regs
output hpet_regs_pkg::hpet_regs__out_t hwif_out;
```

#### Resource Allocation

**Per-Configuration Estimates (Post-Synthesis):**

| Component | NUM_TIMERS=2 | NUM_TIMERS=3 | NUM_TIMERS=8 |
|-----------|--------------|--------------|--------------|
| **hpet_core** | | | |
| - Main counter | 64 FF, 70 LUTs | (same) | (same) |
| - Per-timer logic | 256 FF, 170 LUTs | 384 FF, 255 LUTs | 1024 FF, 680 LUTs |
| - Subtotal | 320 FF, 240 LUTs | 448 FF, 325 LUTs | 1088 FF, 750 LUTs |
| | | | |
| **hpet_config_regs** | | | |
| - Mapping logic | ~50 FF, ~100 LUTs | ~75 FF, ~150 LUTs | ~150 FF, ~300 LUTs |
| - Edge detect | ~10 FF, ~20 LUTs | ~15 FF, ~30 LUTs | ~30 FF, ~60 LUTs |
| - Subtotal | 60 FF, 120 LUTs | 90 FF, 180 LUTs | 180 FF, 360 LUTs |
| | | | |
| **hpet_regs** | | | |
| - Register storage | ~128 FF, ~100 LUTs | ~160 FF, ~125 LUTs | ~256 FF, ~200 LUTs |
| | | | |
| **apb_slave** (no CDC) | | | |
| - APB protocol | ~20 FF, ~50 LUTs | (same) | (same) |
| | | | |
| **apb_slave_cdc** (with CDC) | | | |
| - CDC logic | ~100 FF, ~150 LUTs | (same) | (same) |
| | | | |
| **Total (no CDC)** | ~528 FF, ~510 LUTs | ~718 FF, ~680 LUTs | ~1544 FF, ~1360 LUTs |
| **Total (with CDC)** | ~608 FF, ~610 LUTs | ~798 FF, ~780 LUTs | ~1624 FF, ~1460 LUTs |

**Scaling:** Resource usage is primarily driven by `NUM_TIMERS` parameter. Each additional timer adds ~128 FF and ~85 LUTs.

#### Integration Checklist

When integrating APB HPET:

**1. Parameter Selection:**
- [ ] `NUM_TIMERS`: 2, 3, or 8 timers
- [ ] `VENDOR_ID`: 16-bit vendor identification
- [ ] `REVISION_ID`: 16-bit revision identification
- [ ] `CDC_ENABLE`: 0 for synchronous, 1 for asynchronous clocks

**2. Clock Configuration:**
- [ ] Connect `pclk` (APB clock domain)
- [ ] Connect `hpet_clk` (timer clock domain)
- [ ] If `CDC_ENABLE=0`: Ensure `pclk = hpet_clk`
- [ ] If `CDC_ENABLE=1`: Clocks can be asynchronous

**3. Reset Coordination:**
- [ ] Assert `presetn` (APB reset, active-low)
- [ ] Assert `hpet_rst_n` (HPET reset, active-low)
- [ ] If `CDC_ENABLE=1`: Ensure both resets overlap at power-on
- [ ] Hold resets for >=10 clock cycles

**4. APB Interface:**
- [ ] Connect all APB signals (PSEL, PENABLE, PADDR, etc.)
- [ ] PADDR width = 12 bits (supports up to 4KB address space)
- [ ] PWDATA/PRDATA width = 32 bits (fixed)

**5. Interrupt Outputs:**
- [ ] Connect `timer_irq[NUM_TIMERS-1:0]` to interrupt controller
- [ ] Each timer has independent interrupt output
- [ ] Interrupts are active-high, level-sensitive

**6. Verification:**
- [ ] Test register access via APB
- [ ] Verify timer operation (one-shot and periodic modes)
- [ ] Test interrupt generation and clearing
- [ ] Validate CDC if enabled

---

**Next:** [Chapter 2.2 - hpet_config_regs](02_hpet_config_regs.md)
