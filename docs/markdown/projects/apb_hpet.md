# APB HPET - High Precision Event Timer

**Version:** 1.0
**Status:** ✅ Production Ready (5/6 configurations 100% passing)
**Last Updated:** 2025-10-17

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Design Details](#design-details)
4. [Register Map](#register-map)
5. [Operation Modes](#operation-modes)
6. [Clock Domain Crossing](#clock-domain-crossing)
7. [Integration Guide](#integration-guide)
8. [Verification](#verification)
9. [Performance](#performance)
10. [Known Issues](#known-issues)

---

## Overview

The APB High Precision Event Timer (HPET) is a configurable multi-timer peripheral designed for precise timing and event generation in embedded systems. It provides up to 8 independent hardware timers with 64-bit resolution, supporting both one-shot and periodic operating modes.

### Key Features

- **Configurable Timer Count:** 2, 3, or 8 independent timers
- **64-bit Main Counter:** High-resolution timestamp with sub-microsecond precision
- **64-bit Comparators:** Support for long-duration timing events
- **Dual Operating Modes:**
  - One-shot: Timer fires once
  - Periodic: Timer fires repeatedly at fixed intervals
- **Clock Domain Crossing:** Optional CDC for timer/APB clock independence
- **APB4 Interface:** Standard AMBA APB protocol for register access
- **PeakRDL Integration:** Register map generated from SystemRDL specification
- **Independent Interrupts:** Per-timer interrupt outputs

### Applications

| Application | Use Case |
|-------------|----------|
| **System Tick Generation** | OS kernel timer, scheduler tick |
| **Real-Time OS Scheduling** | Task scheduling, context switching |
| **Precise Event Timing** | Protocol timeouts, sensor sampling |
| **Performance Profiling** | Execution time measurement, benchmarking |
| **Watchdog Timers** | System health monitoring |
| **Multi-Rate Timing** | Different clock domains, multiple timebases |

### Design Highlights

- **Production Ready:** 5/6 configurations at 100% test coverage
- **Configurable:** Parameter-driven design for different use cases
- **Verified:** Comprehensive CocoTB test suite (12 tests per configuration)
- **Documented:** Complete PRD, CLAUDE guide, and integration examples
- **Industry Standard:** Based on IA-PC HPET specification (architectural reference)

---

## Architecture

### Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           APB HPET                                      │
│                    (projects/components/apb_hpet)                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   APB Interface (pclk domain)         HPET Clock Domain (hpet_clk)    │
│   ───────────────────────────         ─────────────────────────────    │
│                                                                         │
│  ┌──────────────────┐                                                  │
│  │   APB Slave      │                                                  │
│  │   (apb_slave)    │  Optional CDC                                   │
│  │   - psel         │◄──────────┐                                     │
│  │   - penable      │           │                                     │
│  │   - paddr        │           │                                     │
│  │   - pwdata       │           │                                     │
│  │   - prdata       │           │                                     │
│  │   - pready       │           │                                     │
│  └────────┬─────────┘           │                                     │
│           │                     │                                     │
│           │ cmd/rsp             │                                     │
│           ▼                     │                                     │
│  ┌──────────────────┐           │                                     │
│  │ hpet_config_regs │           │                                     │
│  │  (Register Map)  │           │                                     │
│  │                  │           │                                     │
│  │ ┌──────────────┐ │◄──────────┘ CDC handshake (if CDC_ENABLE=1)    │
│  │ │ hpet_regs    │ │                                                 │
│  │ │ (PeakRDL)    │ │                                                 │
│  │ │              │ │                                                 │
│  │ │ - CONFIG     │ │                                                 │
│  │ │ - STATUS     │ │                                                 │
│  │ │ - COUNTER    │ │                                                 │
│  │ │ - CAPS       │ │                                                 │
│  │ │ - TIMER[N]   │ │                                                 │
│  │ └──────────────┘ │                                                 │
│  │                  │                                                 │
│  │  Edge Detect &   │                                                 │
│  │  Bus Mapping     │                                                 │
│  └────────┬─────────┘                                                 │
│           │                                                            │
│           │ timer_comp_write[N], timer_enable[N], etc.               │
│           ▼                                                            │
│  ┌──────────────────┐                                                 │
│  │   hpet_core      │                                                 │
│  │  (Timer Logic)   │                                                 │
│  │                  │                                                 │
│  │  ┌────────────┐  │                                                 │
│  │  │ 64-bit     │  │                                                 │
│  │  │ Counter    │  │   Increments every hpet_clk cycle              │
│  │  └────────────┘  │                                                 │
│  │         │        │                                                 │
│  │         ▼        │                                                 │
│  │  ┌────────────┐  │                                                 │
│  │  │ Timer 0    │──┼──► timer_irq[0]                                │
│  │  │ Comparator │  │                                                 │
│  │  │  64-bit    │  │                                                 │
│  │  └────────────┘  │                                                 │
│  │  ┌────────────┐  │                                                 │
│  │  │ Timer 1    │──┼──► timer_irq[1]                                │
│  │  │ Comparator │  │                                                 │
│  │  │  64-bit    │  │                                                 │
│  │  └────────────┘  │                                                 │
│  │       ...        │                                                 │
│  │  ┌────────────┐  │                                                 │
│  │  │ Timer N-1  │──┼──► timer_irq[N-1]                              │
│  │  │ Comparator │  │                                                 │
│  │  │  64-bit    │  │                                                 │
│  │  └────────────┘  │                                                 │
│  └──────────────────┘                                                 │
│                                                                         │
│  Interrupts: timer_irq[NUM_TIMERS-1:0]                                │
└─────────────────────────────────────────────────────────────────────────┘
```

### Module Hierarchy

```
apb_hpet (Top Level)
├── apb_slave (or apb_slave_cdc if CDC_ENABLE=1)
│   └── Provides APB protocol handling
│
├── hpet_config_regs (Register Wrapper)
│   ├── hpet_regs (PeakRDL Generated)
│   │   └── APB register file with all HPET registers
│   │
│   └── Edge detection and bus mapping
│       ├── Timer write strobes (rising edge detect)
│       └── Per-timer data buses (prevent corruption)
│
└── hpet_core (Timer Logic)
    ├── Main counter (64-bit)
    │   └── Increments every hpet_clk cycle when enabled
    │
    ├── Timer comparators [0..NUM_TIMERS-1]
    │   ├── 64-bit comparator registers
    │   ├── One-shot mode: fire once
    │   └── Periodic mode: auto-increment after fire
    │
    └── Interrupt generation
        └── timer_irq[i] = (counter >= comparator[i]) && enabled
```

### Data Flow

#### Write Path (Software → Hardware)

```
APB Write Transaction
      │
      ▼
[APB Slave] ──cmd──► [APB Slave CDC] ──handshake──► [hpet_regs]
                     (if CDC_ENABLE=1)                    │
                                                          │
                                              Register write occurs
                                                          │
                                                          ▼
                                              [Edge Detect Logic]
                                                          │
                                            Generates write strobe
                                                          │
                                                          ▼
                                                  [hpet_core]
                                                          │
                                          Updates counter/comparator
```

#### Read Path (Hardware → Software)

```
APB Read Transaction
      │
      ▼
[APB Slave] ──cmd──► [APB Slave CDC] ──handshake──► [hpet_regs]
                     (if CDC_ENABLE=1)                    │
                                                          │
                                              Register read occurs
                                                          │
                                                          ▼
                                                  Read from:
                                              - Counter value
                                              - Status bits
                                              - Capabilities
                                                          │
                                                          ▼
[APB Slave] ◄──rsp──┼ [APB Slave CDC] ◄──handshake──┤
      │             (if CDC_ENABLE=1)
      ▼
prdata to CPU
```

#### Timer Fire Path (Hardware Event)

```
[hpet_core]
      │
      │ Main counter increments every hpet_clk
      │
      ▼
Counter >= Comparator[i] ?
      │
      ├─ No  ──► Continue incrementing
      │
      └─ Yes ──► Timer fires
                      │
                      ├─ Assert timer_irq[i]
                      │
                      ├─ Set STATUS[i] bit
                      │
                      └─ If periodic mode:
                            Comparator[i] += Period[i]
```

---

## Design Details

### Module Specifications

#### 1. apb_hpet (Top Level)

**File:** `projects/components/apb_hpet/rtl/apb_hpet.sv`

**Purpose:** Top-level wrapper integrating APB slave, configuration registers, and timer core.

**Parameters:**

| Parameter | Type | Valid Values | Default | Description |
|-----------|------|--------------|---------|-------------|
| `NUM_TIMERS` | int | 2, 3, 8 | 2 | Number of independent timers |
| `VENDOR_ID` | int | 0-0xFFFF | 0x8086 | Vendor identification code |
| `REVISION_ID` | int | 0-0xFFFF | 0x0001 | Hardware revision number |
| `CDC_ENABLE` | int | 0, 1 | 0 | Enable clock domain crossing |

**Ports:**

```systemverilog
module apb_hpet #(
    parameter int NUM_TIMERS = 2,
    parameter int VENDOR_ID = 16'h8086,
    parameter int REVISION_ID = 16'h0001,
    parameter int CDC_ENABLE = 0
) (
    // APB Interface (pclk domain)
    input  logic        pclk,
    input  logic        presetn,
    input  logic [11:0] paddr,
    input  logic        psel,
    input  logic        penable,
    input  logic        pwrite,
    input  logic [31:0] pwdata,
    output logic        pready,
    output logic [31:0] prdata,
    output logic        pslverr,

    // HPET Clock Domain
    input  logic        hpet_clk,
    input  logic        hpet_rst_n,

    // Interrupts
    output logic [NUM_TIMERS-1:0] timer_irq
);
```

**Key Functionality:**
- Instantiates APB slave (with optional CDC)
- Connects register interface to timer core
- Routes interrupts to outputs

---

#### 2. hpet_core (Timer Logic)

**File:** `projects/components/apb_hpet/rtl/hpet_core.sv`

**Purpose:** Implements main counter, timer comparators, and interrupt generation.

**Features:**

1. **64-bit Main Counter**
   - Free-running counter
   - Increments every `hpet_clk` cycle when `hpet_enable=1`
   - Read/write access via registers
   - Wraps to 0 on overflow

2. **Per-Timer Comparators**
   - 64-bit comparator registers
   - Independent per-timer configuration
   - Support for one-shot and periodic modes

3. **Timer Fire Detection**
   - Fires when `counter >= comparator`
   - Rising-edge detection (fires on first match)
   - Interrupt assertion

4. **Periodic Mode Auto-Increment**
   - After fire, `comparator += period`
   - Enables repeating timers without software intervention

**Internal Logic:**

```systemverilog
// Main counter increment
always_ff @(posedge hpet_clk or negedge hpet_rst_n) begin
    if (!hpet_rst_n)
        main_counter <= '0;
    else if (counter_write)
        main_counter <= counter_wdata;
    else if (hpet_enable)
        main_counter <= main_counter + 1;
end

// Timer fire detection (per timer)
for (i = 0; i < NUM_TIMERS; i++) begin
    // Fire condition
    assign timer_fire[i] = timer_enable[i] &&
                          (main_counter >= timer_comparator[i]);

    // Interrupt generation
    always_ff @(posedge hpet_clk or negedge hpet_rst_n) begin
        if (!hpet_rst_n)
            timer_irq[i] <= 1'b0;
        else if (timer_int_clear[i])
            timer_irq[i] <= 1'b0;
        else if (timer_fire[i] && timer_int_enable[i])
            timer_irq[i] <= 1'b1;
    end

    // Periodic mode: auto-increment comparator
    always_ff @(posedge hpet_clk) begin
        if (timer_fire[i] && timer_type[i]) // type=1 is periodic
            timer_comparator[i] <= timer_comparator[i] + timer_period[i];
    end
end
```

---

#### 3. hpet_config_regs (Register Wrapper)

**File:** `projects/components/apb_hpet/rtl/hpet_config_regs.sv`

**Purpose:** Wrapper connecting PeakRDL-generated registers to HPET core.

**Key Features:**

1. **PeakRDL Integration**
   - Instantiates `hpet_regs` module (PeakRDL-generated)
   - Maps APB cmd/rsp interface to register file
   - Handles register read/write operations

2. **Edge Detection for Writes**
   - Generates write strobes on register updates
   - Prevents multiple triggers from level-sensitive signals
   - Example: `timer_comp_write` pulse on comparator write

3. **Per-Timer Data Buses**
   - Dedicated data bus for each timer
   - Prevents corruption when multiple timers configured
   - Ensures clean timer updates

**Implementation:**

```systemverilog
// Edge detection for timer comparator writes
for (i = 0; i < NUM_TIMERS; i++) begin
    edge_detect u_timer_comp_wr (
        .i_clk    (pclk),
        .i_signal (hwif.timer[i].comparator.swacc), // PeakRDL write strobe
        .o_pulse  (timer_comp_write[i])             // Edge-detected pulse
    );
end

// Per-timer data buses (prevent corruption)
for (i = 0; i < NUM_TIMERS; i++) begin
    assign timer_comp_wdata[i] = {
        hwif.timer[i].comparator_hi.value,
        hwif.timer[i].comparator_lo.value
    };
end
```

---

#### 4. hpet_regs (PeakRDL Generated)

**Files:**
- `projects/components/apb_hpet/rtl/hpet_regs.sv`
- `projects/components/apb_hpet/rtl/hpet_regs_pkg.sv`

**Purpose:** APB register file auto-generated from SystemRDL specification.

**Generation:**

```bash
# SystemRDL specification location
projects/components/apb_hpet/rtl/peakrdl/hpet_regs.rdl

# Generate command
peakrdl regblock hpet_regs.rdl --cpuif apb4 -o ../

# Generated files
# - hpet_regs.sv (register file RTL)
# - hpet_regs_pkg.sv (package with field definitions)
```

**Register Interface:**

PeakRDL generates a hardware interface (`hwif`) with:
- Field values (`.value`)
- Software access strobes (`.swacc`)
- Hardware write enables (`.we`, `.wel`)
- Interrupt/status signals

---

## Register Map

### Address Map

| Address | Register | Access | Description |
|---------|----------|--------|-------------|
| `0x000` | HPET_CONFIG | RW | Global configuration |
| `0x004` | HPET_STATUS | RW (W1C) | Timer interrupt status |
| `0x008` | HPET_COUNTER_LO | RW | Main counter [31:0] |
| `0x00C` | HPET_COUNTER_HI | RW | Main counter [63:32] |
| `0x010` | HPET_CAPABILITIES | RO | Hardware capabilities |
| `0x100 + i*0x20` | TIMER[i]_CONFIG | RW | Timer i configuration |
| `0x104 + i*0x20` | TIMER[i]_COMPARATOR_LO | RW | Timer i comparator [31:0] |
| `0x108 + i*0x20` | TIMER[i]_COMPARATOR_HI | RW | Timer i comparator [63:32] |

**Note:** `i` ranges from 0 to `NUM_TIMERS-1`

### Register Descriptions

#### HPET_CONFIG (0x000)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| [31:2] | Reserved | RO | 0 | Reserved for future use |
| [1] | legacy_mapping | RW | 0 | Legacy interrupt routing (reserved) |
| [0] | enable | RW | 0 | **HPET Enable:** 1=enabled, 0=disabled |

**Key Behavior:**
- `enable=0`: Counter stops, timers inactive
- `enable=1`: Counter increments, timers operational

---

#### HPET_STATUS (0x004)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| [31:NUM_TIMERS] | Reserved | RO | 0 | Reserved |
| [NUM_TIMERS-1:0] | timer_int_status | RW (W1C) | 0 | **Timer Interrupt Status** |

**Key Behavior:**
- **Read:** Returns current interrupt status for each timer
- **Write:** Write `1` to bit `i` to clear interrupt `i` (W1C = Write-1-to-Clear)
- **Sticky:** Bits remain set until cleared by software

**Example:**
```c
// Read status
uint32_t status = hpet_read(HPET_STATUS);

// Check if timer 2 fired
if (status & (1 << 2)) {
    // Timer 2 interrupt active

    // Clear timer 2 interrupt (W1C)
    hpet_write(HPET_STATUS, (1 << 2));
}
```

---

#### HPET_COUNTER_LO/HI (0x008, 0x00C)

| Register | Bits | Access | Reset | Description |
|----------|------|--------|-------|-------------|
| COUNTER_LO | [31:0] | RW | 0 | Main counter bits [31:0] |
| COUNTER_HI | [31:0] | RW | 0 | Main counter bits [63:32] |

**Key Behavior:**
- **Read:** Returns current 64-bit counter value
- **Write:** Sets counter to specified value
- **Increment:** Counter increments every `hpet_clk` cycle when `enable=1`
- **Overflow:** Wraps to 0 on overflow

**64-bit Counter Access:**
```c
// Read 64-bit counter
uint32_t lo = hpet_read(HPET_COUNTER_LO);
uint32_t hi = hpet_read(HPET_COUNTER_HI);
uint64_t counter = ((uint64_t)hi << 32) | lo;

// Write 64-bit counter
hpet_write(HPET_COUNTER_LO, counter & 0xFFFFFFFF);
hpet_write(HPET_COUNTER_HI, counter >> 32);
```

---

#### HPET_CAPABILITIES (0x010)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| [31:24] | num_timers | RO | NUM_TIMERS | **Number of Timers** (parameter) |
| [23:16] | vendor_id[15:8] | RO | VENDOR_ID[15:8] | Vendor ID (high byte) |
| [15:8] | vendor_id[7:0] | RO | VENDOR_ID[7:0] | Vendor ID (low byte) |
| [7:0] | revision_id | RO | REVISION_ID[7:0] | Revision ID |

**Key Behavior:**
- **Read-Only:** Cannot be modified by software
- **Constant:** Values set by RTL parameters

**Software Discovery:**
```c
uint32_t caps = hpet_read(HPET_CAPABILITIES);
uint8_t num_timers = (caps >> 24) & 0xFF;
uint16_t vendor_id = (caps >> 8) & 0xFFFF;
uint8_t revision = caps & 0xFF;

printf("HPET: %d timers, Vendor=0x%04X, Rev=0x%02X\n",
       num_timers, vendor_id, revision);
```

---

#### TIMER[i]_CONFIG (0x100 + i*0x20)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| [31:4] | Reserved | RO | 0 | Reserved |
| [3] | size | RW | 0 | **Timer Size:** 0=32-bit, 1=64-bit (reserved) |
| [2] | type | RW | 0 | **Timer Type:** 0=one-shot, 1=periodic |
| [1] | int_enable | RW | 0 | **Interrupt Enable:** 1=enabled, 0=disabled |
| [0] | enable | RW | 0 | **Timer Enable:** 1=enabled, 0=disabled |

**Key Behavior:**
- `enable=0`: Timer inactive, no comparisons
- `enable=1`: Timer active, fires when `counter >= comparator`
- `type=0` (one-shot): Fire once, then stop
- `type=1` (periodic): Fire repeatedly, auto-increment comparator
- `int_enable=1`: Assert `timer_irq[i]` on fire

**Configuration Examples:**
```c
// One-shot timer with interrupt
hpet_write(TIMER0_CONFIG, 0x3);  // enable=1, int_enable=1, type=0

// Periodic timer with interrupt
hpet_write(TIMER1_CONFIG, 0x7);  // enable=1, int_enable=1, type=1

// Polling mode (no interrupt)
hpet_write(TIMER2_CONFIG, 0x1);  // enable=1, int_enable=0
```

---

#### TIMER[i]_COMPARATOR_LO/HI (0x104 + i*0x20, 0x108 + i*0x20)

| Register | Bits | Access | Reset | Description |
|----------|------|--------|-------|-------------|
| COMPARATOR_LO | [31:0] | RW | 0 | Timer i comparator [31:0] |
| COMPARATOR_HI | [31:0] | RW | 0 | Timer i comparator [63:32] |

**Key Behavior:**
- **One-Shot Mode:** Timer fires once when `counter >= comparator`
- **Periodic Mode:**
  - First fire at `counter = comparator` (initial value)
  - Auto-increments: `comparator += period` after each fire
  - Period = initial comparator value

**Periodic Timer Example:**
```c
// Configure 1ms periodic timer @ 10MHz HPET clock
// Period = 10,000 clocks = 1ms

// Set initial comparator (defines period)
hpet_write(TIMER0_COMPARATOR_LO, 10000);
hpet_write(TIMER0_COMPARATOR_HI, 0);

// Enable periodic mode
hpet_write(TIMER0_CONFIG, 0x7);  // enable=1, int_enable=1, type=1 (periodic)

// Fires at:
// - counter = 10,000 (first fire)
// - counter = 20,000 (second fire, comparator auto-incremented)
// - counter = 30,000 (third fire)
// - ... repeats indefinitely
```

---

## Operation Modes

### One-Shot Mode

**Configuration:**
- `TIMER[i]_CONFIG.type = 0` (one-shot)
- `TIMER[i]_CONFIG.enable = 1`

**Behavior:**

1. Software writes comparator value
2. Timer monitors main counter
3. When `counter >= comparator`, timer fires:
   - `timer_irq[i]` asserts (if `int_enable=1`)
   - `HPET_STATUS[i]` sets
4. Timer remains idle until reconfigured

**Timing Diagram:**

```
Clock     : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__
Counter   : 95    96    97    98    99   100   101   102   103
Comparator: 100   100   100   100   100   100   100   100   100
Fire      : _____________________________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
IRQ       : _____________________________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
STATUS[i] : _____________________________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                                          ↑
                                    Software clears STATUS to de-assert IRQ
```

**Software Sequence:**

```c
// 1. Disable HPET
hpet_write(HPET_CONFIG, 0x0);

// 2. Reset counter
hpet_write(HPET_COUNTER_LO, 0);
hpet_write(HPET_COUNTER_HI, 0);

// 3. Configure timer 0 (one-shot, fire at 1000)
hpet_write(TIMER0_COMPARATOR_LO, 1000);
hpet_write(TIMER0_COMPARATOR_HI, 0);
hpet_write(TIMER0_CONFIG, 0x3);  // enable=1, int_enable=1, type=0

// 4. Enable HPET
hpet_write(HPET_CONFIG, 0x1);

// 5. Wait for interrupt
// ... interrupt fires when counter reaches 1000 ...

// 6. Handle interrupt
uint32_t status = hpet_read(HPET_STATUS);
if (status & 0x1) {
    // Timer 0 fired - handle event

    // Clear interrupt (W1C)
    hpet_write(HPET_STATUS, 0x1);
}
```

---

### Periodic Mode

**Configuration:**
- `TIMER[i]_CONFIG.type = 1` (periodic)
- `TIMER[i]_CONFIG.enable = 1`

**Behavior:**

1. Software writes initial comparator value (defines period)
2. Timer monitors main counter
3. When `counter >= comparator`, timer fires:
   - `timer_irq[i]` asserts (if `int_enable=1`)
   - `HPET_STATUS[i]` sets
   - **Comparator auto-increments:** `comparator += period`
4. Process repeats indefinitely

**Timing Diagram:**

```
Clock     : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__|‾‾|__
Counter   : 95    96    97    98    99   100   101   102   103   104   105
Comparator: 100   100   100   100   100   100   105   105   105   105   105
                                          ↑
                                    Auto-increment: comparator += 5
Fire      : _____________________________|‾‾|__________________________|‾‾|____
IRQ       : _____________________________|‾‾|__________________________|‾‾|____
                                              ↑                            ↑
                                        First fire (100)          Second fire (105)
```

**Key Points:**
- **Period** = Initial comparator value
- **Auto-increment** happens in hardware (no software intervention)
- **Regular intervals** guaranteed (jitter-free)

**Software Sequence:**

```c
// Configure 1ms periodic timer @ 10MHz HPET clock
// Period = 10,000 clocks = 1ms

// 1. Disable HPET
hpet_write(HPET_CONFIG, 0x0);

// 2. Reset counter
hpet_write(HPET_COUNTER_LO, 0);
hpet_write(HPET_COUNTER_HI, 0);

// 3. Configure timer 0 (periodic, 10,000 clock period)
hpet_write(TIMER0_COMPARATOR_LO, 10000);
hpet_write(TIMER0_COMPARATOR_HI, 0);
hpet_write(TIMER0_CONFIG, 0x7);  // enable=1, int_enable=1, type=1 (periodic)

// 4. Enable HPET
hpet_write(HPET_CONFIG, 0x1);

// 5. Interrupt handler (called every 1ms)
void timer0_isr(void) {
    // Handle periodic event

    // Clear interrupt (W1C)
    hpet_write(HPET_STATUS, 0x1);

    // Next interrupt will fire in 1ms (hardware auto-increments comparator)
}
```

---

### Multiple Independent Timers

**Key Features:**
- All timers share same main counter
- Each timer has independent comparator
- Each timer has independent configuration
- Timers can mix one-shot and periodic modes

**Example: 3 Timers with Different Periods**

```c
// Timer 0: 100 clocks (one-shot)
// Timer 1: 200 clocks (periodic)
// Timer 2: 700 clocks (one-shot)

// Disable HPET
hpet_write(HPET_CONFIG, 0x0);

// Reset counter
hpet_write(HPET_COUNTER_LO, 0);
hpet_write(HPET_COUNTER_HI, 0);

// Configure Timer 0 (one-shot, 100 clocks)
hpet_write(TIMER0_COMPARATOR_LO, 100);
hpet_write(TIMER0_CONFIG, 0x3);  // one-shot, interrupt enabled

// Configure Timer 1 (periodic, 200 clocks)
hpet_write(TIMER1_COMPARATOR_LO, 200);
hpet_write(TIMER1_CONFIG, 0x7);  // periodic, interrupt enabled

// Configure Timer 2 (one-shot, 700 clocks)
hpet_write(TIMER2_COMPARATOR_LO, 700);
hpet_write(TIMER2_CONFIG, 0x3);  // one-shot, interrupt enabled

// Enable HPET
hpet_write(HPET_CONFIG, 0x1);

// Timeline:
// counter =   0: HPET enabled, counter starts incrementing
// counter = 100: Timer 0 fires (one-shot)
// counter = 200: Timer 1 fires (periodic)
// counter = 400: Timer 1 fires again (periodic, comparator = 400)
// counter = 600: Timer 1 fires again (periodic, comparator = 600)
// counter = 700: Timer 2 fires (one-shot)
// counter = 800: Timer 1 fires again (periodic, comparator = 800)
// ... Timer 1 continues firing every 200 clocks ...
```

---

## Clock Domain Crossing

### CDC Configuration

**Parameter:** `CDC_ENABLE`
- **0:** Synchronous clocks (pclk and hpet_clk must be same or synchronous)
- **1:** Asynchronous clocks (pclk and hpet_clk can be completely independent)

### CDC Architecture

**When CDC_ENABLE=0:**
```
APB Interface ──► hpet_regs ──► hpet_core
    (pclk)         (pclk)         (pclk = hpet_clk)
```

**When CDC_ENABLE=1:**
```
APB Interface ──► apb_slave_cdc ──► hpet_regs ──► hpet_core
    (pclk)          (handshake)       (hpet_clk)    (hpet_clk)
```

### CDC Implementation

The `apb_slave_cdc` module provides:

1. **Command CDC (pclk → hpet_clk)**
   - APB write/read requests cross to HPET domain
   - Handshake synchronization ensures safe transfer
   - 2-FF synchronizer chain for metastability protection

2. **Response CDC (hpet_clk → pclk)**
   - Register read data crosses back to APB domain
   - Handshake acknowledgment
   - 2-FF synchronizer chain

**Latency Impact:**
- **No CDC:** 2 pclk cycles for register access
- **With CDC:** 4-6 pclk cycles (handshake overhead)

### Clock Domain Examples

**Example 1: Same Clock**
```systemverilog
// CDC_ENABLE=0
apb_hpet #(
    .NUM_TIMERS(2),
    .CDC_ENABLE(0)
) u_hpet (
    .pclk      (sys_clk),      // 100 MHz
    .presetn   (sys_rst_n),
    .hpet_clk  (sys_clk),      // Same 100 MHz clock
    .hpet_rst_n(sys_rst_n),
    // ...
);
```

**Example 2: Asynchronous Clocks**
```systemverilog
// CDC_ENABLE=1
apb_hpet #(
    .NUM_TIMERS(3),
    .CDC_ENABLE(1)
) u_hpet (
    .pclk      (apb_clk),      // 50 MHz APB clock
    .presetn   (apb_rst_n),
    .hpet_clk  (timer_clk),    // 10 MHz timer clock (async!)
    .hpet_rst_n(timer_rst_n),
    // ...
);
```

### Reset Synchronization

**Important:** Always synchronize resets in each clock domain!

```systemverilog
// APB domain reset synchronizer
reset_sync u_apb_rst_sync (
    .i_clk       (pclk),
    .i_async_rst (async_rst_n),
    .o_sync_rst  (presetn)
);

// HPET domain reset synchronizer
reset_sync u_hpet_rst_sync (
    .i_clk       (hpet_clk),
    .i_async_rst (async_rst_n),
    .o_sync_rst  (hpet_rst_n)
);
```

---

## Integration Guide

### RTL Integration

**Step 1: Add to Filelist**

```tcl
# Dependencies (from rtl/common/)
${RTL_ROOT}/common/counter_bin.sv
${RTL_ROOT}/common/fifo_control.sv

# Dependencies (from rtl/amba/gaxi/)
${RTL_ROOT}/amba/gaxi/gaxi_skid_buffer.sv
${RTL_ROOT}/amba/gaxi/gaxi_fifo_sync.sv
${RTL_ROOT}/amba/shared/cdc_handshake.sv

# Dependencies (from rtl/amba/apb/)
${RTL_ROOT}/amba/apb/apb_slave.sv
${RTL_ROOT}/amba/apb/apb_slave_cdc.sv

# Dependencies (PeakRDL adapter)
${RTL_ROOT}/amba/adapters/peakrdl_to_cmdrsp.sv

# APB HPET RTL
${RTL_ROOT}/projects/components/apb_hpet/rtl/hpet_regs_pkg.sv
${RTL_ROOT}/projects/components/apb_hpet/rtl/hpet_regs.sv
${RTL_ROOT}/projects/components/apb_hpet/rtl/hpet_core.sv
${RTL_ROOT}/projects/components/apb_hpet/rtl/hpet_config_regs.sv
${RTL_ROOT}/projects/components/apb_hpet/rtl/apb_hpet.sv
```

**Step 2: Instantiate in Design**

```systemverilog
// 2-timer configuration (Intel-like)
apb_hpet #(
    .NUM_TIMERS   (2),
    .VENDOR_ID    (16'h8086),  // Intel
    .REVISION_ID  (16'h0001),
    .CDC_ENABLE   (0)          // Synchronous clocks
) u_hpet (
    // APB Interface
    .pclk         (apb_clk),
    .presetn      (apb_rst_n),
    .paddr        (apb_paddr[11:0]),  // 12-bit address (4KB space)
    .psel         (hpet_psel),
    .penable      (apb_penable),
    .pwrite       (apb_pwrite),
    .pwdata       (apb_pwdata),
    .pready       (hpet_pready),
    .prdata       (hpet_prdata),
    .pslverr      (hpet_pslverr),

    // HPET Clock Domain
    .hpet_clk     (apb_clk),      // Same clock (CDC_ENABLE=0)
    .hpet_rst_n   (apb_rst_n),

    // Interrupts
    .timer_irq    (hpet_timer_irq[1:0])
);

// Connect to interrupt controller
assign irq_sources[IRQ_HPET_TIMER0] = hpet_timer_irq[0];
assign irq_sources[IRQ_HPET_TIMER1] = hpet_timer_irq[1];
```

---

### Software Integration

**Step 1: Define Register Addresses**

```c
// HPET base address (from memory map)
#define HPET_BASE 0x40010000

// Register offsets
#define HPET_CONFIG          (HPET_BASE + 0x000)
#define HPET_STATUS          (HPET_BASE + 0x004)
#define HPET_COUNTER_LO      (HPET_BASE + 0x008)
#define HPET_COUNTER_HI      (HPET_BASE + 0x00C)
#define HPET_CAPABILITIES    (HPET_BASE + 0x010)

// Timer registers (stride = 0x20)
#define TIMER_CONFIG(i)        (HPET_BASE + 0x100 + (i)*0x20)
#define TIMER_COMPARATOR_LO(i) (HPET_BASE + 0x104 + (i)*0x20)
#define TIMER_COMPARATOR_HI(i) (HPET_BASE + 0x108 + (i)*0x20)

// CONFIG bits
#define HPET_CONFIG_ENABLE (1 << 0)

// TIMER_CONFIG bits
#define TIMER_CONFIG_ENABLE     (1 << 0)
#define TIMER_CONFIG_INT_ENABLE (1 << 1)
#define TIMER_CONFIG_PERIODIC   (1 << 2)
```

**Step 2: Initialize HPET**

```c
void hpet_init(void) {
    // 1. Disable HPET
    REG32(HPET_CONFIG) = 0;

    // 2. Reset counter
    REG32(HPET_COUNTER_LO) = 0;
    REG32(HPET_COUNTER_HI) = 0;

    // 3. Read capabilities
    uint32_t caps = REG32(HPET_CAPABILITIES);
    uint8_t num_timers = (caps >> 24) & 0xFF;
    uint16_t vendor_id = (caps >> 8) & 0xFFFF;
    uint8_t revision = caps & 0xFF;

    printf("HPET: %d timers, vendor=0x%04X, rev=0x%02X\n",
           num_timers, vendor_id, revision);

    // 4. Enable HPET
    REG32(HPET_CONFIG) = HPET_CONFIG_ENABLE;
}
```

**Step 3: Configure Timer (One-Shot)**

```c
void hpet_oneshot(uint8_t timer_id, uint64_t delay_clocks) {
    // Disable HPET for configuration
    REG32(HPET_CONFIG) = 0;

    // Reset counter
    REG32(HPET_COUNTER_LO) = 0;
    REG32(HPET_COUNTER_HI) = 0;

    // Set comparator
    REG32(TIMER_COMPARATOR_LO(timer_id)) = delay_clocks & 0xFFFFFFFF;
    REG32(TIMER_COMPARATOR_HI(timer_id)) = delay_clocks >> 32;

    // Enable timer (one-shot with interrupt)
    REG32(TIMER_CONFIG(timer_id)) = TIMER_CONFIG_ENABLE |
                                    TIMER_CONFIG_INT_ENABLE;

    // Enable HPET
    REG32(HPET_CONFIG) = HPET_CONFIG_ENABLE;
}
```

**Step 4: Configure Timer (Periodic)**

```c
void hpet_periodic(uint8_t timer_id, uint64_t period_clocks) {
    // Disable HPET for configuration
    REG32(HPET_CONFIG) = 0;

    // Reset counter
    REG32(HPET_COUNTER_LO) = 0;
    REG32(HPET_COUNTER_HI) = 0;

    // Set comparator (defines period)
    REG32(TIMER_COMPARATOR_LO(timer_id)) = period_clocks & 0xFFFFFFFF;
    REG32(TIMER_COMPARATOR_HI(timer_id)) = period_clocks >> 32;

    // Enable timer (periodic with interrupt)
    REG32(TIMER_CONFIG(timer_id)) = TIMER_CONFIG_ENABLE |
                                    TIMER_CONFIG_INT_ENABLE |
                                    TIMER_CONFIG_PERIODIC;

    // Enable HPET
    REG32(HPET_CONFIG) = HPET_CONFIG_ENABLE;
}
```

**Step 5: Interrupt Handler**

```c
void hpet_irq_handler(void) {
    // Read status register
    uint32_t status = REG32(HPET_STATUS);

    // Check each timer
    for (uint8_t i = 0; i < num_hpet_timers; i++) {
        if (status & (1 << i)) {
            // Timer i fired - call handler
            hpet_timer_callback[i]();

            // Clear interrupt (W1C)
            REG32(HPET_STATUS) = (1 << i);
        }
    }
}
```

---

## Verification

### Test Coverage

**Test Hierarchy:**

| Level | Tests | Description | Duration |
|-------|-------|-------------|----------|
| Basic | 4 | Register access, simple operations | <10s each |
| Medium | 5 | Complex features, 64-bit, multiple timers | 10-60s each |
| Full | 3 | Stress testing, CDC, edge cases | 60-180s each |

**Total:** 12 tests per configuration

### Test Configurations

| Configuration | NUM_TIMERS | VENDOR_ID | REV_ID | CDC | Basic | Medium | Full | Overall |
|---------------|------------|-----------|--------|-----|-------|--------|------|---------|
| 2-timer Intel-like | 2 | 0x8086 | 1 | 0 | 4/4 | 5/5 | 3/3 | 12/12 ✅ |
| 3-timer AMD-like | 3 | 0x1022 | 2 | 0 | 4/4 | 5/5 | 3/3 | 12/12 ✅ |
| 8-timer custom | 8 | 0xABCD | 16 | 0 | 4/4 | 5/5 | 2/3 | 11/12 ⚠️ |
| 2-timer Intel-like CDC | 2 | 0x8086 | 1 | 1 | 4/4 | 5/5 | 3/3 | 12/12 ✅ |
| 3-timer AMD-like CDC | 3 | 0x1022 | 2 | 1 | 4/4 | 5/5 | 3/3 | 12/12 ✅ |
| 8-timer custom CDC | 8 | 0xABCD | 16 | 1 | 4/4 | 5/5 | 3/3 | 12/12 ✅ |

**Overall Status:** ✅ **5/6 configurations at 100%, 1 at 92%**

### Running Tests

```bash
# Run all HPET tests
pytest projects/components/apb_hpet/dv/tests/ -v

# Run specific configuration
pytest "projects/components/apb_hpet/dv/tests/test_apb_hpet.py::test_hpet[2-32902-1-0-full-2-timer Intel-like]" -v

# Run basic tests only
pytest projects/components/apb_hpet/dv/tests/ -v -m basic

# Run medium tests only
pytest projects/components/apb_hpet/dv/tests/ -v -m medium

# Run full tests only
pytest projects/components/apb_hpet/dv/tests/ -v -m full
```

---

## Performance

### Resource Usage

**Post-Synthesis Estimates:**

| Configuration | LUTs | FFs | BRAM | Fmax (MHz) |
|---------------|------|-----|------|------------|
| 2-timer (no CDC) | ~500 | ~300 | 0 | >200 |
| 3-timer (no CDC) | ~650 | ~400 | 0 | >200 |
| 8-timer (no CDC) | ~1000 | ~700 | 0 | >150 |
| 2-timer (CDC) | ~650 | ~450 | 0 | >150 |
| 8-timer (CDC) | ~1200 | ~800 | 0 | >100 |

**Scaling:**
- **Per timer:** ~50 LUTs, ~40 FFs
- **CDC overhead:** ~150 LUTs, ~150 FFs

### Timing Characteristics

**Latency:**

| Operation | No CDC | With CDC |
|-----------|--------|----------|
| Register Read | 2 pclk | 4-6 pclk |
| Register Write | 2 pclk | 4-6 pclk |
| Counter Increment | 1 hpet_clk | 1 hpet_clk |
| Timer Fire | 1 hpet_clk | 1 hpet_clk |

**Interrupt Latency:**
- **Fire to IRQ assertion:** 1 hpet_clk cycle
- **Clear to IRQ de-assertion:** 1 hpet_clk cycle

---

## Known Issues

### Issue 1: 8-Timer Stress Test Timeout (Non-CDC)

**Configuration:** 8-timer, CDC_ENABLE=0
**Test:** "All Timers Stress" (Full test level)
**Impact:** Low (single test, CDC version passes)
**Status:** Optional fix

**Description:**
The 8-timer non-CDC configuration times out in the "All Timers Stress" full test. This is a timeout issue in the test, not an RTL bug. The CDC-enabled 8-timer passes the same test.

**Workaround:**
- Use CDC-enabled 8-timer configuration for production
- Or increase test timeout

**Root Cause:**
Test timeout calculation doesn't account for sequential APB transactions in stress scenario.

**See:** `projects/components/apb_hpet/known_issues/active/8timer_stress_timeout.md`

---

## References

### Internal Documentation
- **PRD:** [projects/components/apb_hpet/PRD.md](../../../projects/components/apb_hpet/PRD.md)
- **AI Guide:** [projects/components/apb_hpet/CLAUDE.md](../../../projects/components/apb_hpet/CLAUDE.md)
- **Tasks:** [projects/components/apb_hpet/TASKS.md](../../../projects/components/apb_hpet/TASKS.md)
- **Implementation Status:** [projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md](../../../projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md)

### External Standards
- **AMBA APB Specification v2.0** - ARM IHI 0024
- **IA-PC HPET Specification 1.0a** - Intel/Microsoft (architectural reference)
- **SystemRDL 2.0** - Accellera

### Tools
- **PeakRDL:** [https://peakrdl.readthedocs.io/](https://peakrdl.readthedocs.io/)
- **CocoTB:** [https://docs.cocotb.org/](https://docs.cocotb.org/)
- **Verilator:** [https://verilator.org/](https://verilator.org/)

---

**Document Version:** 1.0
**Last Review:** 2025-10-17
**Maintained By:** RTL Design Sherpa Project
