# RLB (Retro Legacy Blocks) - FPGA Implementation Guide

**Date:** 2025-11-16  
**Purpose:** Explain RLB blocks and FPGA implementation compatibility

---

## What Are RLB (Retro Legacy Blocks)?

### Overview

**Retro Legacy Blocks** are modern implementations of classic PC/embedded system peripherals, designed as reusable IP cores with APB interfaces. They provide functionality compatible with legacy systems but implemented in clean, modern SystemVerilog.

### Purpose

**Educational:**
- Learn how classic PC peripherals work internally
- Understand interrupt controllers, timers, power management
- Study register-based peripheral design
- Practice verification of complex protocols

**Practical:**
- Build soft-core SoC systems on FPGAs
- Create retro computer replicas (PC-compatible)
- Implement embedded systems with familiar peripherals
- Rapid prototyping of control systems

**Industrial:**
- Reusable IP cores for custom SoCs
- Known-good peripheral implementations
- Well-documented, tested components
- Modern coding standards with legacy compatibility

---

## Implemented RLB Modules

### ✅ Complete Modules

#### 1. **HPET** (High Precision Event Timer)
- **Purpose:** High-resolution timer (sub-microsecond precision)
- **Features:** Multiple timers, one-shot/periodic modes, 64-bit counters
- **PC Equivalent:** Modern replacement for PIT
- **Use Cases:** Precise timing, event scheduling, benchmarking

#### 2. **PIT_8254** (Programmable Interval Timer)
- **Purpose:** Classic PC timer (3 channels)
- **Features:** Mode 0-5 operation, binary/BCD counting
- **PC Equivalent:** Intel 8254 PIT
- **Use Cases:** System tick, speaker control, legacy PC compatibility

#### 3. **RTC** (Real-Time Clock)
- **Purpose:** Calendar and alarm functions
- **Features:** Time/date tracking, alarm, periodic interrupts
- **PC Equivalent:** MC146818 / DS12887
- **Use Cases:** Wall-clock time, wake-on-alarm, timestamping

#### 4. **PIC_8259** (Programmable Interrupt Controller)
- **Purpose:** Legacy interrupt management
- **Features:** 8 IRQ inputs, priority, cascading, masking
- **PC Equivalent:** Intel 8259A PIC
- **Use Cases:** Legacy PC interrupts, simple systems

#### 5. **SMBus** (System Management Bus)
- **Purpose:** Low-speed system management communication
- **Features:** I2C/SMBus 2.0, master/slave, PEC, FIFOs
- **PC Equivalent:** Modern motherboard SMBus controller
- **Use Cases:** Sensor monitoring, battery management, system config

#### 6. **PM_ACPI** (Power Management ACPI)
- **Purpose:** Advanced power management
- **Features:** PM timer, power states (S0/S1/S3), GPE, clock gating, power domains
- **PC Equivalent:** ACPI PM controller
- **Use Cases:** Low-power systems, battery devices, sleep/wake, clock control

#### 7. **IOAPIC** (I/O Advanced Programmable Interrupt Controller)
- **Purpose:** Advanced interrupt routing
- **Features:** 24 IRQs, redirection table, edge/level, priority, EOI
- **PC Equivalent:** Intel 82093AA I/O APIC
- **Use Cases:** Multi-processor systems, flexible IRQ routing, modern PCs

---

## FPGA Implementation - Nexys A7 / Genesys2

### Can RLB Be Implemented on These Boards? **YES! ✅**

All RLB modules are **100% compatible** with Nexys A7 and Genesys2 FPGAs.

### Target FPGA Specifications

#### Nexys A7 (Artix-7)
- **FPGA:** XC7A100T-1CSG324C (or XC7A50T)
- **Logic Cells:** 101,440 (A100T) or 52,160 (A50T)
- **Block RAM:** 4,860 Kb
- **Clock:** 100 MHz oscillator
- **I/O:** Extensive (PMOD, switches, LEDs, UART, etc.)
- **Verdict:** ✅ **Excellent fit for full RLB system**

#### Genesys 2 (Kintex-7)
- **FPGA:** XC7K325T-2FFG900C
- **Logic Cells:** 326,080
- **Block RAM:** 16,020 Kb
- **Clock:** 200 MHz oscillator
- **I/O:** Very extensive
- **Verdict:** ✅ **More than sufficient, ideal for complex SoC**

### Resource Usage Estimates

**Per Module (Approximate):**

| Module | LUTs | FFs | BRAM | Notes |
|--------|------|-----|------|-------|
| HPET | ~800-1200 | ~600-900 | 0 | Multi-timer, 64-bit counters |
| PIT_8254 | ~400-600 | ~300-500 | 0 | 3 channels, modes |
| RTC | ~300-500 | ~250-400 | 0 | Time/date logic |
| PIC_8259 | ~200-400 | ~150-300 | 0 | Simple priority logic |
| SMBus | ~600-900 | ~500-700 | 0.5 | FIFOs, protocol FSM |
| PM_ACPI | ~500-800 | ~400-600 | 0 | Power FSM, GPE |
| IOAPIC | ~800-1200 | ~600-900 | 0 | 24 IRQs, redirection |

**Total RLB System (~5500 LUTs, ~4300 FFs):**
- **Nexys A7-100T:** ~5% logic utilization ✅ Plenty of room
- **Nexys A7-50T:** ~11% logic utilization ✅ Still comfortable
- **Genesys 2:** ~2% logic utilization ✅ Massive headroom

### What Can Fit on These Boards?

**Nexys A7-100T Can Support:**
- ✅ All 7 RLB modules
- ✅ MicroBlaze or RISC-V soft processor
- ✅ DDR2 controller
- ✅ Ethernet MAC
- ✅ VGA/HDMI display controller
- ✅ USB interface
- ✅ Audio codec
- **Result:** Complete retro-PC or modern embedded system

**Genesys 2 Can Support:**
- ✅ Everything above PLUS:
- ✅ Multiple soft processors
- ✅ PCIe endpoint
- ✅ High-speed interfaces
- ✅ Complex video processing
- **Result:** Professional-grade SoC development platform

---

## RLB System Integration on FPGA

### Typical FPGA System Architecture

```
┌─────────────────────────────────────────────────────────┐
│ FPGA Top Level (Nexys A7 or Genesys 2)                 │
│                                                          │
│  ┌──────────────┐          ┌──────────────┐            │
│  │ Soft CPU     │          │ DDR2/3       │            │
│  │ (MicroBlaze/ │◄────────►│ Controller   │◄───► DRAM │
│  │  RISC-V)     │   AXI    │              │            │
│  └──────┬───────┘          └──────────────┘            │
│         │ APB                                            │
│         ▼                                                │
│  ┌──────────────────────────────────────┐              │
│  │ APB Crossbar (apb_xbar)              │              │
│  └──┬───┬───┬───┬───┬───┬───┬──────────┘              │
│     │   │   │   │   │   │   │                           │
│   ┌─▼─┐ │   │   │   │   │   │   [More peripherals]     │
│   │HPT│ │   │   │   │   │   │                           │
│   │ ET│ │   │   │   │   │   │                           │
│   └─┬─┘ │   │   │   │   │   │                           │
│     │IRQ│   │   │   │   │   │                           │
│  ┌──▼───▼───▼───▼───▼───▼───▼──────┐                   │
│  │ IOAPIC or PIC_8259               │                   │
│  │ (Interrupt Aggregation)          │                   │
│  └──────────┬────────────────────────┘                   │
│            IRQ                                            │
│             └──────────► CPU Interrupt                    │
│                                                           │
│  External Connections:                                    │
│  ├─ GPIO ◄───► PMOD ports, switches, LEDs               │
│  ├─ UART ◄───► USB-UART bridge                          │
│  ├─ SMBus ◄──► I2C sensors, EEPROMs                     │
│  └─ PM_ACPI ◄► Power management signals                  │
└───────────────────────────────────────────────────────────┘
```

### Example Use Cases on FPGAs

#### 1. **Retro PC Replica**
Build a PC-compatible system on FPGA:
- Soft x86 core (or compatible RISC-V with x86 emulation)
- All RLB peripherals for PC compatibility
- VGA output for display
- PS/2 keyboard/mouse
- Run DOS, early Windows, Linux

#### 2. **Embedded Control System**
Industrial/automotive control:
- RISC-V processor
- HPET for precise timing
- GPIO for sensors/actuators
- SMBus for temperature/voltage monitoring
- PM_ACPI for power optimization
- UART for debug/communication

#### 3. **Education Platform**
Learn computer architecture:
- Study peripheral internals
- Practice interrupt handling
- Understand power management
- Experiment with different configurations
- Debug with real hardware

#### 4. **SoC Prototyping**
Rapid prototyping:
- Test peripheral configurations
- Validate interrupt routing
- Optimize power consumption
- Benchmark performance
- Hardware/software co-development

---

## Nexys A7 Specific Integration

### Available Resources on Nexys A7

**Peripherals Already on Board:**
- 16 switches (GPIO inputs)
- 16 LEDs (GPIO outputs)
- 5 push buttons
- 7-segment displays (4 digits)
- USB-UART bridge
- PMOD connectors
- VGA output
- Microphone
- Speaker
- Temperature sensor
- Accelerometer

### How RLB Modules Map to Nexys A7

| RLB Module | Nexys A7 Resource | Connection |
|------------|-------------------|------------|
| **GPIO** | Switches, LEDs, Buttons | Direct mapping |
| **UART_16550** | USB-UART bridge | FT2232HQ chip |
| **HPET** | Internal timing | No external pins needed |
| **PIT_8254** | Internal timing | Timer/speaker |
| **RTC** | Internal clock | Optional ext crystal |
| **PIC/IOAPIC** | Internal routing | IRQ aggregation |
| **SMBus** | I2C PMOD | Via I2C PMOD adapter |
| **PM_ACPI** | Power control | Clock gates, power logic |

### Example Nexys A7 Top-Level

```systemverilog
module nexys_a7_rlb_system (
    // Clock and reset
    input  wire         clk_100mhz,    // 100 MHz oscillator
    input  wire         cpu_resetn,    // Reset button
    
    // GPIO
    input  wire [15:0]  sw,            // Switches → GPIO inputs
    output wire [15:0]  led,           // LEDs ← GPIO outputs
    input  wire [4:0]   btn,           // Buttons → GPIO/interrupts
    
    // UART
    input  wire         uart_rxd,      // USB-UART RX
    output wire         uart_txd,      // USB-UART TX
    
    // I2C/SMBus (via PMOD)
    inout  wire         smbus_sda,
    inout  wire         smbus_scl,
    
    // 7-segment display
    output wire [6:0]   seg,
    output wire [7:0]   an,
    
    // VGA (optional)
    output wire [3:0]   vga_r, vga_g, vga_b,
    output wire         vga_hs, vga_vs
);

    // Instantiate soft processor (MicroBlaze, RISC-V, etc.)
    // Instantiate APB crossbar
    // Instantiate all RLB modules  
    // Connect to board resources
    
endmodule
```

---

## Implementation Recommendations

### For Nexys A7-100T

**Recommended RLB Configuration:**
```
✅ HPET        - System timing
✅ PIT_8254    - Legacy timer for compatibility
✅ RTC         - Real-time clock
✅ PIC_8259    - Simple interrupt controller (OR IOAPIC)
✅ GPIO        - Board I/O (switches, LEDs, buttons)
✅ UART_16550  - Serial communication
✅ SMBus       - I2C peripherals
⚠️ PM_ACPI     - Optional (if power features needed)
```

**Resource Budget:**
- RLB modules: ~6,000 LUTs, ~5,000 FFs
- MicroBlaze: ~2,000-3,000 LUTs
- DDR2 Controller: ~2,000 LUTs
- VGA/Display: ~1,000 LUTs
- **Total:** ~11,000-12,000 LUTs (11% of XC7A100T) ✅

**Plenty of room for:**
- User applications
- Additional peripherals
- Debug logic
- Custom IP cores

### For Genesys 2

**Can Support Everything:**
- All RLB modules simultaneously
- Multiple soft processors
- Complex memory hierarchy
- High-speed peripherals
- Video processing
- Network interfaces

**Recommended for:**
- Professional SoC development
- Multi-core systems
- High-performance applications
- Complex retro systems (full PC replica)

---

## FPGA-Specific Considerations

### Clock Management

**Nexys A7:**
- 100 MHz main clock → Can generate all needed frequencies
- Use MMCM/PLL for:
  - CPU clock (50-200 MHz)
  - Peripheral clocks (25-100 MHz)
  - Display clocks (25.175 MHz for VGA)
  - USB clock (60 MHz)

**RLB Modules:** Most work at system clock (50-100 MHz), some support CDC for different clocks

### Power Management

**PM_ACPI Use on FPGA:**
- Clock gating controls → Xilin x clock enables
- Power domains → Can't control FPGA power, but can simulate
- Useful for: Power-aware designs, testing, learning ACPI
- Can control external power via GPIO pins

### Interrupt Routing

**IOAPIC vs PIC_8259 Choice:**
- **Simple systems (single CPU):** Use PIC_8259 (smaller)
- **Advanced systems:** Use IOAPIC (more flexible, PC-compatible)
- **Maximum flexibility:** Include both, use jumpers/config

### External Interfaces

**How to Connect RLB to Board Resources:**

1. **GPIO Module:**
   - Inputs: Switches, buttons
   - Outputs: LEDs, 7-segment displays
   - Bidirectional: PMOD I/O pins

2. **UART_16550:**
   - Connect to FT2232HQ USB-UART
   - Baud rate generator uses system clock
   - CTS/RTS for flow control (optional)

3. **SMBus:**
   - Connect to I2C PMOD
   - On-board: Temperature sensor (ADT7420)
   - On-board: Accelerometer (ADXL362)
   - External: I2C EEPROMs, sensors via PMOD

4. **Timers (HPET/PIT):**
   - Internal only, no external pins
   - Can drive speaker output
   - Can generate PWM via GPIO

5. **RTC:**
   - Internal timekeeping
   - Optional: External 32.768 kHz crystal
   - Battery backup simulation

---

## Soft Processor Options

### MicroBlaze (Xilinx)
- **Pros:** Well-supported, debugger, IP integration
- **Cons:** Proprietary, Vivado-specific
- **RLB Compatibility:** ✅ Excellent (APB via AXI interconnect)

### RISC-V (Open Source)
- **Options:** VexRiscv, PicoRV32, Rocket, BOOM
- **Pros:** Open-source, portable, modern ISA
- **Cons:** Need to build toolchain
- **RLB Compatibility:** ✅ Excellent (APB native or via AXI)

### Custom Soft Core
- Can design custom CPU specifically for RLB peripherals
- Full control over instruction set
- Educational value

---

## Step-by-Step FPGA Implementation

### Phase 1: Basic System (Week 1-2)

1. **Create FPGA project** (Vivado for Xilinx)
2. **Add simple processor** (MicroBlaze or RISC-V)
3. **Add APB crossbar** components/apb_xbar/
4. **Add one RLB module** (start with GPIO)
5. **Connect to LEDs/switches**
6. **Test basic register access**

### Phase 2: Expand Peripherals (Week 3-4)

7. **Add UART_16550** → Test serial communication
8. **Add HPET** → Test precise timing
9. **Add PIC_8259 or IOAPIC** → Test interrupts
10. **Add RTC** → Test time keeping

### Phase 3: Advanced Features (Week 5-6)

11. **Add SMBus** → Test I2C communication
12. **Add PM_ACPI** → Test power management
13. **Add all remaining** RLB modules
14. **System integration testing**

### Phase 4: Application Development (Week 7+)

15. **Develop firmware** using RLB peripherals
16. **Test real-world applications**
17. **Optimize and debug**
18. **Hardware/software co-verification**

---

## Example Address Map for FPGA

```
Base Address | Module      | Size | Description
-------------|-------------|------|------------------------
0x4000_0000  | HPET        | 4KB  | High Precision Timer
0x4000_1000  | PIT_8254    | 4KB  | Programmable Interval Timer
0x4000_2000  | RTC         | 4KB  | Real-Time Clock
0x4000_3000  | PIC_8259    | 4KB  | Interrupt Controller
0x4000_4000  | SMBus       | 4KB  | System Management Bus
0x4000_5000  | PM_ACPI     | 4KB  | Power Management
0x4000_6000  | IOAPIC      | 4KB  | I/O APIC
0x4000_7000  | GPIO        | 4KB  | General Purpose I/O
0x4000_8000  | UART_16550  | 4KB  | Serial Port
0x4000_9000  | (Reserved)  | -    | Future expansion
```

All accessible via APB from soft processor.

---

## Software Development

### Bare-Metal Firmware

**Using RLB Modules in C:**
```c
#include "rlb_peripherals.h"

// Initialize system
void system_init(void) {
    // Configure GPIO
    gpio_set_direction(0xFFFF0000);  // Upper 16 = outputs
    
    // Initialize UART
    uart_init(115200);
    uart_puts("System starting...\n");
    
    // Configure HPET timer
    hpet_init();
    hpet_start_timer(0, 1000000);  // 1ms periodic
    
    // Setup interrupts via IOAPIC
    ioapic_configure_irq(14, 0x2E, IRQ_EDGE, 0);  // IDE
    ioapic_configure_irq(15, 0x2F, IRQ_EDGE, 0);  // IDE
    
    // Enable power management
    pm_acpi_init();
}
```

### Operating System Support

**Can Run:**
- **Bare-metal:** Direct hardware access
- **RTOS:** FreeRTOS, Zephyr with RLB drivers
- **Linux:** With proper device drivers for RLB
- **DOS/DOS-compatible:** If using x86-compatible core
- **Custom OS:** Educational OS development

---

## Advantages of RLB on FPGA

### Development Benefits

1. **Rapid Prototyping:** Change peripheral config instantly (no PCB)
2. **Debugging:** ChipScope/ILA for internal signals
3. **Flexibility:** Easy to add/remove peripherals
4. **Cost-Effective:** One board, infinite configurations
5. **Educational:** See everything, change everything

### Technical Benefits

1. **Known-Good IP:** Well-documented, tested peripherals
2. **Standard Interfaces:** APB everywhere, easy integration
3. **Scalable:** Start simple, add complexity
4. **Portable:** Pure SystemVerilog, vendor-independent
5. **Modern Design:** Clean code, proper methodology

### Vs. Microcontroller

**Why FPGA + RLB instead of MCU?**

| Feature | MCU | FPGA + RLB |
|---------|-----|------------|
| Peripherals | Fixed | Infinite flexibility |
| Interrupts | Fixed routing | Programmable (IOAPIC) |
| Timers | Limited count | As many as needed |
| Clock domains | 1-2 | Unlimited with CDC |
| Custom logic | Limited | Full flexibility |
| Learning value | Black box | Full visibility |
| Cost | Lower | Higher but more capable |

---

## Conclusion

### Can RLB Be Used on Nexys A7/Genesys2? **ABSOLUTELY! ✅**

**Perfect Match Because:**
- Plenty of logic resources
- Rich I/O for peripheral connections
- Clock resources for multi-domain design
- Development boards with extensive support
- Educational and professional use

**Recommended Starting Point:**
1. Nexys A7-100T for most projects
2. Genesys 2 for complex/multi-core systems
3. Start with GPIO + UART + HPET
4. Add peripherals incrementally
5. Full RLB system fits comfortably with room to spare

**The RLB modules are specifically designed to be FPGA-friendly and work excellently on these development boards!**

---

**Last Updated:** 2025-11-16  
**Recommendation:** Nexys A7-100T is ideal for complete RLB-based SoC development
