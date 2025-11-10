### APB PIT 8254 - Acronyms and Terminology

#### Acronyms

| Acronym | Definition |
|---------|-----------|
| **AMBA** | Advanced Microcontroller Bus Architecture |
| **APB** | Advanced Peripheral Bus |
| **APB4** | Advanced Peripheral Bus Protocol Version 4 |
| **ASIC** | Application-Specific Integrated Circuit |
| **BCD** | Binary-Coded Decimal |
| **BFM** | Bus Functional Model |
| **CDC** | Clock Domain Crossing |
| **CLK** | Clock |
| **CMD** | Command |
| **CPU** | Central Processing Unit |
| **CW** | Control Word |
| **DUT** | Design Under Test |
| **FIFO** | First-In First-Out |
| **FPGA** | Field-Programmable Gate Array |
| **FSM** | Finite State Machine |
| **HWIF** | Hardware Interface |
| **I/O** | Input/Output |
| **IRQ** | Interrupt Request |
| **LSB** | Least Significant Byte |
| **MSB** | Most Significant Byte |
| **OUT** | Output signal (terminal count indicator) |
| **PC/AT** | Personal Computer/Advanced Technology |
| **PIT** | Programmable Interval Timer |
| **RDL** | Register Description Language |
| **RSP** | Response |
| **RTOS** | Real-Time Operating System |
| **RTL** | Register Transfer Level |
| **RW** | Read/Write |
| **SoC** | System-on-Chip |
| **SystemRDL** | System Register Description Language |
| **TB** | Testbench |
| **W1C** | Write-1-to-Clear |
| **WO** | Write-Only |

#### Terminology

**8254 Compatibility:**
The Intel 8254 Programmable Interval Timer is the original reference specification. APB PIT 8254 maintains functional compatibility for Mode 0 operation while adapting the interface from port I/O to APB protocol.

**Active-Low Reset:**
A reset signal that performs reset when driven to logic 0. The APB PIT uses `presetn` (active-low) following standard APB convention.

**APB Protocol:**
AMBA APB4 is a simple synchronous protocol for low-bandwidth peripheral access. APB transactions consist of:
- **Setup phase**: `psel=1`, `penable=0`
- **Access phase**: `psel=1`, `penable=1`
- **Response**: `pready=1` when slave completes transaction

**BCD Counting:**
Binary-Coded Decimal mode where each 4-bit nibble represents 0-9. For 16-bit counter, BCD mode supports counts from 0000 to 9999 (4 decimal digits). Currently implemented but not yet tested.

**Binary Counting:**
Standard binary mode where full 16-bit range is used: 0 to 65,535 counts.

**Clock Domain Crossing (CDC):**
Transfer of signals between two asynchronous clock domains. When `CDC_ENABLE=1`, the APB PIT includes synchronization logic to safely cross between `pclk` (APB clock) and `pit_clk` (timer clock).

**Clock Enable:**
A signal (`i_clk_en`) that gates counter operation without stopping the clock. When `i_clk_en=0`, counters hold their current value.

**Control Word:**
An 8-bit value written to `PIT_CONTROL` register to configure counter operation. Format follows Intel 8254 specification:
```
[7:6] SC   - Counter Select (00=Counter 0, 01=Counter 1, 10=Counter 2)
[5:4] RW   - Read/Write mode (01=LSB only, 10=MSB only, 11=LSB then MSB)
[3:1] MODE - Counter mode (000=Mode 0, 001-101=Modes 1-5)
[0]   BCD  - 0=Binary, 1=BCD
```

**Counter:**
A 16-bit down-counter that decrements on each clock cycle when enabled. The PIT contains three independent counters (Counter 0, Counter 1, Counter 2).

**GATE Input:**
Per-counter enable signal. When `gate_in[N]=1`, counter N can count (if also enabled globally). When `gate_in[N]=0`, counter N is paused.

**Interrupt on Terminal Count (Mode 0):**
Counter operation mode where OUT signal goes high when count reaches zero, typically used to generate interrupts.

**LSB/MSB Access:**
8254 compatibility feature for byte-by-byte access:
- **LSB only (RW=01)**: Only lower 8 bits accessible
- **MSB only (RW=10)**: Only upper 8 bits accessible
- **LSB then MSB (RW=11)**: Full 16-bit access (recommended for APB)

**NULL_COUNT Flag:**
Status bit indicating no count value has been loaded into a counter. Set to 1 on reset, cleared to 0 when count value written.

**OUT Signal:**
Per-counter output signal indicating terminal count reached. In Mode 0:
- `OUT=0` during counting
- `OUT=1` when count reaches zero

**PeakRDL:**
An open-source toolchain for generating register RTL from SystemRDL descriptions. Used to generate the PIT register file from `pit_regs.rdl`.

**Reload Value:**
The count value written to `COUNTERx_DATA` register. Counter loads this value and begins counting down.

**Terminal Count:**
The state when a counter reaches zero. In Mode 0, this sets the OUT signal high and stops counting.

**Timer Interrupt:**
In this implementation, `timer_irq[N]` outputs are driven by the corresponding OUT signals, providing interrupt capability for system integration.

#### Register Field Access Types

**RO (Read-Only):**
Software can read this field, but writes have no effect. Hardware controls the value.

**WO (Write-Only):**
Software can write this field, but reads return undefined or zero values. Used for command registers.

**RW (Read-Write):**
Software can read and write this field. Hardware may also update the value (e.g., counter readback).

**W1C (Write-1-to-Clear):**
Software writes 1 to clear the bit, writes 0 have no effect. Used for interrupt/status flags. (Note: Not used in PIT, but common in other peripherals)

#### SystemRDL Concepts

**hwif (Hardware Interface):**
The interface between PeakRDL-generated register file and custom RTL logic. Provides:
- `hwif_out`: Register values from SW writes (to hardware)
- `hwif_in`: Hardware values to read back (from hardware)

**regfile:**
SystemRDL construct representing a collection of related registers.

**field:**
Smallest addressable unit within a register, representing specific bits with defined access semantics.

#### Design Architecture Terms

**Three-Layer Architecture:**
The PIT uses a clean separation:
1. **APB Interface Layer** - Protocol conversion and optional CDC
2. **Configuration Layer** - Register file and edge detection
3. **Core Logic Layer** - Counter implementation

**Edge Detection:**
Converting a level signal (register field) to a pulse (write strobe). Critical for triggering actions on register writes without level-sensitive issues.

**cmd/rsp Interface:**
Internal protocol used between APB slave and register adapter:
- **cmd**: Command signals (address, write data, write enable)
- **rsp**: Response signals (read data, valid)

---

**Version:** 1.0
**Last Updated:** 2025-11-08
