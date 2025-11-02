### APB HPET - Acronyms and Terminology

#### Acronyms

| Acronym | Full Term | Description |
|---------|-----------|-------------|
| **AMBA** | Advanced Microcontroller Bus Architecture | ARM's on-chip interconnect specification |
| **APB** | Advanced Peripheral Bus | AMBA low-complexity peripheral bus protocol |
| **CDC** | Clock Domain Crossing | Synchronization between asynchronous clock domains |
| **FSB** | Front Side Bus | Legacy PC architecture bus (not supported in APB HPET) |
| **FSM** | Finite State Machine | Sequential logic controller |
| **HPET** | High Precision Event Timer | Multi-timer peripheral for precise timing |
| **IA-PC** | Intel Architecture - Personal Computer | PC platform specification (architectural reference) |
| **IRQ** | Interrupt Request | Hardware interrupt signal |
| **PIT** | Programmable Interval Timer | Legacy PC timer (8254-compatible) |
| **RO** | Read-Only | Register field cannot be written by software |
| **RTC** | Real-Time Clock | Calendar/time-of-day clock (not emulated by HPET) |
| **RW** | Read-Write | Register field can be read and written |
| **SystemRDL** | System Register Description Language | Industry-standard register specification language |
| **W1C** | Write-1-to-Clear | Register field cleared by writing 1, writing 0 has no effect |
| **WO** | Write-Only | Register field can only be written, reads return undefined |

#### Terminology

**64-bit Counter:**
The main free-running counter that increments on every HPET clock cycle. Provides high-resolution timestamp and comparison base for all timers.

**Comparator:**
Per-timer 64-bit value that defines when a timer should fire. Timer fires when main counter value becomes greater than or equal to comparator value.

**Fire / Fired:**
Event when a timer's comparator matches the main counter value. In one-shot mode, timer fires once. In periodic mode, timer fires repeatedly.

**One-Shot Mode:**
Timer operating mode where the timer fires once when the counter reaches the comparator value, then remains idle until reconfigured.

**Periodic Mode:**
Timer operating mode where the timer fires repeatedly at fixed intervals. After each fire event, the comparator is automatically incremented by the period value.

**Period:**
In periodic mode, the interval (in HPET clock cycles) between timer fires. Stored internally and used for auto-incrementing the comparator.

**PeakRDL:**
Industry-standard toolchain for generating register files from SystemRDL specifications. Used to generate `hpet_regs.sv` from `hpet_regs.rdl`.

**Per-Timer Data Bus:**
Dedicated 64-bit data path for each timer to prevent corruption when multiple timer registers are written in rapid succession.

**Timer Corruption:**
Historical bug where shared data bus allowed one timer's configuration to overwrite another timer's configuration. Fixed by implementing per-timer dedicated data buses.

**Write Strobe:**
Edge-detected pulse generated when software writes to a timer configuration register. Used to sample comparator and configuration data atomically.

#### Register Field Access Types

**RO (Read-Only):**
- Software can read the field
- Software writes are ignored
- Hardware controls the value
- Example: `HPET_CAPABILITIES` register

**RW (Read-Write):**
- Software can read and write the field
- Hardware may also update the value
- Example: `HPET_CONFIG[0]` (enable bit)

**WO (Write-Only):**
- Software can write the field
- Software reads return undefined value
- Hardware uses written value internally
- Example: `HPET_COUNTER_LO/HI` (write from APB domain, read by HPET core)

**W1C (Write-1-to-Clear):**
- Software writes 1 to clear the bit
- Software writes 0 have no effect
- Hardware can set the bit
- Example: `HPET_STATUS` interrupt flags

#### Signal Naming Conventions

**APB Signals:**
All APB signals use standard AMBA naming with `p` prefix:
- `pclk` - APB clock
- `presetn` - APB reset (active-low)
- `paddr` - APB address bus
- `psel` - APB select
- `penable` - APB enable
- `pwrite` - APB write enable
- `pwdata` - APB write data
- `pready` - APB ready
- `prdata` - APB read data
- `pslverr` - APB slave error

**HPET Domain Signals:**
Timer-related signals use descriptive names:
- `hpet_clk` - HPET timer clock
- `hpet_rst_n` - HPET reset (active-low)
- `timer_irq[N]` - Timer interrupt outputs
- `r_main_counter` - Internal 64-bit counter
- `r_timer_comparator[i]` - Per-timer comparator value
- `r_timer_period[i]` - Per-timer period value

**Prefix Conventions:**
- `r_` - Registered (flip-flop) signal
- `w_` - Wire (combinational) signal
- `cfg_` - Configuration input
- `hwif_` - PeakRDL hardware interface signal

#### Common Abbreviations in Code

| Abbreviation | Meaning | Example |
|--------------|---------|---------|
| `cfg` | Configuration | `cfg_initial_credit` |
| `cmp` | Comparator | `timer_cmp_data` |
| `wr` | Write | `timer_comparator_wr` |
| `rd` | Read | `counter_rd_data` |
| `hi` | High (upper 32 bits) | `HPET_COUNTER_HI` |
| `lo` | Low (lower 32 bits) | `HPET_COUNTER_LO` |
| `en` | Enable | `timer_en` |
| `irq` | Interrupt Request | `timer_irq` |
| `clr` | Clear | `status_clr` |

---

**Next:** [Chapter 1.5 - References](05_references.md)
