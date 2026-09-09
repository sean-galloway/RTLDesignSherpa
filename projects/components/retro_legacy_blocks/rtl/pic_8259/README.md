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

# 8259 Programmable Interrupt Controller (PIC)

**Status:** Implementation complete; GitHub #50 defects fixed (2026-09-09)
**Priority:** High
**Address:** `0x4000_1000 - 0x4000_1FFF` (4 KB window, only 0x000-0x02C decoded)

---

## Overview

Intel 8259A-compatible Programmable Interrupt Controller with APB interface. Provides prioritized interrupt management with 8 IRQ inputs, cascade support for multi-level systems, and comprehensive priority control modes.

## Features

### Core Functionality
- **8 IRQ Inputs:** IRQ0-7 with programmable priority
- **Priority Modes:**
  - Fixed priority (IRQ0 highest, IRQ7 lowest)
  - Rotating priority (dynamic priority rotation)
- **Trigger Modes:**
  - Edge-triggered interrupt detection
  - Level-triggered interrupt detection
- **Interrupt Masking:** Individual IRQ mask control via IMR
- **EOI Handling:**
  - Non-specific EOI (retires the highest-priority in-service level)
  - Specific EOI (targeted IRQ)
  - Rotating EOI (with priority adjustment)
- **Acknowledge by read (PIC_INTA, 0x02C):** APB has no INTA bus cycle, so the
  acknowledge is a READ of PIC_INTA - see below. This is what sets the ISR and
  clears an edge-triggered IRR bit.

### Advanced Features
- **Cascade Support:**
  - Master/slave configuration
  - Up to 8 slaves per master (64 total IRQs)
  - Buffered mode for cascade systems
- **Auto-EOI Mode:** Automatic interrupt acknowledgment
- **Special Fully Nested Mode:** Enhanced cascade interrupt handling
- **Special Mask Mode:** Flexible interrupt priority override
- **Interrupt Vector Generation:** Programmable base address

### Register Interface
- **ICW Registers (Initialization):**
  - ICW1: Control word (edge/level, cascade, ICW4 needed)
  - ICW2: Interrupt vector base address
  - ICW3: Cascade configuration
  - ICW4: Special modes (AEOI, buffered, nested)
- **OCW Registers (Operation):**
  - OCW1: IMR (interrupt mask register)
  - OCW2: EOI commands, priority rotation
  - OCW3: Read commands, special mask mode
- **Status Registers:**
  - IRR: Interrupt Request Register (pending interrupts)
  - ISR: In-Service Register (servicing interrupts)
  - STATUS: Initialization state and diagnostics

## Acknowledge by Read (PIC_INTA, 0x02C)

The original 8259A moves a request from the IRR to the ISR during the CPU's
INTA bus cycle. APB has no equivalent, so this block substitutes a READ of
PIC_INTA, the way the ARM PL190 VIC acknowledges through a read of
`VICVectAddr`.

Reading PIC_INTA returns

| bits | field  | meaning |
|------|--------|---------|
| 7:0  | vector | `ICW2 vector_base[7:3]` concatenated with the acknowledged IRQ level |
| 8    | valid  | 1 = a request was acknowledged; 0 = nothing was pending |
| 31:9 | -      | reserved, reads 0 |

If an unmasked, unblocked request is pending the read:

- returns `valid = 1` and that level's vector (the value returned is the state
  BEFORE the acknowledge - PIC_INTA is a wire, not storage, so the bridge
  captures it in the same cycle the side effect is registered);
- sets `ISR[irq]`;
- clears `IRR[irq]` in EDGE mode. In LEVEL mode the IRR follows the pin, so the
  acknowledge leaves it alone;
- in AEOI mode clears `ISR[irq]` again immediately (so the bit is never
  observable) and, if rotate-on-AEOI is armed, rotates the priority base ONCE,
  to the acknowledged level.

If nothing is pending the read returns `valid = 0` with the spurious vector
`base[7:3] | 7` (the 8259A spurious-IRQ7 convention) and has NO side effects.
Writes to PIC_INTA are ignored.

Typical handler flow:

```
read PIC_INTA          -> vector, valid
  if !valid: spurious, return
  ... service the device ...
write PIC_OCW2         -> specific EOI for that level (unless AEOI)
```

## Address Decode

ONLY the twelve mapped registers 0x000-0x02C are software-visible. Every other
address in the 4 KB window is dropped - the write is ignored, the read returns
0 - and answered with **PSLVERR**. In particular an alias that shares the low
six bits with a real register (0x044 for ICW1, 0x054 for OCW1) is rejected, not
folded onto the register.

## Priority, In-Service Blocking and Special Mask Mode

A level is delivered when it is requesting, unmasked, and **no level of equal or
higher priority is in service**. An in-service level therefore blocks ITSELF as
well as everything below it: a second edge on a level already in service still
sets its IRR bit (the request is remembered), but INT stays low until that
level's EOI - after which INT reasserts and the next PIC_INTA read returns it.

**Special Mask Mode is IMR-gated, not a blanket lift.** The datasheet rule is
that a mask bit set in OCW1 "inhibits further interrupts at that level and
enables interrupts from all other levels that are not masked". So under SMM an
in-service level is removed from the blocking set exactly when its own IMR bit
is set - the usual pattern being a handler that masks its own level and sets
SMM so lower levels can come in. An in-service level that is still unmasked
keeps blocking, exactly as in normal mode.

The **same gated set is what a non-specific EOI retires**: the highest-priority
in-service level *among those not masked*, per the datasheet's SMM note. So the
handler that masked its own level and enabled SMM has its own non-specific EOI
retire ITS level, not the outer masked one. With SMM off the gate is empty and
this is the plain highest-priority in-service level. If nothing qualifies the
EOI is a no-op - it never defaults to level 0.

## Enable, Disable and the Initialization Window

`PIC_CONFIG.pic_enable` gates **delivery**, not observation. While it is 0 the
INT pin stays low and PIC_INTA acknowledges nothing, but the IRR keeps tracking
the pins - so a request that arrives during a disabled window is delivered when
the PIC is re-enabled rather than being dropped. The edge reference follows the
synchronized pin every cycle, so re-enabling also never manufactures an edge
from a line that was already high. In-service state survives a disable/enable
cycle for the same reason.

Initialization is deliberately different. An ICW1 write clears the IRR, and the
IRR does not observe again until INIT_COMPLETE, because the trigger mode and
vector base are still in flux mid-sequence. An edge that occurs inside the
ICW2..ICW4 window is therefore **not latched** - and, because the edge reference
is still tracking, it is not fabricated at INIT_COMPLETE either. Assert the line
after initialization completes, or use level-triggered mode.

Commands are equally strict: a write with `PSTRB = 0` changes no register and
executes no command, so it cannot replay whatever the ICW/OCW register happened
to be holding.

## Deviations from a Real 8259A

Stated rather than implied. In-service blocking and special mask mode are NOT
in this list - both follow the datasheet, as described above.

- **No cascade.** ICW3 (cascade), ICW4 buffered-mode and ICW4 SFNM are
  software-visible storage with no hardware effect. Special Fully Nested Mode
  is NOT implemented; the ordinary nesting rule runs regardless of the bit.
- **OCW3 poll and read-register-select are storage only.** IRR and ISR have
  their own read-only registers (0x020, 0x024), which is what makes the
  register-select command moot here.
- **Re-initialization** (an ICW1 write) clears IRR, ISR, special mask mode and
  rotate-on-AEOI, and returns the priority base to 7 (IRQ0 highest). It does
  NOT reset the ICW4 storage.
- **`PIC_CONFIG.init_mode` is a start REQUEST, not a mode level.** Write it
  0 -> 1 to request a re-initialization; the ICW1 write consumes the request.
  Leaving it at 1 with `auto_reset_init = 0` is legal and does not disturb
  INIT_COMPLETE.
- **`irq_in` is treated as asynchronous** and crosses `SYNC_STAGES` (default 2)
  flops before it is sampled, so every IRQ carries that much latency.

## Applications

- Legacy PC-compatible interrupt management
- Multi-source interrupt aggregation
- Priority-based interrupt handling
- Cascaded multi-level interrupt systems (up to 64 IRQs)
- Real-time systems requiring deterministic interrupt priority

## Architecture

Follows HPET/PIT 8254 three-layer architecture:

```
Layer 1: apb4_pic_8259.sv
  ├─ APB4 slave interface
  └─ Top-level integration

Layer 2: pic_8259_config_regs.sv
  ├─ PeakRDL-generated register file
  ├─ CMD/RSP adapter
  └─ ICW/OCW write edge detection

Layer 3: pic_8259_core.sv
  ├─ 8 IRQ prioritization
  ├─ IRR/ISR/IMR management
  ├─ Priority resolver (fixed/rotating)
  ├─ EOI command processing
  └─ Cascade logic
```

## Files

### RTL Implementation
- ✅ `apb4_pic_8259.sv` - Top-level APB wrapper (parameter `SYNC_STAGES`, default 2)
- ✅ `pic_8259_core.sv` - Core PIC interrupt controller logic
- ✅ `pic_8259_config_regs.sv` - Register wrapper with edge detection
- ✅ `pic_8259_regs.sv` - PeakRDL generated register file
- ✅ `pic_8259_regs_pkg.sv` - PeakRDL generated package

### Register Specification
- ✅ `peakrdl/pic_8259_regs.rdl` - SystemRDL specification
- ✅ `peakrdl/README.md` - Generation instructions

### Python Support
- ✅ `pic_8259_regmap.py` - Auto-generated register map
- ✅ `pic_8259_helper.py` - Human-readable programming helper

## Register Map

| Address | Register    | Access | Description |
|---------|-------------|--------|-------------|
| 0x000   | PIC_CONFIG  | RW     | Global configuration and control |
| 0x004   | PIC_ICW1    | WO     | Initialization Command Word 1 |
| 0x008   | PIC_ICW2    | WO     | Initialization Command Word 2 (vector base) |
| 0x00C   | PIC_ICW3    | WO     | Initialization Command Word 3 (cascade) |
| 0x010   | PIC_ICW4    | WO     | Initialization Command Word 4 (modes) |
| 0x014   | PIC_OCW1    | RW     | Operation Command Word 1 (IMR) |
| 0x018   | PIC_OCW2    | WO     | Operation Command Word 2 (EOI/priority) |
| 0x01C   | PIC_OCW3    | WO     | Operation Command Word 3 (special modes) |
| 0x020   | PIC_IRR     | RO     | Interrupt Request Register |
| 0x024   | PIC_ISR     | RO     | In-Service Register |
| 0x028   | PIC_STATUS  | RO     | Status and diagnostics |
| 0x02C   | PIC_INTA    | RO     | Interrupt acknowledge BY READ (side-effecting) |

Everything else in the 4 KB window is dropped with PSLVERR.

## Usage Example (Python Helper)

```python
from pic_8259_helper import PIC8259Helper

# Initialize PIC helper
pic = PIC8259Helper('pic_8259_regmap.py', apb_data_width=32,
                    apb_addr_width=16, start_address=0x40001000, log=logger)

# Initialize PIC for single mode with vector base 0x20
pic.initialize(vector_base=0x20, edge_triggered=True,
               single_mode=True, icw4_needed=True, auto_eoi=False)

# Enable specific IRQs (unmask IRQ0, IRQ1, IRQ5)
pic.unmask_irqs([0, 1, 5])

# Send EOI for IRQ5
pic.send_eoi(irq=5, specific=True)

# Enable rotating priority mode
pic.enable_auto_rotate_eoi(True)

# Generate APB transactions
apb_packets = pic.generate_apb_cycles()
```

## PC-Compatible Cascade Configuration

```python
# Configure Master PIC (IRQ0-7)
master_pic = PIC8259Helper('pic_8259_regmap.py', ...)
master_pic.configure_pc_master_pic(cascade_irq=2)
master_pic.unmask_irqs([0, 1, 2, 3, 4, 5, 6, 7])

# Configure Slave PIC (IRQ8-15)
slave_pic = PIC8259Helper('pic_8259_regmap.py', ...)
slave_pic.configure_pc_slave_pic(slave_id=2)
slave_pic.unmask_irqs([0, 1, 2, 3, 4, 5, 6, 7])  # IRQ8-15
```

## Implementation Details

### Initialization Sequence
1. Write ICW1: Set edge/level mode, cascade mode, ICW4 needed
2. Write ICW2: Set interrupt vector base address
3. Write ICW3: Configure cascade (if not single mode)
4. Write ICW4: Set special modes (if IC4=1 in ICW1)

### Priority Resolution
`r_priority_base` names the LOWEST-priority level; the resolver scans
`(base + 1 + k) mod 8` for k = 0..7, i.e. in descending priority. This is a
rotation of the level index, not a reflection - with base = 3 the order is
4,5,6,7,0,1,2,3, so IRQ4 outranks IRQ2.

- **Fixed Priority:** base = 7, so IRQ0 (highest) -> IRQ7 (lowest)
- **Rotating Priority:** the base moves on set-priority, rotate-on-EOI, and
  once per acknowledge in rotate-on-AEOI mode
- **Special Mask Mode:** IMR-gated - an in-service level stops blocking
  exactly when its own IMR bit is set (see the section above); an unmasked
  in-service level keeps blocking, as in normal mode

### EOI Commands
- **0b001:** Non-specific EOI (clear highest priority ISR bit)
- **0b011:** Specific EOI (clear designated IRQ)
- **0b101:** Rotate on non-specific EOI
- **0b111:** Rotate on specific EOI
- **0b110:** Set priority command
- **0b100/000:** Rotate in auto-EOI mode control

## Development Status

- [x] SystemRDL register specification
- [x] PeakRDL register file generation
- [x] Core PIC logic implementation
- [x] APB wrapper
- [x] Register map Python generator
- [x] Helper class for register programming
- [x] Basic testbench
- [x] Medium testbench (GitHub #50 defect regression)
- [x] Full testbench
- [x] MAS refresh for the GitHub #50 behaviour (done 2026-09-09: PIC_INTA,
      live ISR, strict decode with PSLVERR, datasheet blocking and SMM rules)

## Technical Specifications

- **Bus Interface:** APB4 (AMBA 3)
- **Register Width:** 32-bit
- **Address Width:** 12-bit (4KB window)
- **IRQ Inputs:** 8 (IRQ0-7)
- **Interrupt Output:** Single INT pin
- **Clock Domain:** Single (APB clock); `irq_in` is synchronized on entry
- **Reset:** `presetn`, active-low. Asynchronous on assertion in the
  hand-written core and wrapper (the `ALWAYS_FF_RST` house macro); the
  PeakRDL-generated `pic_8259_regs.sv` uses a SYNCHRONOUS reset, which is what
  its generator emits and is not overridden here

## Verification Targets

1. **Basic Functionality:**
   - IRQ edge/level detection
   - Priority resolution (fixed and rotating)
   - IMR masking behavior
   - EOI command processing

2. **Advanced Features:**
   - Cascade master/slave coordination
   - Auto-EOI mode
   - Special mask mode
   - Priority rotation algorithms

3. **Corner Cases:**
   - Simultaneous IRQ assertions
   - EOI during active interrupt
   - Reinitialization during operation
   - Cascade communication timing

## References

- Intel 8259A Datasheet
- IBM PC/AT Technical Reference
- AMBA APB Protocol Specification

---

**Last Updated:** 2026-09-09
**Implementation:** Complete (GitHub #50 fixes landed)
**Verification:** 31/31 in each of the three test configurations
