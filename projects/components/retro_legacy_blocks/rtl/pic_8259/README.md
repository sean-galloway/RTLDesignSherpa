# 8259 Programmable Interrupt Controller (PIC)

**Status:** ✅ Implementation Complete
**Priority:** High
**Address:** `0x4000_1000 - 0x4000_1FFF` (4KB window)

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
  - Non-specific EOI (automatic highest priority)
  - Specific EOI (targeted IRQ)
  - Rotating EOI (with priority adjustment)

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

## Applications

- Legacy PC-compatible interrupt management
- Multi-source interrupt aggregation
- Priority-based interrupt handling
- Cascaded multi-level interrupt systems (up to 64 IRQs)
- Real-time systems requiring deterministic interrupt priority

## Architecture

Follows HPET/PIT 8254 three-layer architecture:

```
Layer 1: apb_pic_8259.sv
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
- ✅ `apb_pic_8259.sv` - Top-level APB wrapper
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
- **Fixed Priority:** IRQ0 (highest) → IRQ7 (lowest)
- **Rotating Priority:** Priority base rotates after each EOI
- **Special Mask Mode:** Allows servicing masked IRQs

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
- [ ] Basic testbench
- [ ] Medium testbench
- [ ] Full testbench
- [ ] Documentation enhancement

## Technical Specifications

- **Bus Interface:** APB4 (AMBA 3)
- **Register Width:** 32-bit
- **Address Width:** 12-bit (4KB window)
- **IRQ Inputs:** 8 (IRQ0-7)
- **Interrupt Output:** Single INT pin
- **Clock Domain:** Single (APB clock)
- **Reset:** Synchronous active-high (internal), active-low (APB interface)

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

**Last Updated:** 2025-11-15  
**Implementation:** Complete  
**Verification:** Pending
