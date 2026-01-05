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

### APB IOAPIC - Block Overview

#### Module Hierarchy

The APB IOAPIC consists of four primary blocks organized in a clean hierarchical structure:

```
apb_ioapic (Top Level)
├── apb_slave or apb_slave_cdc (Bus Interface)
├── ioapic_config_regs (Register Wrapper)
│   ├── peakrdl_to_cmdrsp (Protocol Adapter)
│   └── ioapic_regs (PeakRDL Generated)
└── ioapic_core (Core Interrupt Logic)
```

#### Block Summary

| Block | File | Lines | Purpose |
|-------|------|-------|---------|
| **apb_ioapic** | apb_ioapic.sv | ~340 | Top-level integration, CDC selection |
| **ioapic_config_regs** | ioapic_config_regs.sv | ~220 | Register interface, indirect access, hwif mapping |
| **ioapic_regs** | ioapic_regs.sv | ~2500 | PeakRDL generated register block |
| **ioapic_core** | ioapic_core.sv | ~290 | Interrupt routing, edge/level detection, arbitration |
| **peakrdl_to_cmdrsp** | (external) | ~150 | CMD/RSP to PeakRDL passthrough adapter |
| **apb_slave[_cdc]** | (external) | ~200 | APB protocol handler |

**Total Implementation:** ~900 lines of custom RTL + ~2700 lines generated/reused

#### Block Descriptions

**1. apb_ioapic (Top Level)**
- Selects APB slave type based on CDC_ENABLE parameter
- Routes clocks and resets to submodules
- Instantiates config_regs and core
- Connects external IRQ and EOI interfaces
- See: [apb_ioapic_top.md](04_apb_ioapic_top.md)

**2. ioapic_config_regs (Register Wrapper)**
- Instantiates peakrdl_to_cmdrsp adapter
- Instantiates PeakRDL generated registers
- Maps hwif signals to/from ioapic_core
- Handles array mapping for 24 redirection entries
- See: [ioapic_config_regs.md](02_ioapic_config_regs.md)

**3. ioapic_regs (PeakRDL Generated)**
- Generated from ioapic_regs.rdl SystemRDL specification
- Implements IOREGSEL/IOWIN indirect access
- Provides hwif_in/hwif_out structs
- Handles register read/write/reset
- See: [ioapic_regs.md](03_ioapic_regs.md)

**4. ioapic_core (Core Logic)**
- 24 IRQ input synchronization (3-stage)
- Polarity handling (active-high/low)
- Edge/level detection
- Priority arbitration (static)
- Interrupt delivery FSM (IDLE/DELIVER/WAIT_EOI)
- Remote IRR management
- See: [ioapic_core.md](01_ioapic_core.md)

#### Data Flow Between Blocks

**Configuration Write Path:**
```
APB Write Request
  ↓
apb_slave[_cdc] (APB protocol handling)
  ↓ CMD interface
peakrdl_to_cmdrsp (protocol adapter)
  ↓ Passthrough interface
ioapic_regs (register storage, indirect access)
  ↓ hwif_out
ioapic_config_regs (signal mapping)
  ↓ cfg_* signals
ioapic_core (uses configuration)
```

**Status Read Path:**
```
ioapic_core (generates status)
  ↓ status_* signals
ioapic_config_regs (signal mapping)
  ↓ hwif_in
ioapic_regs (register readback, indirect access)
  ↓ RSP interface
peakrdl_to_cmdrsp (protocol adapter)
  ↓ APB response
apb_slave[_cdc] (APB protocol)
  ↓
APB Read Data
```

**Interrupt Delivery Path:**
```
External IRQ assertion
  ↓
ioapic_core (sync → polarity → detect → arbitrate → deliver)
  ↓ irq_out_valid, irq_out_vector, irq_out_dest
apb_ioapic (top-level signals)
  ↓
CPU/LAPIC
```

#### Interface Summary

**External Interfaces:**
- APB4 slave (to CPU/interconnect)
- 24 IRQ inputs (from interrupt sources)
- Interrupt output (to CPU/LAPIC)
- EOI input (from CPU/LAPIC)

**Internal Interfaces:**
- CMD/RSP between APB slave and config_regs
- PeakRDL passthrough between adapter and registers
- hwif between registers and config_regs
- Config/status signals between config_regs and core

#### Clock Domain Assignment

**CDC_ENABLE=0 (Single Clock):**
- All blocks run on `pclk`
- apb_slave instantiated (no CDC)
- Simplest timing analysis

**CDC_ENABLE=1 (Dual Clock):**
- apb_slave_cdc runs on `pclk` (APB domain)
- config_regs runs on `ioapic_clk` (IOAPIC domain)
- core runs on `ioapic_clk` (IOAPIC domain)
- CDC handled by apb_slave_cdc module

#### Module Dependencies

**RLB Project Dependencies:**
- `reset_defs.svh` - Reset macro definitions
- `apb_slave.sv` or `apb_slave_cdc.sv` - APB protocol
- `peakrdl_to_cmdrsp.sv` - Register adapter

**Generated Files:**
- `ioapic_regs.sv` - From ioapic_regs.rdl via peakrdl_generate.py
- `ioapic_regs_pkg.sv` - Package with hwif struct definitions

**No External IP Required:**
All dependencies are within the RLB project or generated from specifications.

---

**Chapter 2 Contents:**
- [01_ioapic_core.md](01_ioapic_core.md) - Core interrupt logic
- [02_ioapic_config_regs.md](02_ioapic_config_regs.md) - Register wrapper
- [03_ioapic_regs.md](03_ioapic_regs.md) - PeakRDL generated
- [04_apb_ioapic_top.md](04_apb_ioapic_top.md) - Top-level integration
- [05_fsm_summary.md](05_fsm_summary.md) - State machine summary

**Back to:** [Index](../ioapic_index.md) | **Next:** [ioapic_core Block](01_ioapic_core.md)
