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

# RLB Top Specification

**Component:** Retro Legacy Blocks subsystem integration (`rlb_top`)
**Version:** 1.0
**Last Updated:** 2026-09-30
**Status:** RTL Functional -- all ten windows implemented and answering, the
interrupt fabric routing all six sourcing blocks to both 8259s and the IOAPIC,
and the master/slave 8259 cascade cross-connected. 16/16 integration tests pass
at the `full` level. Two integration gaps are deliberate and stated as such
below: `ioapic_msi_emit` is not instantiated, and `hpet_timer_irq` is not routed
into the fabric.

---

## Overview

This is the micro-architecture specification for `rlb_top`, the integration
level of the Retro Legacy Blocks subsystem. The nine other books in this
directory each specify one peripheral. This one specifies the layer that
instantiates them: one APB slave port in, a 1-to-10 crossbar, ten 4KB windows,
and an interrupt fabric that collects every block's interrupt and presents it on
the conventional legacy lines to two 8259s and an IOAPIC.

Read this book if you are integrating the subsystem into an SoC, writing the
firmware that brings it up, or trying to work out which controller a given
block's interrupt arrives on. Read the per-block book for anything inside a
block.

Three facts are worth knowing before anything else, because each one has
surprised somebody:

- **There is no reserved window.** Window 9 was reserved; it is the slave 8259
  of the cascaded pair now. All ten windows are assigned.
- **IRQ2 is never driven by the fabric.** It is the 8259 cascade input, forced
  from the slave's `INT`. Anything routed to IRQ2 reaches nothing.
- **The fabric is OR-ed into the external inputs, not substituted for them.**
  `pic_irq_in` and `ioapic_irq_in` remain inputs, so a board keeps its external
  interrupt path.

> Status (2026-10-03): all chapters listed below exist in this tree. The
> Chapter 2 block pages, the Chapter 3 APB4 and interrupt-pin pages, and the
> Chapter 4 power-management page were added on 2026-10-03 (RLB TASK-020).

### Chapter 1: Overview
**Location:** `ch01_overview/`

- [01_overview.md](ch01_overview/01_overview.md) - What the subsystem is, block inventory, deliberate scope boundaries
- [02_architecture.md](ch01_overview/02_architecture.md) - Integration architecture, the crossbar, the interrupt fabric
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock and reset ports, and the CDC parameterisation trap
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External specifications and in-repo references

### Chapter 2: Blocks
**Location:** `ch02_blocks/`

- [00_overview.md](ch02_blocks/00_overview.md) - The twelve instances and what each contributes
- [01_apbx_xbar.md](ch02_blocks/01_apbx_xbar.md) - The generated 1-to-10 crossbar in detail
- [02_interrupt_fabric.md](ch02_blocks/02_interrupt_fabric.md) - The fabric as its own block
- [03_cascade.md](ch02_blocks/03_cascade.md) - The 8259 cascade cross-connect in detail

### Chapter 3: Interfaces
**Location:** `ch03_interfaces/`

- [01_top_level.md](ch03_interfaces/01_top_level.md) - Parameters, full port list, address decode contract
- [02_apb_interface_spec.md](ch03_interfaces/02_apb_interface_spec.md) - APB4 protocol specification at this boundary
- [03_interrupt_interfaces.md](ch03_interfaces/03_interrupt_interfaces.md) - Per-block interrupt pin reference

### Chapter 4: Programming Model
**Location:** `ch04_programming/`

- [01_initialization.md](ch04_programming/01_initialization.md) - Subsystem bring-up order, 8259 single and cascade configuration, IOAPIC redirection entries
- [02_use_cases.md](ch04_programming/02_use_cases.md) - Routing an interrupt end to end, legacy replacement, boot-interrupt rerouting
- [03_power_management.md](ch04_programming/03_power_management.md) - ACPI sleep and wake sequencing across blocks

### Chapter 5: Registers
**Location:** `ch05_registers/`

- [01_register_map.md](ch05_registers/01_register_map.md) - The ten-window address map, and where each block's registers are specified

---

## Design Notes

### Document Conventions

**Notation:**
- **bold** - Important terms, signal names
- `code` - Register names, field names, code examples
- *italic* - Emphasis, notes

**Signal naming:**
- `pclk` / `presetn` - APB clock and reset, the primary domain
- `s_apb_*` - The single APB4 slave port into the subsystem
- `w_fabric_irq[15:0]` - The internal interrupt fabric vector
- `w_master_pic_irq[7:0]` - What the master 8259 actually sees
- `rlb_irq_out` - The aggregated single-line interrupt output

**Address notation:**
- `0xFEC0_0000` - `BASE_ADDR`, the subsystem base
- Window *n* - the 4KB region at `BASE_ADDR + n * 0x1000`
- Slave index - `PADDR[15:12]`, which equals the window number

### Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-09-30 | RTL Design Sherpa | Initial release. Documents the ten-window map, the interrupt fabric (RLB TASK-015), the cascade cross-connect (RLB/pic_8259 TASK-001), boot-interrupt rerouting (RLB TASK-008) and the two deliberate integration gaps. Written because the routing table and the bring-up order had existed only in the testbench. |

---

## Testing

### Test Results

- **Suite:** `dv/tests/test_rlb_top.py`, one cocotb test parameterised by
  `TEST_LEVEL`, running a method list that grows with the level
- **Levels:** `gate` 1 test, `func` 7 tests, `full` 16 tests
- **Result:** 16/16 at `full`, including 8 logged `per-IR-line OK` checks

Run it through the area Makefile, which supplies the level and cleans first:

```bash
source env_python
cd projects/components/retro_legacy_blocks/dv/tests
make clean-all && make run-rlb_top-full
```

### What the suite proves

1. Every one of the ten windows answers at its probe register
2. The slave 8259 answers on window 9
3. Decode isolation - a write to one window does not alias into another
4. An unmapped address completes with `PSLVERR` rather than hanging
5. `rlb_irq_out` aggregates block interrupts
6. Each of the six sourcing blocks reaches its own master or slave IR line,
   verified per line rather than in aggregate
7. Each of those blocks reaches its IOAPIC pin and is delivered
8. The boot-interrupt reroute path reaches the 8259
9. Coincident asserts at two, three and four sources, spanning both PICs

### Deliberate scope boundaries

These are integration decisions, not defects:

- **`ioapic_msi_emit` is not instantiated.** Software can program
  `cfg_msi_addr` and `cfg_msi_data` through `IOWIN`, but nothing in this
  subsystem consumes them. The pins are connected and left open rather than
  omitted, so the gap is visible instead of hidden behind `PINMISSING`.
- **`ioapic_boot_intx` is instantiated, but its pin-to-legacy map is a board
  decision.** The default is the 82093AA identity mapping for pins 0-7 and no
  reroute above that.
- **`hpet_timer_irq` is not routed into the fabric.** The general HPET timers
  have no conventional legacy line, which is the same reason
  `TIMER_INT_ROUTE_CAP` reads 0. They reach `rlb_irq_out` and their own pins.
- **Every block is instantiated with `CDC_ENABLE(0)`.** The per-block clock and
  reset ports exist on `rlb_top` but are unused in this configuration. See
  Chapter 1.3.

---

## References

- **RTL Implementation:** [../../rtl/rlb_top/rlb_top.sv](../../rtl/rlb_top/rlb_top.sv)
- **Filelist:** [../../rtl/rlb_top/filelists/rlb_top.f](../../rtl/rlb_top/filelists/rlb_top.f)
- **Test Suite:** [../../dv/tests/test_rlb_top.py](../../dv/tests/test_rlb_top.py)
- **Testbench Classes:** [../../dv/tbclasses/rlb_top/](../../dv/tbclasses/rlb_top/)
- **Subsystem requirements:** [../../PRD.md](../../PRD.md)
- **FPGA integration guide:** [../RLB_FPGA_IMPLEMENTATION_GUIDE.md](../RLB_FPGA_IMPLEMENTATION_GUIDE.md)

---

## Navigation

### For Software Developers
- Start with [Chapter 4: Programming Model](ch04_programming/01_initialization.md)
- Reference [Chapter 5: Window Map](ch05_registers/01_register_map.md), then the
  per-block book for the registers inside a window

### For Hardware Integrators
- Start with [Chapter 3: Interfaces](ch03_interfaces/01_top_level.md)
- Reference [Chapter 1.3: Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### For Verification Engineers
- Start with [Chapter 2: Blocks](ch02_blocks/00_overview.md)
- Reference [Chapter 4.2: Use Cases](ch04_programming/02_use_cases.md) for the
  routing paths the suite exercises

### For System Architects
- Start with [Chapter 1.2: Architecture](ch01_overview/02_architecture.md)

---

**Documentation and implementation support by Claude.**
