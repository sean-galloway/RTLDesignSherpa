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

# RLB Top - Block Hierarchy Overview

## The Twelve Instances

`rlb_top` contains no logic blocks of its own. It instantiates twelve modules
and wires them together, with two pieces of combinational glue: the interrupt
fabric and the cascade cross-connect.

| Instance | Module | Window | Parameters passed |
| --- | --- | --- | --- |
| `u_apbx_xbar` | `apbx_xbar_1to10` | - | `ADDR_WIDTH`, `DATA_WIDTH`, `STRB_WIDTH`, `BASE_ADDR` |
| `u_hpet` | `apb4_hpet` | 0 | `VENDOR_ID`, `REVISION_ID`, `NUM_TIMERS`, `CDC_ENABLE(0)` |
| `u_pic` | `apb4_pic_8259` | 1 | none |
| `u_pit` | `apb4_pit_8254` | 2 | `NUM_COUNTERS`, `CDC_ENABLE(0)` |
| `u_rtc` | `apb4_rtc` | 3 | none |
| `u_smbus` | `apb4_smbus` | 4 | `FIFO_DEPTH`, `CDC_ENABLE(0)` |
| `u_pm_acpi` | `apb4_pm_acpi` | 5 | `CDC_ENABLE(0)` |
| `u_ioapic` | `apb4_ioapic` | 6 | `NUM_IRQS`, `CDC_ENABLE(0)` |
| `u_gpio` | `apb4_gpio` | 7 | `GPIO_WIDTH`, `SYNC_STAGES`, `CDC_ENABLE(0)`, `SKID_DEPTH(2)` |
| `u_uart` | `apb4_uart_16550` | 8 | `FIFO_DEPTH`, `SYNC_STAGES`, `CDC_ENABLE(0)`, `SKID_DEPTH(2)` |
| `u_pic_slave` | `apb4_pic_8259` | 9 | none |
| `u_ioapic_boot_intx` | `ioapic_boot_intx` | - | `NUM_IRQS`, `NUM_PIC(8)`, `PIC_IDX_W(4)`, `PIC_MAP` |

## u_apbx_xbar - the address decode

A generated 1-to-10 APB crossbar. It is produced by the shared crossbar
generator, configured as one master, ten slaves, base `0xFEC00000`, 32-bit
address and data, and 4KB per slave.

**Do not hand-edit it.** The generator owns the decode-miss path - an unmapped
address completes with `PSLVERR` rather than hanging the bus - and the
hand-rolled crossbar this one replaced had already lost that behaviour. It is
regenerated, not patched.

The crossbar forwards the full 32-bit address. Each peripheral instantiation
slices `PADDR[11:0]` from its own channel, so a block sees offsets from `0x000`
within its window.

## The two 8259 instances

The same module appears twice, and the difference is entirely in the wiring.

| | `u_pic` (master, window 1) | `u_pic_slave` (slave, window 9) |
| --- | --- | --- |
| `irq_in` | `w_master_pic_irq` (a named signal) | `pic_irq_in[15:8] \| w_fabric_irq[15:8]` (inline) |
| `int_out` | `pic_int_out`, a module output | `w_spic_int`, internal only |
| `cas_vector` | `w_spic_vector`, from the slave | `8'h00`, tied off |
| `cas_ack_in` | `1'b0` - nothing acknowledges the master | `w_pic_cas_ack`, from the master |
| `cas_ack` | `w_pic_cas_ack`, to the slave | unconnected |
| `inta_vector_o` | unconnected | `w_spic_vector`, to the master |

Two details are worth carrying away. First, the slave's `irq_in` is an **inline
expression, not a named signal**, so there is nothing to probe by name; with
`pic_irq_in` held at zero the slave's IR line for a given IRQ is exactly
`w_fabric_irq[irq]`. Second, the master's IR2 is not OR-ed with anything - it is
masked off every other source and then forced from the slave.

## u_ioapic - and what it is not wired to

The IOAPIC receives `w_ioapic_irq`, which is the external `ioapic_irq_in` OR-ed
with the zero-extended fabric vector. Its delivery handshake, EOI input and
retry input are all on the module boundary.

Four of its configuration outputs are **connected and deliberately left open**:

| Pin | Why it is open |
| --- | --- |
| `cfg_msi_addr` | `ioapic_msi_emit` is not instantiated here, so nothing consumes MSI configuration |
| `cfg_msi_data` | as above |
| `cfg_mask_vec` | consumed by `u_ioapic_boot_intx` |
| `cfg_boot_intx_en` | consumed by `u_ioapic_boot_intx` |

The first two are the interesting case. Software can program them through
`IOWIN`, and nothing will happen. They are wired to an empty connection rather
than omitted from the instantiation because an omitted pin produces a
`PINMISSING` warning, which is how a gap like this becomes invisible.

## u_ioapic_boot_intx - the boot-interrupt companion

A small combinational module. It takes the raw IOAPIC pin inputs, the IOAPIC's
mask vector and its boot-interrupt enable, and produces legacy PIC inputs for
the pins the IOAPIC is not delivering.

Its map, `BOOT_INTX_PIC_MAP`, is built as a localparam in `rlb_top`: the
identity mapping for pins 0 through 7, and a no-reroute code for every pin above
that. Field 0 is the least significant, so the identity entries are written last
in the concatenation.

Pin 2 is a **dead entry**. The map still names legacy input 2, but master IR2 is
masked off the external inputs and driven from the slave controller, so a reroute
onto pin 2 reaches nothing. It is kept in the map so the table still reads as the
published identity mapping; an integrator who needs pin 2 rerouted must choose a
different legacy input.

Because the IOAPIC's boot-interrupt enable resets to 0, this module's output is
all zeros after reset and the master's interrupt input is exactly `pic_irq_in`
until software opts in.

## The glue

Neither of these is a module, and both are worth naming because they are where
the integration behaviour lives.

**The interrupt fabric** is one `always_comb` block that builds
`w_fabric_irq[15:0]` from the blocks' interrupt outputs, plus three continuous
assignments that distribute it: to the IOAPIC, to the master controller with the
IR2 mask, and into the `rlb_irq_out` aggregate.

**The cascade cross-connect** is three wires between the two controllers, listed
in the table above.

`rlb_top` has no `always_ff` of its own. It holds no state.

## Related Documents

- [Architecture](../ch01_overview/02_architecture.md) - the fabric and cascade in detail
- [Top-Level Interface](../ch03_interfaces/01_top_level.md) - the port list
- [Window Map](../ch05_registers/01_register_map.md)
