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

# RLB Top - Clocks and Reset

## The Short Version

There is one functional clock domain in this configuration: `pclk`. Every other
clock port exists on the boundary and is unused.

That needs stating plainly, because the port list suggests otherwise.

## Clock and Reset Ports

| Clock | Reset | Intended domain | Used in this configuration |
| --- | --- | --- | --- |
| `pclk` | `presetn` | APB, primary | **Yes** - everything runs here |
| `hpet_clk` | `hpet_resetn` | HPET counter | No |
| `pit_clk` | `pit_resetn` | PIT counting clock | No |
| `rtc_clk` | `rtc_resetn` | RTC time base | No |
| `smbus_clk` | `smbus_resetn` | SMBus bit clock | No |
| `pm_clk` | `pm_resetn` | PM/ACPI | No |
| `ioapic_clk` | `ioapic_resetn` | IOAPIC | No |
| `gpio_clk` | `gpio_rstn` | GPIO sampling | No |
| `uart_clk` | `uart_rstn` | UART baud reference | No |

Note the naming inconsistency in the last two: GPIO and UART use `gpio_rstn` and
`uart_rstn`, not `_resetn`. That is the blocks' own port naming, carried through.

## Why the Extra Clocks Are Unused

`rlb_top` instantiates every CDC-capable block with `CDC_ENABLE(0)`:

| Instance | Parameterisation |
| --- | --- |
| `u_hpet` | `CDC_ENABLE(0)` |
| `u_pit` | `CDC_ENABLE(0)` |
| `u_smbus` | `CDC_ENABLE(0)` |
| `u_pm_acpi` | `CDC_ENABLE(0)` |
| `u_ioapic` | `CDC_ENABLE(0)` |
| `u_gpio` | `CDC_ENABLE(0)` |
| `u_uart` | `CDC_ENABLE(0)` |

With `CDC_ENABLE=0` a block uses the plain APB slave and ignores its second
clock and reset entirely. The ports remain on `rlb_top` so the boundary does not
change if a future configuration enables CDC on one or more blocks, but today
nothing downstream of them is clocked.

**What an integrator should do:** tie every unused clock to `pclk` and every
unused reset to `presetn`. Leaving them unconnected or tied to a constant is
legal in this configuration but becomes a real bug the moment any block is
rebuilt with `CDC_ENABLE=1`, and the failure then looks like a dead peripheral
rather than a missing clock.

The RTC is the case worth flagging: a real system usually wants its time base on
a separate always-on 32.768 kHz domain, which in this subsystem means
instantiating `apb4_rtc` with CDC enabled rather than relying on `rtc_clk` as
wired here.

## Reset Behaviour

- **Active low, asynchronous**, throughout. There is no positive-polarity reset
  anywhere in this subsystem.
- Reset is applied through the repository's reset macros from
  `reset_defs.svh`, which `rlb_top` includes. A hand-written
  `always_ff @(posedge clk or negedge rst_n)` is not used and would be
  rejected.
- `rlb_top` itself holds no state. It has no `always_ff` of its own: the
  interrupt fabric is a single `always_comb`, and the cascade and aggregate are
  continuous assignments. All reset behaviour belongs to the instantiated
  blocks.

### Reset state of the interrupt fabric

Because the fabric is purely combinational, its reset state is whatever its
sources are, and at reset those are all deasserted. Two consequences matter for
bring-up:

- **`w_boot_intx_pic_irq` is all zeros after reset**, because the IOAPIC's
  boot-interrupt enable resets to 0. The master's interrupt input is therefore
  exactly `pic_irq_in` until software enables rerouting.
- **IOAPIC redirection entries reset masked.** A source can reach the IOAPIC's
  pin and produce no delivery at all, which looks identical to a broken route.
  Unmasking the relevant entry is a required bring-up step, not an
  optimisation. See [Initialization](../ch04_programming/01_initialization.md).

### Resetting to clear an interrupt

The 8259 in edge-triggered mode latches `INT` high until it is acknowledged.
The integration test suite resets the whole subsystem between phases rather
than acknowledging, because the acknowledge and EOI paths have their own known
limitations at block level. That is a verification convenience and not a
recommendation for firmware; software should acknowledge properly. It is
mentioned here because it explains why the testbench re-programs both
controllers and re-arms the IOAPIC after every such phase - a full reset drops
all of that configuration.

## Related Documents

- [Architecture](02_architecture.md)
- [Top-Level Interface](../ch03_interfaces/01_top_level.md)
- Repository reset and clocking rules: `vault/handbook/design/reset-and-clocking.md`
