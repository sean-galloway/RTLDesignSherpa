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

# RLB Top - Top-Level Interface

## Overview

`rlb_top` is the integration contract for the whole subsystem: one APB4 slave
port, the peripherals' external pins, and one aggregated interrupt output. This
chapter is the pin list, the parameters, and the address decode rules an
integrator has to honour.

## Parameters

| Parameter | Type | Default | Description |
| --- | --- | --- | --- |
| `ADDR_WIDTH` | int | 32 | APB address width. The subsystem decodes a full system address, not a windowed one. |
| `DATA_WIDTH` | int | 32 | APB data width. |
| `STRB_WIDTH` | int | `DATA_WIDTH/8` | Write-strobe width. Derived; do not override independently. |
| `BASE_ADDR` | logic [ADDR_WIDTH-1:0] | `32'hFEC00000` | Base of the ten-window region. |
| `HPET_VENDOR_ID` | int | 1 | Driven into the HPET capability register. |
| `HPET_REVISION` | int | 1 | Driven into the HPET capability register. |
| `HPET_NUM_TIMERS` | int | 2 | HPET comparator count. Sets the width of `hpet_timer_irq`. |
| `PIT_NUM_COUNTERS` | int | 3 | 8254 counter count. Sets the width of `pit_gate_in` and `pit_timer_irq`. |
| `IOAPIC_NUM_IRQS` | int | 24 | IOAPIC pin count. Sets the width of `ioapic_irq_in`. |
| `GPIO_WIDTH` | int | 32 | GPIO pin count. |
| `GPIO_SYNC_STAGES` | int | 2 | GPIO input synchroniser depth. |
| `UART_FIFO_DEPTH` | int | 16 | UART FIFO depth. |
| `UART_SYNC_STAGES` | int | 2 | UART input synchroniser depth. |
| `SMBUS_FIFO_DEPTH` | int | 32 | SMBus FIFO depth. |
| `IRQ_SMBUS` | int | 10 | **Choice, not convention.** The legacy line SMBus is routed to. |
| `IRQ_GPIO` | int | 11 | **Choice, not convention.** The legacy line GPIO is routed to. |

### Why only two interrupt lines are parameters

IRQ0, IRQ4, IRQ8 and IRQ9 are fixed as `localparam` inside the module because
they come from the published typical-assignment table: the system timer, COM1,
the RTC alarm and ACPI respectively. Exposing them would invite silently
diverging from what every driver already assumes.

SMBus and GPIO have no traditional assignment - the table lists IRQ10 and IRQ11
as available - so those two are this subsystem's choice and are parameters an
integrator can move.

## Ports

### Clock and Reset

| Port | Dir | Width | Notes |
| --- | --- | --- | --- |
| `pclk` | in | 1 | APB clock. The only functional clock in this configuration. |
| `presetn` | in | 1 | APB reset, active low, asynchronous. |
| `hpet_clk`, `hpet_resetn` | in | 1 each | Unused: `u_hpet` is `CDC_ENABLE(0)`. Tie to `pclk` / `presetn`. |
| `pit_clk`, `pit_resetn` | in | 1 each | Unused: `CDC_ENABLE(0)`. Tie to `pclk` / `presetn`. |
| `rtc_clk`, `rtc_resetn` | in | 1 each | Unused in this configuration. Tie to `pclk` / `presetn`. |
| `smbus_clk`, `smbus_resetn` | in | 1 each | Unused: `CDC_ENABLE(0)`. Tie to `pclk` / `presetn`. |
| `pm_clk`, `pm_resetn` | in | 1 each | Unused: `CDC_ENABLE(0)`. Tie to `pclk` / `presetn`. |
| `ioapic_clk`, `ioapic_resetn` | in | 1 each | Unused: `CDC_ENABLE(0)`. Tie to `pclk` / `presetn`. |
| `gpio_clk`, `gpio_rstn` | in | 1 each | Unused: `CDC_ENABLE(0)`. Note `_rstn`, not `_resetn`. |
| `uart_clk`, `uart_rstn` | in | 1 each | Unused: `CDC_ENABLE(0)`. Note `_rstn`, not `_resetn`. |

See [Clocks and Reset](../ch01_overview/03_clocks_and_reset.md) for why the
secondary clocks are present but unused, and what to do about it.

### APB4 Slave Interface

The single entry point to the subsystem.

| Port | Dir | Width | Notes |
| --- | --- | --- | --- |
| `s_apb_PSEL` | in | 1 | |
| `s_apb_PENABLE` | in | 1 | |
| `s_apb_PADDR` | in | `ADDR_WIDTH` | **Full system address**, not a window offset. |
| `s_apb_PWRITE` | in | 1 | |
| `s_apb_PWDATA` | in | `DATA_WIDTH` | |
| `s_apb_PSTRB` | in | `STRB_WIDTH` | Carried through to the selected block. |
| `s_apb_PPROT` | in | 3 | Carried through to the selected block. |
| `s_apb_PRDATA` | out | `DATA_WIDTH` | |
| `s_apb_PSLVERR` | out | 1 | Also the decode-miss response. |
| `s_apb_PREADY` | out | 1 | |

### Peripheral External Interfaces

| Block | Inputs | Outputs |
| --- | --- | --- |
| HPET | - | `hpet_timer_irq[HPET_NUM_TIMERS-1:0]`, `hpet_legacy_irq0`, `hpet_legacy_irq8` |
| 8259 PIC | `pic_irq_in[15:0]` | `pic_int_out` |
| 8254 PIT | `pit_gate_in[PIT_NUM_COUNTERS-1:0]` | `pit_timer_irq[PIT_NUM_COUNTERS-1:0]` |
| RTC | - | `rtc_alarm_irq`, `rtc_second_irq` |
| SMBus | `smb_scl_i`, `smb_sda_i` | `smb_scl_o`, `smb_scl_t`, `smb_sda_o`, `smb_sda_t`, `smb_interrupt` |
| PM/ACPI | `pm_gpe_events[31:0]`, `pm_gpe1_events[31:0]`, `pm_power_button_n`, `pm_sleep_button_n`, `pm_rtc_alarm`, `pm_ext_wake_n`, `pm_wdt_reset_n`, `pm_ext_reset_n`, `pm_power_domain_ack[7:0]` | `pm_clock_gate_en[31:0]`, `pm_power_domain_en[7:0]`, `pm_sys_reset_req`, `pm_periph_reset_req`, `pm_interrupt` |
| IOAPIC | `ioapic_irq_in[IOAPIC_NUM_IRQS-1:0]`, `ioapic_irq_out_ready`, `ioapic_irq_out_retry`, `ioapic_eoi_in`, `ioapic_eoi_vector[7:0]` | `ioapic_irq_out_valid`, `ioapic_irq_out_vector[7:0]`, `ioapic_irq_out_dest[7:0]`, `ioapic_irq_out_deliv_mode[2:0]`, `ioapic_irq_out_dest_mode` |
| GPIO | `gpio_in[GPIO_WIDTH-1:0]` | `gpio_out[GPIO_WIDTH-1:0]`, `gpio_oe[GPIO_WIDTH-1:0]`, `gpio_irq` |
| UART 16550 | `uart_rx`, `uart_cts_n`, `uart_dsr_n`, `uart_ri_n`, `uart_dcd_n` | `uart_tx`, `uart_dtr_n`, `uart_rts_n`, `uart_rxrdy_n`, `uart_txrdy_n`, `uart_out1_n`, `uart_out2_n`, `uart_irq` |
| Subsystem | - | `rlb_irq_out` |

### Ports that need care

| Port | What to know |
| --- | --- |
| `pic_irq_in[2]` | **Ignored.** Master IR2 is the cascade input, forced from the slave controller. Driving this bit reaches nothing. |
| `pic_irq_in[15:8]` | Goes to the **slave** controller, not the master. |
| `ioapic_irq_out_retry` | Tie low if the receiver always accepts. It is the IOAPIC's half of delegated lowest-priority delivery. |
| `pm_power_domain_ack[7:0]` | Tie high unless the rail sequencer is enabled with an acknowledge requirement. |
| `pm_wdt_reset_n`, `pm_ext_reset_n` | Tie high (inactive) if the system has no watchdog or reset button. They are reported in the PM reset-status register. |
| `pm_gpe1_events[31:0]` | Tie to zero when the system has only one GPE bank. |
| `uart_rxrdy_n`, `uart_txrdy_n` | DMA handshake pins. Leave unconnected in a programmed-I/O system. |
| `hpet_timer_irq` | Not routed into the interrupt fabric. Wire it yourself if you need it delivered. |
| `rlb_irq_out` | A pure OR of every block interrupt including `pic_int_out`. Drives nothing internally. |

## Address Decode Contract

| Property | Value |
| --- | --- |
| Base | `BASE_ADDR`, default `0xFEC0_0000` |
| Window size | `0x1000` (4KB) |
| Window count | 10, indices 0-9 |
| Slave index | `PADDR[15:12]` |
| Offset seen by a block | `PADDR[11:0]` |
| Reserved windows | none - all ten are assigned |
| Unmapped address | completes normally with `PSLVERR` asserted; it does not hang |

The decode-miss behaviour is a property of the generated crossbar, and it is the
reason the crossbar must be regenerated rather than hand-edited.

## Integration Checklist

1. Drive `pclk` and `presetn`. Tie every secondary clock to `pclk` and every
   secondary reset to `presetn` unless you have rebuilt a block with
   `CDC_ENABLE=1`.
2. Connect the APB4 slave port, passing the **full** system address.
3. Decide whether you want the internal interrupt fabric, the external pins, or
   both. Both is the default and costs nothing: they are OR-ed.
4. If you are not driving external legacy interrupts, tie `pic_irq_in` and
   `ioapic_irq_in` to zero. The fabric then supplies everything.
5. Tie off the PM pins listed above according to what your system actually has.
6. Choose `IRQ_SMBUS` and `IRQ_GPIO` if the defaults clash with your platform.
7. Decide how the IOAPIC's delivery handshake is consumed, and tie
   `ioapic_irq_out_retry` low if your receiver always accepts.
8. Use `rlb_irq_out` if you want a single interrupt input; otherwise use
   `pic_int_out` and the IOAPIC delivery interface.

## Related Documents

- [Architecture](../ch01_overview/02_architecture.md)
- [Clocks and Reset](../ch01_overview/03_clocks_and_reset.md)
- [Initialization](../ch04_programming/01_initialization.md)
- [Window Map](../ch05_registers/01_register_map.md)
