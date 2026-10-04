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

# RLB Top - Initialization and Programming Guide

## Scope

This chapter is the **subsystem** bring-up: the order in which the pieces have to
be configured, and the parts that only exist at the integration level - the
interrupt controllers, the IOAPIC redirection table, and the cascade. Programming
a block's own function (setting a timer period, configuring a UART's baud rate)
belongs to that block's specification.

The sequences below are the ones the integration test suite executes, which is
why they are known to work rather than merely plausible.

There is also an executable transcription of this chapter:
`dv/host/rlb_bringup_programs.py` runs steps 1-4 against any
`write32`/`read32` bus (a board port binds the same program to a UART
bridge), and `dv/tests/test_rlb_top_bringup.py` proves the book sufficient
by driving bring-up through that program alone — it never calls the DV
helpers this chapter was transcribed from. Edit this chapter, then run that
test: it caught two wrong register offsets in this chapter's first edition
(`IOWIN`, `PIC_STATUS`), which is exactly the drift it exists to catch.

## Address Helper

Every register access in this chapter goes through a window. One helper keeps the
rest readable:

```c
#define RLB_BASE      0xFEC00000u
#define RLB_WINDOW    0x1000u

#define WIN_HPET      0
#define WIN_PIC       1      /* master 8259 */
#define WIN_PIT       2
#define WIN_RTC       3
#define WIN_SMBUS     4
#define WIN_PM        5
#define WIN_IOAPIC    6
#define WIN_GPIO      7
#define WIN_UART      8
#define WIN_PIC_SLAVE 9      /* slave 8259 */

static inline volatile uint32_t *rlb_reg(unsigned window, unsigned offset)
{
    return (volatile uint32_t *)(RLB_BASE + window * RLB_WINDOW + offset);
}
```

## Bring-Up Order

| Step | What | Why here |
| --- | --- | --- |
| 1 | Release reset, confirm the subsystem answers | Nothing below is meaningful if decode is broken |
| 2 | Decide the interrupt topology | Determines whether step 3 is the single or cascade sequence |
| 3 | Configure the 8259 (single **or** cascaded pair) | The controllers must be initialised before any source is enabled |
| 4 | Configure IOAPIC redirection entries | Entries reset **masked**; an unconfigured entry silently delivers nothing |
| 5 | Enable the peripheral blocks | Only now can a source assert without being lost |
| 6 | Verify | Read back status rather than assuming |

The ordering constraint that actually matters is steps 3 and 4 before step 5. A
block enabled before its controller is configured asserts into a controller that
is still in its initialisation state, and in edge-triggered mode the result is a
latched interrupt nobody is ready to service.

## Step 1: Confirm the Subsystem Answers

Each window has a read-safe probe register. Reading all ten is the cheapest
possible confirmation that the crossbar and every block are alive.

```c
/* Read-safe probe per window. */
static const struct { unsigned window, offset; const char *name; } probes[] = {
    { WIN_HPET,      0x000, "hpet"      },  /* HPET_ID, read-only identity */
    { WIN_PIC,       0x000, "pic"       },  /* PIC_CONFIG */
    { WIN_PIT,       0x000, "pit"       },  /* PIT_CONFIG */
    { WIN_RTC,       0x000, "rtc"       },  /* RTC_CONFIG */
    { WIN_SMBUS,     0x000, "smbus"     },  /* SMBUS_CONTROL */
    { WIN_PM,        0x000, "pm"        },  /* ACPI_CONTROL */
    { WIN_IOAPIC,    0x000, "ioapic"    },  /* IOREGSEL */
    { WIN_GPIO,      0x000, "gpio"      },  /* GPIO_CONTROL */
    { WIN_UART,      0x020, "uart"      },  /* UART_SCR -- see the warning */
    { WIN_PIC_SLAVE, 0x000, "pic_slave" },  /* PIC_CONFIG on the slave */
};
```

**Do not probe the UART at offset `0x000`.** That is the receive buffer, and
reading it pops a byte off the RX FIFO. Use the scratch register at `0x020`. This
is a real trap: a "harmless" identity read that destroys received data.

An unmapped address is also a useful probe in the other direction: it must
complete with `PSLVERR` asserted rather than hang. If it hangs, the crossbar is
not the generated one.

## Step 2: Choose the Interrupt Topology

| Topology | Use when | Configure |
| --- | --- | --- |
| Single 8259 | Nothing you care about is on IRQ8-15 | Master only, `SNGL` set |
| Cascaded pair | Anything on IRQ8-15 - which includes the RTC, ACPI, SMBus and GPIO | Both controllers, `SNGL` clear |
| IOAPIC | You want vectored delivery with per-pin destination control | Redirection entries, step 4 |

The fabric feeds all of these simultaneously. Choosing one does not disable the
others.

Note which sources land where: **IRQ0 and IRQ4 reach the master; IRQ8, IRQ9,
IRQ10 and IRQ11 reach the slave.** With four of the six sourcing blocks on the
slave controller, the single-controller topology is rarely what you want.

## Step 3a: Single-Controller Configuration

Master only, in single mode. This is enough to get `INT` asserting.

```c
#define PIC_CONFIG 0x000
#define PIC_ICW1   0x004
#define PIC_ICW2   0x008
#define PIC_ICW3   0x00C
#define PIC_ICW4   0x010
#define PIC_OCW1   0x014
#define PIC_STATUS 0x028

int pic_init_single(uint8_t vector_base)   /* vector_base e.g. 0x20 */
{
    *rlb_reg(WIN_PIC, PIC_CONFIG) = 0x1;          /* enable, NOT init_mode */
    *rlb_reg(WIN_PIC, PIC_ICW1)   = 0x10 | 0x02 | 0x01;  /* marker | SNGL | IC4 */
    *rlb_reg(WIN_PIC, PIC_ICW2)   = vector_base;
    /* No ICW3: SNGL is set, so the controller does not expect one. */
    *rlb_reg(WIN_PIC, PIC_ICW4)   = 0x01;         /* 8086 mode */
    *rlb_reg(WIN_PIC, PIC_OCW1)   = 0x00;         /* unmask all */

    return (*rlb_reg(WIN_PIC, PIC_STATUS) & 1) != 0;   /* init complete */
}
```

**`PIC_CONFIG` must set the enable bit without `init_mode`.** Setting
`init_mode` here sends the initialisation state machine back to its idle state
once the sequence completes, and the controller ends up unconfigured. This is
the single most likely way to get a controller that accepts every write and then
does nothing.

`ICW1` here is `0x13`: the marker bit, `SNGL`, and `IC4`. Level-triggered mode
(`LTIM`) is left clear, so the controller is edge-triggered - which matters when
clearing an interrupt, because `INT` latches until acknowledged.

## Step 3b: Cascaded-Pair Configuration

Both controllers, as a master and slave pair. Anything arriving on IRQ8-15
requires this.

```c
int pic_init_cascade(uint8_t master_base, uint8_t slave_base)  /* e.g. 0x20, 0x28 */
{
    /* ---- MASTER, window 1 */
    *rlb_reg(WIN_PIC, PIC_CONFIG) = 0x1;
    *rlb_reg(WIN_PIC, PIC_ICW1)   = 0x10 | 0x01;  /* marker | IC4, SNGL CLEAR */
    *rlb_reg(WIN_PIC, PIC_ICW2)   = master_base;
    *rlb_reg(WIN_PIC, PIC_ICW3)   = 0x04;         /* a slave is attached on IR2 */
    *rlb_reg(WIN_PIC, PIC_ICW4)   = 0x01;
    *rlb_reg(WIN_PIC, PIC_OCW1)   = 0x00;         /* unmask all, IR2 included */

    /* ---- SLAVE, window 9 */
    *rlb_reg(WIN_PIC_SLAVE, PIC_CONFIG) = 0x1;
    *rlb_reg(WIN_PIC_SLAVE, PIC_ICW1)   = 0x10 | 0x01;
    *rlb_reg(WIN_PIC_SLAVE, PIC_ICW2)   = slave_base;
    *rlb_reg(WIN_PIC_SLAVE, PIC_ICW3)   = 0x02;   /* I hang off master IR2 */
    *rlb_reg(WIN_PIC_SLAVE, PIC_ICW4)   = 0x01;
    *rlb_reg(WIN_PIC_SLAVE, PIC_OCW1)   = 0x00;

    return (*rlb_reg(WIN_PIC,       PIC_STATUS) & 1)
        && (*rlb_reg(WIN_PIC_SLAVE, PIC_STATUS) & 1);
}
```

Four things must all be true for a slave interrupt to reach the CPU, and omitting
any one of them looks exactly like a broken interrupt fabric:

1. The master is in cascade mode - `SNGL` **clear** in `ICW1`
2. The master's `ICW3` marks IR2 as carrying a slave (`0x04`)
3. The slave's `ICW3` states which master line it hangs off (`0x02`)
4. Master IR2 is unmasked in `OCW1`

**With `SNGL` clear, `ICW3` is mandatory.** The initialisation state machine
waits for it. Skipping it leaves the controller stuck mid-sequence.

Note that `master_base` and `slave_base` differ by 8 (`0x20` and `0x28`): the
slave's eight lines get their own vector block.

## Step 4: IOAPIC Redirection Entries

The IOAPIC is programmed indirectly: write the register index to `IOREGSEL`,
then the value to `IOWIN`.

```c
#define IOAPIC_IOREGSEL  0x000
#define IOAPIC_IOWIN     0x004
#define IOAPIC_BOOTINTX  /* see ioapic_mas ch05 for the offset */

static void ioapic_write(unsigned selector, uint32_t value)
{
    *rlb_reg(WIN_IOAPIC, IOAPIC_IOREGSEL) = selector;
    *rlb_reg(WIN_IOAPIC, IOAPIC_IOWIN)    = value;
}

/* Redirection entries are two 32-bit halves per pin. */
static unsigned rte_lo(unsigned irq) { return 0x10 + irq * 2; }
static unsigned rte_hi(unsigned irq) { return 0x11 + irq * 2; }

void ioapic_arm(unsigned irq, uint8_t vector, int masked)
{
    ioapic_write(rte_lo(irq), vector | ((masked ? 1u : 0u) << 16));
    ioapic_write(rte_hi(irq), 0);      /* destination */
}
```

**Redirection entries reset masked.** This is the step most often missed, and its
failure mode is the worst kind: the source reaches the IOAPIC's pin, the pin is
correct, and no message is ever delivered. That is indistinguishable from a
broken route unless you know to check the mask bit.

On vectors: the assignment is yours. The published typical-assignment table
suggests `0x20` through `0x2F` for the legacy lines. The integration test suite
uses `0x40 + irq`, which is a **test convention, not a hardware property** -
convenient because the vector then says which line produced it. Nothing in the
RTL constrains the choice.

## Step 5: Enable the Blocks

Per-block, from that block's specification. The only integration-level rule is
that this comes last.

If you enable the HPET's legacy-replacement mode, be aware it takes over IRQ0 and
IRQ8: HPET timers 0 and 1 then drive `hpet_legacy_irq0` and `hpet_legacy_irq8`
into those lines and are suppressed on `hpet_timer_irq`. You should silence the
8254 channel 0 and the RTC periodic interrupt to match, or two sources will be
competing for one line - legally, since the fabric ORs them, but confusingly.

## Step 6: Verify

| Check | How |
| --- | --- |
| Decode is sound | All ten probes read without error; an unmapped address sets `PSLVERR` |
| Controllers initialised | `PIC_STATUS` bit 0 set on each configured controller |
| Cascade consistent | Master IR2 follows the slave's `INT`. It should rise for an IRQ8-15 source - that is the cascade working, not a fault |
| A route works | Assert a source, confirm `pic_int_out`, and confirm an IOAPIC delivery with the vector you programmed |
| Anything at all is pending | `rlb_irq_out` is asserted while any block interrupt is |

## Clearing an Interrupt

In edge-triggered mode `pic_int_out` latches until the controller is
acknowledged. Software should acknowledge and issue EOI normally.

The integration test suite instead resets the whole subsystem between phases,
because the acknowledge and EOI paths carry their own block-level limitations
that would make an integration test fail on somebody else's known defect. That is
a verification convenience, not guidance for firmware. It is mentioned here only
because it explains a real consequence: **a reset drops all controller and IOAPIC
configuration**, so anything that resets must redo steps 3 and 4.

## Related Documents

- [Use Cases](02_use_cases.md) - complete routing paths, end to end
- [Architecture](../ch01_overview/02_architecture.md) - what the fabric does with a source
- [Window Map](../ch05_registers/01_register_map.md) - where each block's registers are specified
- [pic_8259_mas](../../pic_8259_mas/pic_8259_mas_index.md), [ioapic_mas](../../ioapic_mas/ioapic_mas_index.md) - the controllers' own specifications
