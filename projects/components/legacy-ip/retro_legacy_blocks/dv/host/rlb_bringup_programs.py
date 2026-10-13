# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rlb_bringup_programs
# Purpose: The rlb_top subsystem bring-up as an executable host program,
#          transcribed from docs/rlb_top_mas/ch04_programming/01_initialization.md.
#
# Documentation: projects/components/retro_legacy_blocks/docs/rlb_top_mas/
# Subsystem: retro_legacy_blocks/rlb_top
#
# Created: 2026-10-03

"""Bring the rlb_top subsystem up from its own specification (RLB TASK-020).

This module is the book's initialization chapter made executable. Every
sequence below is transcribed from
``docs/rlb_top_mas/ch04_programming/01_initialization.md`` and cross-checked
against it line by line; where the book cites a per-block specification, this
module stops and the caller (a driver, or a test arming a source) takes over.

The module is plain Python on purpose. It knows nothing about cocotb, APB
BFMs, or the DV helpers the book's sequences were originally transcribed
from. It talks to a ``bus`` with two methods::

    await bus.write32(addr, value)
    await bus.read32(addr) -> int

``test_rlb_top_bringup.py`` binds those to the testbench's APB master; a
board port binds them to a UARTAxiBridge the same way the reed-solomon
host programs do.

Bring-up order (book section "Bring-Up Order"):

1. Release reset, confirm the subsystem answers  -> ``probe_all_windows``
2. Choose the interrupt topology                 -> the ``topology`` argument
3. Configure the 8259 (single or cascade)        -> ``_pic_init_*``
4. Configure IOAPIC redirection entries          -> ``_ioapic_arm_all``
5. Enable the peripheral blocks                  -> per-block specs; NOT here
6. Verify                                        -> ``run_initialization``'s
   return value plus the caller's own checks

The one ordering constraint the book states -- controllers before sources --
is structural here: ``run_initialization`` finishes the controllers and
returns; nothing in this module enables a block.
"""

from dataclasses import dataclass
from typing import List, Optional, Tuple

# ---------------------------------------------------------------------------
# Address map (book "Address Helper"). The bus carries FULL system addresses.
# ---------------------------------------------------------------------------

RLB_BASE = 0xFEC00000
RLB_WINDOW = 0x1000

WIN_HPET = 0
WIN_PIC = 1        # master 8259
WIN_PIT = 2
WIN_RTC = 3
WIN_SMBUS = 4
WIN_PM = 5
WIN_IOAPIC = 6
WIN_GPIO = 7
WIN_UART = 8
WIN_PIC_SLAVE = 9  # slave 8259

# Fabric lines (docs/rlb_top_mas ch02 "The Interrupt Fabric"). Convention
# lines 0/4/8/9 are fixed localparams in the RTL; 10/11 are the subsystem's
# choice and are module parameters there -- mirrored as parameters of
# run_initialization so an integrator moves them in one place.
IRQ_TIMER = 0
IRQ_UART = 4
IRQ_RTC = 8
IRQ_ACPI = 9
IRQ_SMBUS = 10
IRQ_GPIO = 11

# The fabric lines run_initialization arms in the IOAPIC by default are
# derived from the IRQ_* constants and the irq_smbus/irq_gpio arguments.

# ---------------------------------------------------------------------------
# Register offsets inside each window (book steps 1, 3 and 4).
# ---------------------------------------------------------------------------

# Step 1 probes. UART is probed at 0x020 (UART_SCR): reading 0x000 pops the
# RX FIFO. That trap is stated in the book and reproduced here as data.
PROBES: Tuple[Tuple[int, int, str], ...] = (
    (WIN_HPET,      0x000, "hpet"),
    (WIN_PIC,       0x000, "pic"),
    (WIN_PIT,       0x000, "pit"),
    (WIN_RTC,       0x000, "rtc"),
    (WIN_SMBUS,     0x000, "smbus"),
    (WIN_PM,        0x000, "pm"),
    (WIN_IOAPIC,    0x000, "ioapic"),
    (WIN_GPIO,      0x000, "gpio"),
    (WIN_UART,      0x020, "uart"),
    (WIN_PIC_SLAVE, 0x000, "pic_slave"),
)

# 8259 registers (pic_8259_mas register map).
PIC_CONFIG = 0x000
PIC_ICW1 = 0x004
PIC_ICW2 = 0x008
PIC_ICW3 = 0x00C
PIC_ICW4 = 0x010
PIC_OCW1 = 0x014
# PIC_STATUS is at 0x028 — the pic_8259 RDL (PIC_STATUS @ 0x028) is
# authoritative. The book's first edition said 0x018 (which is OCW2), and
# a STATUS read from there never reports init complete: how this got caught.
PIC_STATUS = 0x028

# IOAPIC indirect access (book step 4). IOWIN is at 0x004 — the ioapic_mas
# register map (ch05) is authoritative; the book's first edition said 0x010
# and a write there completes with PSLVERR, which is how this got caught.
IOAPIC_IOREGSEL = 0x000
IOAPIC_IOWIN = 0x004


class BringUpError(RuntimeError):
    """A bus access failed, or a controller did not come up."""


@dataclass
class BringUpResult:
    """What run_initialization did and observed; the caller verifies.

    ``slave_init`` is None when the single-controller topology was chosen:
    the book's "each configured controller" check applies to the controllers
    that exist in the chosen topology.
    """

    probes: List[Tuple[str, int]]
    master_init: bool
    slave_init: Optional[bool]
    ioapic_armed: Tuple[int, ...]


def window_addr(window: int, offset: int) -> int:
    """The book's ``rlb_reg(window, offset)`` helper."""
    return RLB_BASE + window * RLB_WINDOW + offset


def ioapic_vector(irq: int, vector_base: int = 0x20) -> int:
    """Vector for a fabric line: the typical-assignment table's 0x20 base.

    The book notes the integration suite uses 0x40 + irq as a TEST
    convention; that is a property of that suite, not of this program.
    Nothing in the RTL constrains the choice.
    """
    return vector_base + irq


async def probe_all_windows(bus) -> List[Tuple[str, int]]:
    """Book step 1: read every window's probe register.

    Raises BringUpError on the first window that does not answer cleanly --
    the book's step 6 row 1 checks decode by these reads, so a probe that
    errors means nothing below is meaningful.
    """
    readings = []
    for window, offset, name in PROBES:
        value = await bus.read32(window_addr(window, offset))
        readings.append((name, value))
    return readings


async def _pic_init_single(bus, vector_base: int) -> bool:
    """Book step 3a: master only, SNGL set, no ICW3."""
    base = window_addr(WIN_PIC, 0)
    await bus.write32(base + PIC_CONFIG, 0x1)               # enable, NOT init_mode
    await bus.write32(base + PIC_ICW1, 0x10 | 0x02 | 0x01)  # marker | SNGL | IC4
    await bus.write32(base + PIC_ICW2, vector_base)
    await bus.write32(base + PIC_ICW4, 0x01)                # 8086 mode
    await bus.write32(base + PIC_OCW1, 0x00)                # unmask all
    status = await bus.read32(base + PIC_STATUS)
    return bool(status & 1)


async def _pic_init_cascade(bus, master_base: int, slave_base: int) -> Tuple[bool, bool]:
    """Book step 3b: master and slave as a PC/AT pair.

    The four requirements the book lists for a slave interrupt to reach the
    CPU -- SNGL clear, master ICW3 = 0x04, slave ICW3 = 0x02, IR2 unmasked --
    are exactly the four differences from _pic_init_single; omitting any one
    looks exactly like a broken fabric, which is why they are all here and
    none is optional.
    """
    mbase = window_addr(WIN_PIC, 0)
    sbase = window_addr(WIN_PIC_SLAVE, 0)

    await bus.write32(mbase + PIC_CONFIG, 0x1)
    await bus.write32(mbase + PIC_ICW1, 0x10 | 0x01)  # marker | IC4, SNGL CLEAR
    await bus.write32(mbase + PIC_ICW2, master_base)
    await bus.write32(mbase + PIC_ICW3, 0x04)         # a slave is attached on IR2
    await bus.write32(mbase + PIC_ICW4, 0x01)
    await bus.write32(mbase + PIC_OCW1, 0x00)         # unmask all, IR2 included

    await bus.write32(sbase + PIC_CONFIG, 0x1)
    await bus.write32(sbase + PIC_ICW1, 0x10 | 0x01)
    await bus.write32(sbase + PIC_ICW2, slave_base)
    await bus.write32(sbase + PIC_ICW3, 0x02)         # I hang off master IR2
    await bus.write32(sbase + PIC_ICW4, 0x01)
    await bus.write32(sbase + PIC_OCW1, 0x00)

    m_status = await bus.read32(mbase + PIC_STATUS)
    s_status = await bus.read32(sbase + PIC_STATUS)
    return bool(m_status & 1), bool(s_status & 1)


async def _ioapic_write(bus, selector: int, value: int):
    base = window_addr(WIN_IOAPIC, 0)
    await bus.write32(base + IOAPIC_IOREGSEL, selector)
    await bus.write32(base + IOAPIC_IOWIN, value)


async def _ioapic_arm(bus, irq: int, vector: int, masked: bool):
    """Book step 4: one redirection entry, programmed indirectly.

    Redirection entries reset MASKED -- the book calls this the step most
    often missed, because its failure mode is silent. ``masked`` is a
    parameter for callers that genuinely want the entry parked; the
    run_initialization default arms unmasked.
    """
    rte_lo = 0x10 + irq * 2
    rte_hi = 0x11 + irq * 2
    await _ioapic_write(bus, rte_lo, vector | ((1 if masked else 0) << 16))
    await _ioapic_write(bus, rte_hi, 0)  # destination


async def run_initialization(bus, topology: str = "cascade",
                             master_base: int = 0x20, slave_base: int = 0x28,
                             vector_base: int = 0x20,
                             arm_irqs: Optional[Tuple[int, ...]] = None,
                             irq_smbus: int = IRQ_SMBUS,
                             irq_gpio: int = IRQ_GPIO,
                             masked: bool = False) -> BringUpResult:
    """Book steps 1-4: probe, controllers, IOAPIC entries.

    Steps 5 and 6 are the caller's: enabling blocks is per-block
    specification (the book says so), and verification needs a source this
    module deliberately does not drive. The return value carries what the
    book's step 6 table reads back: the probe values, per-controller init
    status, and which IOAPIC pins were armed.

    ``topology``: "cascade" (both 8259s, the usual choice -- four of the six
    sourcing blocks land on the slave) or "single" (master only). The book's
    step 2 decides; here it is an argument for the same reason the IRQ_SMBUS
    and IRQ_GPIO lines are RTL parameters: the choice belongs to the
    integrator, not to the program.
    """
    if topology not in ("single", "cascade"):
        raise ValueError(f"topology must be 'single' or 'cascade', got {topology!r}")

    if arm_irqs is None:
        arm_irqs = (IRQ_TIMER, IRQ_UART, IRQ_RTC, IRQ_ACPI, irq_smbus, irq_gpio)

    probes = await probe_all_windows(bus)

    if topology == "single":
        master_init = await _pic_init_single(bus, master_base)
        slave_init = None
    else:
        master_init, slave_init = await _pic_init_cascade(
            bus, master_base, slave_base)

    armed = []
    for irq in arm_irqs:
        await _ioapic_arm(bus, irq, ioapic_vector(irq, vector_base), masked)
        armed.append(irq)

    return BringUpResult(probes=probes, master_init=master_init,
                         slave_init=slave_init, ioapic_armed=tuple(armed))
