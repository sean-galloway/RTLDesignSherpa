# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: irq package
# Purpose: BFM for plain interrupt lines (level or pulse, scalar or vector)
#
# Created: 2026-09-28

"""Interrupt-line BFM package.

    from TBClasses.irq import IRQMonitor, IRQMonitorGroup, IRQPacket

    irqs = IRQMonitorGroup(dut, dut.pclk, {
        'gpio_irq':      None,     # width auto-detected
        'pic_int_out':   None,
        'pit_timer_irq': None,     # vector: one event per bit
        'rlb_irq_out':   None,
    }, title="RLB")
    irqs.start()
    ...
    ok, missing, unexpected = irqs.expect_only(['gpio_irq', 'pic_int_out',
                                                'rlb_irq_out'])

For a line WITH a handshake (valid/ready/retry) use GAXI instead -- see
vault/handbook/dv/bfm-usage.md. This package is for plain interrupt wires.
"""

from .irq_components import IRQMonitor, IRQMonitorGroup
from .irq_packet import IRQPacket

__all__ = [
    'IRQPacket',
    'IRQMonitor',
    'IRQMonitorGroup',
]
