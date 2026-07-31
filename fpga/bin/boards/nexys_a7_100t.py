# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Digilent Nexys A7-100T (XC7A100T).

JTAG and the USB-UART are two interfaces of the SAME FT2232HQ, so the JTAG
serial also identifies the UART -- which is what lets `find_uart_ports()` return
only this board's ports when a Genesys 2 is on the chain too.
"""

from __future__ import annotations

from board import Board, BoardSpec
from boards import register


@register
class NexysA7100T(Board):
    SPEC = BoardSpec(
        name="nexys_a7_100t",
        display_name="Nexys A7-100T",
        part="xc7a100tcsg324-1",
        jtag_serial="210292B7D46F",
        uart_serial=None,          # same FT2232HQ as JTAG
        uart_baud=115200,
        notes=(
            "Digilent Adept steals the UART ttyUSB; do not power-cycle after "
            "programming or the port binding is lost.",
            "ftdi_sio does not block Vivado programming; no driver dance needed.",
        ),
    )
