# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Digilent Genesys 2 (XC7K325T).

The one that costs an afternoon: unlike the Nexys A7, the Genesys 2 UART is a
SEPARATE FT232R, not an interface of the JTAG FT2232. Matching UART ports
against the JTAG serial therefore finds nothing, which reads as "no board" when
the board is right there. `uart_serial` records the FT232R's own serial so the
lookup works, and both cables must be plugged in for a UART to exist at all.
"""

from __future__ import annotations

from board import Board, BoardSpec
from boards import register


@register
class Genesys2(Board):
    SPEC = BoardSpec(
        name="genesys2",
        display_name="Genesys 2",
        part="xc7k325tffg900-2",
        jtag_serial="200300B818A0",
        uart_serial="AU05X8RM",    # separate FT232R -- NOT the JTAG FT2232
        uart_baud=115200,
        notes=(
            "UART is a separate FT232R (serial AU05X8RM). Both it and the JTAG "
            "FT2232 must be enumerated or there is no UART, whatever the "
            "bitstream does.",
            "Preferred over the A7 for monitor work: the K325T is not on the "
            "100 MHz timing knife-edge the A7 stream_char build sits on.",
        ),
    )
