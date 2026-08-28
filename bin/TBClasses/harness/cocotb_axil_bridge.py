# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Cocotb-side UART transport for the char harness — the sim half of the
silicon/sim equivalence.

The host driver stack (UARTAxiBridge -> DDR2CharDriver -> pumice_master
programs) is synchronous and speaks an ASCII W/R byte protocol. On silicon
those bytes go out a pyserial port; here they go to a cocotb `UARTMaster`
driving the DUT's `i_uart_rx`, and replies are captured from `o_uart_tx` by a
`UARTMonitor`. Because the *identical* `UARTAxiBridge` produces the bytes in
both cases (only the ByteChannel differs), sim and FPGA are equivalent at the
wire.

Sync/async bridge: the synchronous program runs in a worker thread (via
`cocotb.external`); this channel's `write`/`read_until` are `cocotb.function`
wrappers — the inverse of `external`. When the worker calls them, cocotb hands
the wrapped coroutine to the scheduler, ADVANCES SIM TIME while it drives the
UARTMaster / drains the UARTMonitor, and returns the result to the worker. This
is the pattern that actually steps the simulation (a free-running pump + plain
thread queues does not — the scheduler stalls while the worker blocks).
"""

from __future__ import annotations

import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.uart.uart_components import UARTMaster, UARTMonitor


class CocotbUartChannel:
    """ByteChannel over a cocotb UARTMaster/Monitor, callable from a worker
    thread (under cocotb.external) via cocotb.function wrappers.

    Duck-types the subset of serial.Serial that UARTAxiBridge uses:
    write / read_until / reset_*_buffer / close / is_open.
    """

    def __init__(self, dut, clock, clks_per_bit: int, *,
                 rx_signal: str = "i_uart_rx", tx_signal: str = "o_uart_tx",
                 log=None, max_idle_cycles: int = 400_000):
        self._clock = clock
        self._max_idle = max_idle_cycles
        self._master = UARTMaster(dut, "uart_m", rx_signal, clock,
                                  clks_per_bit=clks_per_bit, log=log)
        self._monitor = UARTMonitor(dut, "uart_mon", tx_signal, clock,
                                    clks_per_bit=clks_per_bit, direction="TX",
                                    log=log)
        # cocotb.function: lets the synchronous worker call these coroutines and
        # block until they complete, while the scheduler advances the sim.
        self._send = cocotb.function(self._send_coro)
        self._recv = cocotb.function(self._recv_coro)

    async def _send_coro(self, data: bytes):
        for b in data:
            await self._master.send(b)

    async def _recv_coro(self, expected: bytes, size):
        buf = bytearray()
        idle = 0
        while True:
            progressed = False
            while self._monitor._recvQ:
                buf.append(self._monitor._recvQ.popleft().data)
                progressed = True
                if expected and buf.endswith(expected):
                    return bytes(buf)
                if size is not None and len(buf) >= size:
                    return bytes(buf)
            idle = 0 if progressed else idle + 1
            if idle >= self._max_idle:
                return bytes(buf)  # wall-of-silence => partial, like a serial timeout
            await RisingEdge(self._clock)

    # ----- ByteChannel surface (called from the worker thread) -------------
    def write(self, data: bytes) -> int:
        self._send(bytes(data))
        return len(data)

    def read_until(self, expected: bytes = b"\n", size: int | None = None) -> bytes:
        return self._recv(expected, size)

    def reset_input_buffer(self) -> None:
        self._monitor._recvQ.clear()

    def reset_output_buffer(self) -> None:
        pass

    def close(self) -> None:
        pass

    @property
    def is_open(self) -> bool:
        return True

    # ----- BFM access (called from the cocotb side, not the worker thread) --
    # A testbench that also needs coroutine-level UART access must drive THESE,
    # not a second UARTMaster/UARTMonitor of its own: two masters on the same
    # rx pin is a multi-driver conflict, and two monitors race for the same
    # bytes. Exposing the pair is what lets a TB keep its own async helpers
    # while there is still exactly one wire.
    @property
    def master(self):
        """The UARTMaster driving the DUT's rx pin."""
        return self._master

    @property
    def monitor(self):
        """The UARTMonitor watching the DUT's tx pin."""
        return self._monitor


def make_uart_channel(dut, clock, clks_per_bit: int, **kwargs) -> CocotbUartChannel:
    """Build a CocotbUartChannel to hand to UARTAxiBridge(channel=...)."""
    return CocotbUartChannel(dut, clock, clks_per_bit, **kwargs)
