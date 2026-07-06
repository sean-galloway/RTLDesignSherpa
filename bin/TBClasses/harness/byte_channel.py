#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Byte-transport abstraction for the char-harness UART bridge.

The `UARTAxiBridge` protocol layer (W/R ASCII commands) is transport-agnostic:
it only needs something that can push bytes out and pull a line back. That
"something" is a `ByteChannel`. The equivalence between silicon and sim lives
here — the *identical* ASCII byte stream is produced by the bridge and simply
handed to a different channel:

    SerialChannel      -> pyserial /dev/ttyUSB*        (real FPGA)
    CocotbUartChannel  -> UARTMaster/UARTMonitor pins  (sim; see cocotb test)

`TracingChannel` wraps any channel and records every (direction, bytes) event,
so a program run against two channels can be proven byte-for-byte identical.

The interface intentionally mirrors the subset of `serial.Serial` that
`UARTAxiBridge` uses, so `SerialChannel` is a thin passthrough and the bridge
needs no special-casing.
"""

from __future__ import annotations

from typing import List, Protocol, Tuple, runtime_checkable


@runtime_checkable
class ByteChannel(Protocol):
    """Minimal byte pipe used by UARTAxiBridge (subset of serial.Serial)."""

    def write(self, data: bytes) -> int: ...
    def read_until(self, expected: bytes = b"\n", size: int | None = None) -> bytes: ...
    def reset_input_buffer(self) -> None: ...
    def reset_output_buffer(self) -> None: ...
    def close(self) -> None: ...

    @property
    def is_open(self) -> bool: ...


class SerialChannel:
    """Real UART transport over pyserial. Thin wrapper so the bridge is
    channel-agnostic; opens the port on construction (import serial lazily so
    board-less/sim callers never need pyserial installed)."""

    def __init__(self, port: str = "/dev/ttyUSB1", baudrate: int = 115200,
                 timeout: float = 1.0):
        import serial  # lazy: only the silicon path needs pyserial
        self._ser = serial.Serial(port, baudrate, timeout=timeout)
        self.port = port
        self.baudrate = baudrate

    def write(self, data: bytes) -> int:
        return self._ser.write(data)

    def read_until(self, expected: bytes = b"\n", size: int | None = None) -> bytes:
        return self._ser.read_until(expected, size)

    def reset_input_buffer(self) -> None:
        self._ser.reset_input_buffer()

    def reset_output_buffer(self) -> None:
        self._ser.reset_output_buffer()

    def close(self) -> None:
        if self._ser.is_open:
            self._ser.close()

    @property
    def is_open(self) -> bool:
        return self._ser.is_open


class TracingChannel:
    """Decorator that records the byte stream flowing through an inner channel.

    Every `write` appends ('tx', data); every `read_until` result appends
    ('rx', data). `trace` is the ordered list of events; `wire_bytes()` returns
    just the concatenated TX+RX stream for a coarse diff. Two program runs whose
    traces match are equivalent at the byte layer — the equivalence oracle.
    """

    def __init__(self, inner: ByteChannel):
        self.inner = inner
        self.trace: List[Tuple[str, bytes]] = []

    def write(self, data: bytes) -> int:
        self.trace.append(("tx", bytes(data)))
        return self.inner.write(data)

    def read_until(self, expected: bytes = b"\n", size: int | None = None) -> bytes:
        data = self.inner.read_until(expected, size)
        self.trace.append(("rx", bytes(data)))
        return data

    def reset_input_buffer(self) -> None:
        self.inner.reset_input_buffer()

    def reset_output_buffer(self) -> None:
        self.inner.reset_output_buffer()

    def close(self) -> None:
        self.inner.close()

    @property
    def is_open(self) -> bool:
        return self.inner.is_open

    def wire_bytes(self) -> bytes:
        return b"".join(data for _dir, data in self.trace)

    def tx_bytes(self) -> bytes:
        """Just the host->device stream (the deterministic, program-driven half)."""
        return b"".join(data for d, data in self.trace if d == "tx")
