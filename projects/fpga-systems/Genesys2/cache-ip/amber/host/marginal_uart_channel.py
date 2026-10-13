# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Marginal-UART byte-channel decorator for the Genesys2 amber bring-up.

The Genesys2 FT232R UART link drops whole transactions under load. That
recovery belongs BELOW the ASCII command interpreter, as a ByteChannel
decorator, so the shared UARTAxiBridge protocol stays identical to every
other flow and the retry logic rides only where the electrical link needs it.

The decorator:
  * drains stray boot/programming bytes before the first command,
  * skips junk lines (NULs, dots, silence) that arrive before a response,
  * re-transmits the last command and waits again when a response is missing
    or malformed, up to a small retry limit.

It duck-types the serial.Serial subset that UARTAxiBridge needs:
write / read_until / reset_input_buffer / reset_output_buffer / close /
is_open.
"""

from __future__ import annotations

import logging
import time
from typing import Optional


class MarginalUartChannel:
    """Wrap a ByteChannel with FT232R-drop recovery and boot-junk tolerance."""

    def __init__(self, inner, *, max_retries: int = 4,
                 junk_lines_to_drain: int = 4,
                 inter_line_timeout_s: float = 0.25,
                 log: Optional[logging.Logger] = None):
        self.inner = inner
        self.max_retries = max_retries
        self.junk_lines_to_drain = junk_lines_to_drain
        self.inter_line_timeout_s = inter_line_timeout_s
        self.log = log or logging.getLogger("marginal_uart")
        self._last_cmd: Optional[bytes] = None
        self._boot_drained = False

    # ------------------------------------------------------------------
    # ByteChannel surface
    # ------------------------------------------------------------------
    def write(self, data: bytes) -> int:
        if not self._boot_drained:
            self._drain_boot_junk()
        self._last_cmd = bytes(data)
        return self.inner.write(data)

    def read_until(self, expected: bytes = b"\n",
                   size: int | None = None) -> bytes:
        # UARTAxiBridge always sends a command then immediately reads the
        # response. Retry here means: get a line, decide if it is a valid
        # response to the last command; if not, purge and re-send.
        for attempt in range(self.max_retries):
            line = self._read_one_line()
            if line is None:
                self.log.debug("marginal: no line (attempt %d)", attempt)
            elif self._is_valid_response(line):
                return line
            else:
                self.log.debug("marginal: junk line %r (attempt %d)",
                               line, attempt)

            if attempt + 1 < self.max_retries and self._last_cmd is not None:
                self.inner.reset_input_buffer()
                time.sleep(0.01)
                self.inner.write(self._last_cmd)

        # Return whatever we got so the caller can fail normally.
        return b""

    def reset_input_buffer(self) -> None:
        self.inner.reset_input_buffer()

    def reset_output_buffer(self) -> None:
        self.inner.reset_output_buffer()

    def close(self) -> None:
        self.inner.close()

    @property
    def is_open(self) -> bool:
        return getattr(self.inner, "is_open", True)

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------
    def _drain_boot_junk(self) -> None:
        """Purge stale lines that the FPGA emitted before the bridge woke up."""
        self._boot_drained = True
        for _ in range(self.junk_lines_to_drain):
            line = self._read_one_line()
            if line is None:
                break
            self.log.debug("marginal: drained boot line %r", line)

    def _read_one_line(self) -> Optional[bytes]:
        """Read one newline-terminated line, with a bounded wait."""
        if not getattr(self.inner, "is_open", True):
            return None
        try:
            # read_until already blocks up to the underlying serial timeout.
            return self.inner.read_until(b"\n", size=64)
        except Exception as exc:  # noqa: BLE001
            self.log.debug("marginal: read_until raised %s", exc)
            return None

    def _is_valid_response(self, line: bytes) -> bool:
        """Does this line look like a response to the last W/R command?"""
        stripped = line.strip().strip(b"\x00").lstrip(b".")
        if not stripped:
            return False
        if stripped == b"ERR":
            return True
        cmd = self._last_cmd or b""
        if cmd.startswith(b"W "):
            return stripped == b"OK"
        if cmd.startswith(b"R "):
            return stripped.startswith(b"0x")
        # Unknown command shape: accept anything non-empty to avoid starving
        # higher layers.
        return True
