#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board abstraction: find this board's UART, and program this board.

A `Board` is the machine-readable version of what used to live in tcl comments
and a handbook note: which JTAG serial, which FPGA part, and -- the part that
actually bites -- whether the UART is on the same FTDI as the JTAG or a separate
one. Seven copies of `program_fpga.tcl` each hardcoded a serial and invented
their own env-var name to override it; `boards/` holds those facts once.

    from boards import get_board
    b = get_board("nexys_a7_100t")
    b.find_uart_ports()                       # only THIS board's ports
    port = b.find_uart_port(probe=my_probe)   # ...and which one answers
    b.program("bitstream/ddr2_char.bit")      # vivado -mode batch, pinned serial

Subclass `Board` when a board needs different behaviour (see
`boards/genesys2.py`, whose UART is a separate FT232R); most boards need only a
`BoardSpec`.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from dataclasses import dataclass, field
from typing import List, Optional, Sequence

from uart_link import (DEFAULT_BAUD, Probe, UartLink, UartPort, find_port,
                       list_uart_ports, open_bridge)

# The one parameterized programming script, replacing the per-flow copies.
PROGRAM_TCL = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "program_fpga.tcl")


@dataclass(frozen=True)
class BoardSpec:
    """Everything about a board that host tooling needs to know.

    `jtag_serial` pins JTAG when several Digilent boards share a chain, and --
    when `uart_serial` is None -- doubles as the USB serial of the UART, because
    the two interfaces are on one FTDI part. `uart_serial` exists for boards
    where that is NOT true and the UART must be found some other way.
    """

    name: str                              # registry key
    display_name: str
    part: str                              # e.g. xc7a100tcsg324-1
    jtag_serial: Optional[str] = None      # Vivado hw_target serial
    uart_serial: Optional[str] = None      # only when UART != JTAG FTDI
    uart_baud: int = DEFAULT_BAUD
    uart_glob: str = "/dev/ttyUSB*"
    notes: Sequence[str] = field(default_factory=tuple)

    @property
    def uart_usb_serial(self) -> Optional[str]:
        """USB serial to match UART ports against (JTAG serial unless split)."""
        return self.uart_serial or self.jtag_serial


class Board:
    """Base board: UART discovery + JTAG programming, both by-serial."""

    SPEC: BoardSpec

    def __init__(self, spec: Optional[BoardSpec] = None):
        if spec is not None:
            self.SPEC = spec
        if not getattr(self, "SPEC", None):
            raise TypeError(f"{type(self).__name__} has no BoardSpec")

    # ---- identity ----------------------------------------------------------

    @property
    def name(self) -> str:
        return self.SPEC.name

    @property
    def jtag_serial(self) -> Optional[str]:
        """JTAG serial, honouring an env override.

        `FPGA_JTAG_SERIAL` is the ONE override name. The per-flow names
        (`RAPIDS_CHAR_JTAG_SERIAL`, `STREAM_CHAR_JTAG_SERIAL`) are still read so
        existing shell setups keep working, but new code should not add more.
        """
        for var in ("FPGA_JTAG_SERIAL", "STREAM_CHAR_JTAG_SERIAL",
                    "RAPIDS_CHAR_JTAG_SERIAL"):
            val = os.environ.get(var)
            if val:
                return val
        return self.SPEC.jtag_serial

    # ---- UART discovery ----------------------------------------------------

    def find_uart_ports(self) -> List[UartPort]:
        """Every serial port belonging to THIS board.

        Filtered by USB serial, so with two boards attached you get only yours.
        When the USB serial is unknown -- no pyserial, or an FTDI whose serial
        the kernel did not surface -- this cannot filter, and returns ALL
        candidates rather than an empty list: a probe can still sort them out,
        whereas an empty list would look like "board not attached".
        """
        ports = list_uart_ports(self.SPEC.uart_glob)
        # Use the env-AWARE serial. `SPEC.uart_usb_serial` falls back to the
        # spec's static jtag_serial, so an FPGA_JTAG_SERIAL override reached
        # programming but not port discovery: on a board whose serial differs
        # from the registry, `make program` worked and `make run` then reported
        # "no UART ports found" quoting the registry value the user had just
        # overridden. A board with its own uart_serial (Genesys 2's separate
        # FT232R) still wins, because that is not the JTAG serial at all.
        want = self.SPEC.uart_serial or self.jtag_serial
        if not want:
            return ports
        matched = [p for p in ports if p.matches_serial(want)]
        if matched:
            return matched
        if any(p.usb_serial for p in ports):
            return []      # serials ARE visible and none is ours: honest answer
        return ports       # no serials visible at all: cannot filter, don't lie

    def find_uart_port(self, probe: Optional[Probe] = None,
                       want: Optional[str] = None,
                       baudrate: Optional[int] = None,
                       timeout: float = 0.4,
                       label: Optional[str] = None) -> str:
        """The single port this board's harness answers on.

        Narrows to this board's ports by USB serial first, then applies the
        harness identity `probe`. Either alone is weaker: the serial filter
        cannot tell which bitstream is loaded, and the probe alone cannot tell
        two identically-programmed boards apart.
        """
        return find_port(
            probe=probe,
            want=want,
            candidates=self.find_uart_ports(),
            baudrate=baudrate or self.SPEC.uart_baud,
            timeout=timeout,
            label=label or f"{self.SPEC.display_name} harness",
            pattern=self.SPEC.uart_glob,
        )

    def open_link(self, port: Optional[str] = None,
                  probe: Optional[Probe] = None,
                  baudrate: Optional[int] = None,
                  timeout: float = 1.0) -> UartLink:
        """Open a `UartLink` to this board, resolving the port if not given."""
        resolved = port if (port and port != "auto") else self.find_uart_port(probe, want=port)
        return UartLink(resolved, baudrate or self.SPEC.uart_baud, timeout=timeout)

    def open_bridge(self, port: Optional[str] = None,
                    probe: Optional[Probe] = None,
                    baudrate: Optional[int] = None,
                    timeout: float = 1.0):
        """Open an AXI-over-UART bridge to this board (registers by address;
        wrap it in a `DeviceBus` for registers by name)."""
        return open_bridge(channel=self.open_link(port, probe, baudrate, timeout))

    # ---- programming -------------------------------------------------------

    def program_command(self, bitstream: str, vivado: str = "vivado") -> List[str]:
        """The exact command `program()` will run. Separated so it can be
        asserted in a test, and printed by `--dry-run`, without Vivado present."""
        return [vivado, "-mode", "batch", "-notrace", "-source", PROGRAM_TCL]

    def program_env(self, bitstream: str) -> dict:
        """Environment the programming tcl reads. The tcl is deliberately dumb:
        every board-specific fact is passed in from here."""
        env = dict(os.environ)
        env["FPGA_BITSTREAM"] = os.path.abspath(bitstream)
        if self.jtag_serial:
            env["FPGA_JTAG_SERIAL"] = self.jtag_serial
        env["FPGA_BOARD"] = self.SPEC.name
        return env

    def program(self, bitstream: str, vivado: str = "vivado",
                dry_run: bool = False, check: bool = True) -> int:
        """Program this board over JTAG with `bitstream`.

        Fails before launching Vivado if the bitstream is missing (a 30-second
        tool startup to be told the file is not there is pure waste) or if
        Vivado is not on PATH.
        """
        if not os.path.isfile(bitstream):
            raise FileNotFoundError(
                f"bitstream not found: {bitstream} -- run 'make bitstream' first")

        cmd = self.program_command(bitstream, vivado)
        env = self.program_env(bitstream)

        if dry_run:
            print("FPGA_BITSTREAM=" + env["FPGA_BITSTREAM"])
            print("FPGA_JTAG_SERIAL=" + env.get("FPGA_JTAG_SERIAL", "(any)"))
            print(" ".join(cmd))
            return 0

        if shutil.which(vivado) is None:
            raise FileNotFoundError(
                f"{vivado} not found on PATH -- source the Vivado settings script")

        print(f"[program] {self.SPEC.display_name} "
              f"(serial {self.jtag_serial or 'any'}) <- {bitstream}")
        proc = subprocess.run(cmd, env=env)
        if check and proc.returncode != 0:
            raise RuntimeError(f"programming failed (vivado exit {proc.returncode})")
        return proc.returncode

    # ---- misc --------------------------------------------------------------

    def describe(self) -> str:
        s = self.SPEC
        lines = [
            f"{s.display_name} ({s.name})",
            f"  part         {s.part}",
            f"  jtag serial  {self.jtag_serial or '(unset)'}",
            f"  uart serial  {s.uart_usb_serial or '(unknown)'}"
            + ("  [separate from JTAG]" if s.uart_serial else ""),
            f"  uart baud    {s.uart_baud}",
        ]
        lines += [f"  note         {n}" for n in s.notes]
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"<{type(self).__name__} {self.SPEC.name}>"
