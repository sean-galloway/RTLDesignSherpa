#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generic host-side UART link + port discovery for FPGA characterization boards.

This is the layer BELOW the existing transport spine
(`bin/TBClasses/harness/`), which had no port/board layer at all -- so every
flow grew its own `autodetect_port()` that globbed `/dev/ttyUSB*` and probed a
flow-specific identity register. Four near-identical copies existed (stream,
rapids, cdc, ddr2/pumice). This module is the one implementation they collapse
into.

Three pieces:

  * `UartPort`      one enumerated candidate, with the USB metadata that says
                    WHICH BOARD it belongs to (see `matches_serial`).
  * `UartLink`      a `ByteChannel`-compatible pyserial client. Because it
                    satisfies the same protocol as
                    `TBClasses.harness.byte_channel.SerialChannel`, it drops
                    straight into `UARTAxiBridge(channel=...)` -- the sim/silicon
                    equivalence boundary is untouched.
  * `find_port`     the generic probe loop: walk candidates, hand each to a
                    caller-supplied predicate, return the first that answers.

The probe stays a caller concern because each harness identifies itself
differently (a SCRATCH round-trip, a BUILD_ID magic, a CSR_ID magic).
`register_probe` / `scratch_probe` build the two shapes that actually occur.

    from uart_link import find_port, register_probe
    port = find_port(register_probe(addr=0x1_0000, magic=0x44445232),
                     want=args.port, label="pumice DDR2 char harness")
"""

from __future__ import annotations

import glob
import os
import re
from dataclasses import dataclass
from typing import Callable, Iterable, List, Optional, Sequence

DEFAULT_BAUD = 115200
DEFAULT_GLOB = "/dev/ttyUSB*"

# A probe is handed an OPEN UartLink and answers "is this the board I want?".
# It must not raise on a wrong-but-healthy board; returning False is enough.
Probe = Callable[["UartLink"], bool]


def _normalize_serial(serial: Optional[str]) -> str:
    """Upper-case, strip punctuation. USB serials are compared loosely because
    the same physical board is reported slightly differently by different
    layers (see `UartPort.matches_serial`)."""
    if not serial:
        return ""
    return re.sub(r"[^0-9A-Za-z]", "", serial).upper()


@dataclass(frozen=True)
class UartPort:
    """One candidate serial device plus the USB identity behind it.

    `usb_serial` is the interesting field: on a Digilent board the USB-UART and
    the JTAG interface sit on the SAME FTDI part, so the USB serial number and
    the Vivado JTAG target serial are the same string (give or take an interface
    suffix). That is what lets `Board.find_uart_ports()` return only the ports
    belonging to the board you are about to program -- the problem the flows
    previously handled with a comment telling you to keep them straight.
    """

    device: str
    usb_serial: Optional[str] = None
    vid: Optional[int] = None
    pid: Optional[int] = None
    description: Optional[str] = None
    manufacturer: Optional[str] = None
    location: Optional[str] = None

    def matches_serial(self, serial: Optional[str]) -> bool:
        """Does this port belong to the board with USB/JTAG serial `serial`?

        Compared with prefix tolerance in BOTH directions: an FT2232 exposes one
        EEPROM serial across its interfaces, but the tooling on either side may
        or may not append the interface letter ('...D46F' vs '...D46FB'). An
        exact-match test silently finds nothing on some hosts, which reads as
        "board not attached" -- the failure this tolerance exists to avoid.
        """
        want = _normalize_serial(serial)
        have = _normalize_serial(self.usb_serial)
        if not want or not have:
            return False
        return have.startswith(want) or want.startswith(have)

    def __str__(self) -> str:
        bits = [self.device]
        if self.usb_serial:
            bits.append(f"serial={self.usb_serial}")
        if self.description:
            bits.append(self.description)
        return " ".join(bits)


def list_uart_ports(pattern: str = DEFAULT_GLOB,
                    include_all: bool = False) -> List[UartPort]:
    """Enumerate candidate UART devices, richest source first.

    Prefers `serial.tools.list_ports` because it carries the USB serial number
    (without which a board cannot be told from its neighbour on a shared JTAG
    chain). Falls back to a bare glob when pyserial is absent or reports
    nothing, so board-less callers and minimal environments still work -- that
    glob is exactly what the per-flow copies did, so nothing regresses.

    `pattern` filters the device path (default `/dev/ttyUSB*`); pass
    `include_all=True` to keep every port pyserial reports (e.g. `/dev/ttyACM*`
    boards).
    """
    ports: List[UartPort] = []
    try:
        from serial.tools import list_ports  # lazy: pyserial is optional here
    except ImportError:
        list_ports = None

    if list_ports is not None:
        for info in list_ports.comports():
            ports.append(UartPort(
                device=info.device,
                usb_serial=getattr(info, "serial_number", None),
                vid=getattr(info, "vid", None),
                pid=getattr(info, "pid", None),
                description=getattr(info, "description", None),
                manufacturer=getattr(info, "manufacturer", None),
                location=getattr(info, "location", None),
            ))

    known = {p.device for p in ports}
    for dev in sorted(glob.glob(pattern)):
        if dev not in known:
            ports.append(UartPort(device=dev))

    if not include_all and pattern:
        import fnmatch
        ports = [p for p in ports if fnmatch.fnmatch(p.device, pattern)]

    return sorted(ports, key=lambda p: p.device)


class UartLink:
    """A host UART client that is also a `ByteChannel`.

    Satisfies the write / read_until / reset_input_buffer / reset_output_buffer
    / close / is_open protocol that `UARTAxiBridge` needs, so it can be injected
    directly: `UARTAxiBridge(channel=link)`. Opening is lazy-imported so a
    machine without pyserial can still import this module (the sim path and the
    unit tests never touch a real port).
    """

    def __init__(self, port: str, baudrate: int = DEFAULT_BAUD,
                 timeout: float = 1.0, settle: float = 0.1):
        import serial  # lazy: only the silicon path needs pyserial
        self.port = port
        self.baudrate = baudrate
        self.timeout = timeout
        self._ser = serial.Serial(port, baudrate, timeout=timeout)
        if settle:
            import time
            time.sleep(settle)  # let the USB-UART settle before the first frame
        self._ser.reset_input_buffer()
        self._ser.reset_output_buffer()

    # ---- ByteChannel protocol ---------------------------------------------

    def write(self, data: bytes) -> int:
        return self._ser.write(data)

    def read_until(self, expected: bytes = b"\n",
                   size: Optional[int] = None) -> bytes:
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

    # ---- Convenience -------------------------------------------------------

    def bridge(self):
        """An AXI-over-UART bridge speaking the repo's ASCII W/R protocol over
        this link. Imported lazily so `uart_link` stays free of the converters
        path hack when a caller only wants port discovery."""
        return open_bridge(channel=self)

    def __enter__(self) -> "UartLink":
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self.close()

    def __repr__(self) -> str:
        return f"UartLink({self.port!r}, baudrate={self.baudrate})"


def _converters_bin() -> str:
    """Directory holding `uart_axi_bridge.py`.

    The bridge lives with the converter RTL it talks to
    (`projects/components/converters/bin`), which is not on PYTHONPATH. Every
    host tool used to re-derive this by hand -- via `$REPO_ROOT` or a 12-deep
    parent walk. Derived here once instead, from this file's own location, so it
    works with or without the environment being sourced.
    """
    env = os.environ.get("REPO_ROOT")
    if env:
        cand = os.path.join(env, "projects/components/converters/bin")
        if os.path.isdir(cand):
            return cand
    # fpga/bin/uart_link.py -> repo root is two levels up.
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    return os.path.join(root, "projects/components/converters/bin")


def open_bridge(port: Optional[str] = None, baudrate: int = DEFAULT_BAUD,
                timeout: float = 1.0, channel=None):
    """Build a `UARTAxiBridge` over a port (or an injected channel).

    One place that knows where the bridge module lives; callers just ask for a
    bridge. Passing `channel=` (a `UartLink`, or a cocotb channel) keeps the
    sim/silicon equivalence boundary exactly where it was.
    """
    import sys
    bin_dir = _converters_bin()
    if bin_dir not in sys.path:
        sys.path.insert(0, bin_dir)
    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    if channel is not None:
        return UARTAxiBridge(channel=channel)
    return UARTAxiBridge(port=port, baudrate=baudrate, timeout=timeout)


# ---------------------------------------------------------------------------
# Probes -- how a board says "yes, I am the one you want"
# ---------------------------------------------------------------------------

def register_probe(addr: int, magic: int) -> Probe:
    """Probe that reads one register and compares it to an identity magic.

    The shape used by the rapids (CSR_ID='RAP1'), cdc (BUILD_ID='CDC1') and
    pumice (BUILD_ID='DDR2') harnesses. Read-only, so it is safe to point at a
    board running someone else's bitstream.
    """
    def probe(link: UartLink) -> bool:
        return open_bridge(channel=link).read(addr) == magic
    return probe


def scratch_probe(addr: int, magic: int = 0xC0FFEE5A) -> Probe:
    """Probe that round-trips a RW scratch register and then restores it.

    The shape used by the stream char harness, for harnesses whose identity
    register is a plain scratchpad rather than a build-ID constant. Leaves no
    footprint: the scratch is zeroed again on a match.
    """
    def probe(link: UartLink) -> bool:
        bridge = open_bridge(channel=link)
        bridge.write(addr, magic)
        if bridge.read(addr) != magic:
            return False
        try:
            bridge.write(addr, 0)
        except Exception:  # noqa: BLE001 - restoring is best-effort
            pass
        return True
    return probe


def find_port(probe: Optional[Probe] = None,
              want: Optional[str] = None,
              candidates: Optional[Sequence] = None,
              baudrate: int = DEFAULT_BAUD,
              timeout: float = 0.4,
              label: str = "harness",
              pattern: str = DEFAULT_GLOB,
              verbose: bool = True) -> str:
    """Resolve the serial port a given harness is on.

    The USB-UART re-enumerates across reboots and replugs, so the ttyUSB index
    is not stable and must never be hardcoded. Each candidate is opened and
    handed to `probe`; the first that answers True wins.

    `want`   an explicit `--port` from the caller. Tried FIRST but still probed,
             so a stale path in a script fails loudly instead of driving the
             wrong board. The string "auto" means "no preference".
    `probe`  None means "take the first port that opens" -- only sensible when
             exactly one board is attached.

    Raises SystemExit with the candidate list when nothing answers, because
    every caller of this is a CLI and a traceback helps nobody.
    """
    if candidates is None:
        cands = [p.device for p in list_uart_ports(pattern)]
    else:
        cands = [c.device if isinstance(c, UartPort) else str(c) for c in candidates]

    ordered: List[str] = []
    if want and want != "auto":
        ordered.append(want)
    ordered += [c for c in cands if c not in ordered]

    for port in ordered:
        try:
            with UartLink(port, baudrate, timeout=timeout) as link:
                if probe is None or probe(link):
                    if verbose:
                        print(f"[autodetect] {label} found on {port}")
                    return port
        except Exception:  # noqa: BLE001 - a busy/absent/foreign port is just a miss
            continue

    raise SystemExit(
        f"[autodetect] no {label} responded on any of: "
        f"{ordered or f'(no {pattern} present)'}. "
        f"Is the board powered and programmed with the right bitstream?")


def _cli() -> int:
    """`python3 uart_link.py` -- list what is attached, with USB serials."""
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--pattern", default=DEFAULT_GLOB)
    ap.add_argument("--all", action="store_true",
                    help="list every port pyserial reports, not just --pattern")
    args = ap.parse_args()

    ports = list_uart_ports(args.pattern, include_all=args.all)
    if not ports:
        print(f"no serial ports matching {args.pattern}")
        return 1
    for p in ports:
        print(f"  {p}")
    return 0


if __name__ == "__main__":
    raise SystemExit(_cli())
