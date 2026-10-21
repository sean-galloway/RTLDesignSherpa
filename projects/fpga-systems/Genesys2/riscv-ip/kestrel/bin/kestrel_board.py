#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for kestrel on the Genesys 2 (kestrel_genesys2_top).

Wraps `UARTAxiBridge` (projects/fpga-systems/bin) around kestrel_mem_bram's
AXIL map. The register names below mirror the map in the RTL header
(projects/components/riscv-ip/kestrel-rv32i/rtl/fub/kestrel_mem_bram.sv) --
the one place an offset is written down on the host side.

The bridge is INJECTABLE: the same driver runs the board over pyserial or a
cocotb sim over make_uart_channel (dv/tests/test_kestrel_board_uart.py).
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass
from typing import Dict, Optional

_REPO_ROOT = os.environ.get("REPO_ROOT")
if not _REPO_ROOT:
    raise RuntimeError("REPO_ROOT is not set. Source RTLDesignSherpa/env_python first.")
_FPGA_BIN = os.path.join(_REPO_ROOT, "projects/fpga-systems/bin")
if _FPGA_BIN not in sys.path:
    sys.path.insert(0, _FPGA_BIN)

from uart_axi_bridge import UARTAxiBridge    # noqa: E402
from uart_link import find_port              # noqa: E402

# kestrel_mem_bram AXIL map: addr[17] = 1 selects the registers.
REGS = {
    "CTRL":     0x2_0000,   # W bit0 run; R {cause[7:4], halted[1], run[0]}
    "CYCLES":   0x2_0004,
    "INSTRET":  0x2_0008,
    "GP":       0x2_000C,   # last value written to x3: the riscv-tests verdict
    "BUILD_ID": 0x2_0010,
}
BUILD_ID = 0x4B42_524D       # "KBRM"
MEM_BYTES = 0x4000           # kestrel_mem_bram default: unified 16 KB, aliased above
CAUSE_ECALL = 1


@dataclass(frozen=True)
class Status:
    run: bool
    halted: bool
    cause: int
    cycles: int
    instret: int
    gp: int

    @property
    def cpi(self) -> float:
        return self.cycles / self.instret if self.instret else 0.0

    @property
    def riscv_tests_pass(self) -> bool:
        """riscv-tests verdict: halted on the final ecall with gp == 1."""
        return self.halted and self.cause == CAUSE_ECALL and self.gp == 1


class KestrelBoard:
    """kestrel_mem_bram over UART: load, run, status."""

    def __init__(self, port: Optional[str] = None, baudrate: int = 115200,
                 bridge: Optional[UARTAxiBridge] = None, timeout: float = 1.0):
        if bridge is None:
            if port is None or port == "auto":
                port = find_port()
            bridge = UARTAxiBridge(port=port, baudrate=baudrate, timeout=timeout)
        self.bridge = bridge

    def reg(self, name: str) -> int:
        return self.bridge.read(REGS[name])

    def build_id(self) -> int:
        return self.reg("BUILD_ID")

    def stop(self) -> None:
        """Back to load mode: the core is held in reset."""
        self.bridge.write(REGS["CTRL"], 0)

    def load(self, words: Dict[int, int]) -> None:
        """Write an image of {word_address: word} (full addresses; the memory
        decodes the low 17 bits). Only legal in load mode."""
        for idx, w in sorted(words.items()):
            self.bridge.write((idx << 2) % MEM_BYTES, w & 0xFFFF_FFFF)

    def read_word(self, byte_addr: int) -> int:
        return self.bridge.read(byte_addr % MEM_BYTES)

    def run(self) -> None:
        self.bridge.write(REGS["CTRL"], 1)

    def status(self) -> Status:
        c = self.reg("CTRL")
        return Status(run=bool(c & 1), halted=bool(c & 2), cause=(c >> 4) & 0xF,
                      cycles=self.reg("CYCLES"), instret=self.reg("INSTRET"),
                      gp=self.reg("GP"))

    def run_to_halt(self, timeout_s: float = 5.0) -> Status:
        self.run()
        t0 = time.time()
        while True:
            st = self.status()
            if st.halted or time.time() - t0 > timeout_s:
                return st
