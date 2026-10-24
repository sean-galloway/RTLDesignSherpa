#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for gatling on the Nexys A7 (gatling_nexysa7_top).

Wraps `UARTAxiBridge` (projects/fpga-systems/bin) around gatling_mem_bram's
AXIL map. The offsets below mirror the map in the RTL header
(projects/components/riscv-ip/gatling-rv32i/rtl/fub/gatling_mem_bram.sv)
-- the one place an offset is written down on the host side.

The bridge is INJECTABLE: the same driver runs the board over pyserial or a
cocotb sim over make_uart_channel (dv/tests/test_gatling_board_uart.py).
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass
from typing import Dict, Iterable, Optional

_REPO_ROOT = os.environ.get("REPO_ROOT")
if not _REPO_ROOT:
    raise RuntimeError("REPO_ROOT is not set. Source RTLDesignSherpa/env_python first.")
_FPGA_BIN = os.path.join(_REPO_ROOT, "projects/fpga-systems/bin")
if _FPGA_BIN not in sys.path:
    sys.path.insert(0, _FPGA_BIN)

from uart_axi_bridge import UARTAxiBridge    # noqa: E402
from uart_link import find_port              # noqa: E402

NUM_HARTS = 4
ALL_HARTS = (1 << NUM_HARTS) - 1

# gatling_mem_bram AXIL map: addr[17] = 1 selects the registers.
REG_CTRL = 0x2_0000          # W bits[3:0] run per hart; R {halted[7:4], run[3:0]}
REG_BUILD_ID = 0x2_0004
HART_REGS = {"STATUS": 0x0, "CYCLES": 0x4, "INSTRET": 0x8, "GP": 0xC}
BUILD_ID = 0x4741_544C       # "GATL"
BANK_SHIFT = 14              # addr[15:14] = hart bank
BANK_BYTES = 1 << BANK_SHIFT # 16 KB per hart, aliased above
CAUSE_ECALL = 1


def hart_reg(hart: int, name: str) -> int:
    return 0x2_0100 + 0x10 * hart + HART_REGS[name]


def mem_addr(hart: int, byte_addr: int) -> int:
    """AXIL address of a byte address in ``hart``'s bank."""
    return (hart << BANK_SHIFT) | (byte_addr % BANK_BYTES)


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


class GatlingBoard:
    """gatling_mem_bram over UART: per-hart load, run, status."""

    def __init__(self, port: Optional[str] = None, baudrate: int = 115200,
                 bridge: Optional[UARTAxiBridge] = None, timeout: float = 1.0):
        if bridge is None:
            if port is None or port == "auto":
                port = find_port()
            bridge = UARTAxiBridge(port=port, baudrate=baudrate, timeout=timeout)
        self.bridge = bridge

    def read(self, addr: int) -> int:
        return self.bridge.read(addr)

    def write(self, addr: int, data: int) -> None:
        """One acked write. UARTAxiBridge.write returns False when no "OK"
        arrives within its timeout; carrying on would let a late "OK" answer
        the next read, so a lost ack stops here, naming the command."""
        if not self.bridge.write(addr, data):
            raise IOError(f"UART write W {addr:08X} {data:08X}: no OK ack")

    def build_id(self) -> int:
        return self.read(REG_BUILD_ID)

    def run_mask(self) -> int:
        return self.read(REG_CTRL) & ALL_HARTS

    def set_run(self, mask: int) -> None:
        """CTRL: bit h = 1 runs hart h, 0 holds it at RESET_ADDR."""
        self.write(REG_CTRL, mask & ALL_HARTS)

    def stop(self, harts: Iterable[int] = range(NUM_HARTS)) -> None:
        mask = self.run_mask()
        for h in harts:
            mask &= ~(1 << h)
        self.set_run(mask)

    def load(self, hart: int, words: Dict[int, int]) -> None:
        """Write an image of {word_address: word} into ``hart``'s bank (full
        addresses; the bank decodes the low 14 bits). The hart must be
        stopped: writes to a running hart's bank are dropped."""
        for idx, w in sorted(words.items()):
            self.write(mem_addr(hart, idx << 2), w & 0xFFFF_FFFF)

    def read_word(self, hart: int, byte_addr: int) -> int:
        return self.read(mem_addr(hart, byte_addr))

    def status(self, hart: int) -> Status:
        c = self.read(hart_reg(hart, "STATUS"))
        return Status(run=bool(c & 1), halted=bool(c & 2), cause=(c >> 4) & 0xF,
                      cycles=self.read(hart_reg(hart, "CYCLES")),
                      instret=self.read(hart_reg(hart, "INSTRET")),
                      gp=self.read(hart_reg(hart, "GP")))

    def run_to_halt(self, harts: Iterable[int], timeout_s: float = 5.0) -> Dict[int, Status]:
        """Start ``harts`` together (one CTRL write) and poll until every one
        has halted or the timeout passes; returns each hart's status."""
        harts = list(harts)
        mask = 0
        for h in harts:
            mask |= 1 << h
        self.set_run(self.run_mask() | mask)
        t0 = time.time()
        while True:
            halted = (self.read(REG_CTRL) >> 4) & ALL_HARTS
            if (halted & mask) == mask or time.time() - t0 > timeout_s:
                return {h: self.status(h) for h in harts}
