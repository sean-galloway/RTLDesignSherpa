#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for the ALU harness (alu_genesys2_top / alu_harness).

Wraps `UARTAxiBridge` (projects/fpga-systems/bin, the shared board+UART layer)
with by-name register access via `UartRegisterMap`, backed by the
PeakRDL-generated `alu_harness_regs_regmap.py`. No offsets live here.

The bridge is INJECTABLE: the identical driver runs the board over pyserial
or a cocotb sim over `make_uart_channel` (dv/tests/test_alu_harness_uart.py).

    from alu_harness import AluHarness, Cmd
    h = AluHarness(port="/dev/ttyUSB0")
    h.load([Cmd(a=0x3F803F80, b=0x40004000, func_sel=1)])
    r = h.run(1)
    r.results[0].line
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass, field
from typing import List, Optional

_REPO_ROOT = os.environ.get("REPO_ROOT")
if not _REPO_ROOT:
    raise RuntimeError("REPO_ROOT is not set. Source RTLDesignSherpa/env_python first.")
_FPGA_BIN = os.path.join(_REPO_ROOT, "projects/fpga-systems/bin")
if _FPGA_BIN not in sys.path:
    sys.path.insert(0, _FPGA_BIN)

from uart_axi_bridge import UARTAxiBridge                          # noqa: E402
from uart_link import find_port                                    # noqa: E402
from TBClasses.harness.uart_register_map import UartRegisterMap    # noqa: E402

HARNESS_BASE = 0x0
REGMAP = os.path.join(
    _REPO_ROOT, "projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/dv/tbclasses/"
    "alu_harness_regs_regmap.py")

BUILD_ID = 0x414C_5548          # "ALUH"
SLOT_ALU_INFER = 1

STALL_NONE, STALL_RANDOM, STALL_FILL = 0, 1, 2

EN_BITS = ("int8", "fp32", "fp8", "reduce", "pwl", "act", "cvt")


@dataclass(frozen=True)
class Cmd:
    """One invocation at the ALU's issue seam."""
    a: int = 0
    b: int = 0
    imm: int = 0
    func_sel: int = 0
    acc_ctrl: int = 0


@dataclass(frozen=True)
class Result:
    line: int
    flags: int
    issue: int          # cycle of the issue edge, after START
    retire: int         # cycle of the retire edge
    err: bool           # err_opcode pulsed at this invocation's issue

    @property
    def latency(self) -> int:
        """Cycles from the issue edge to the first cycle the result could be
        taken: 0 for a row that lands at the issue edge (offered next cycle)."""
        return self.retire - self.issue - 1


@dataclass
class RunResult:
    count: int
    stall_mode: int
    cycles: int
    stall_cycles: int
    err_count: int
    issued: int
    retired: int
    done: bool
    results: List[Result] = field(default_factory=list)


def func_sel(opcode: int, sub_op: int = 0, fmt: int = 0) -> int:
    return ((fmt & 3) << 7) | ((sub_op & 3) << 5) | (opcode & 0x1F)


class AluHarness:
    """By-name driver for alu_harness_regs."""

    def __init__(self, port: Optional[str] = None, baudrate: int = 115200,
                 bridge: Optional[UARTAxiBridge] = None, timeout: float = 1.0):
        if bridge is None:
            if port is None or port == "auto":
                port = find_port()
            bridge = UARTAxiBridge(port=port, baudrate=baudrate, timeout=timeout)
        self.bridge = bridge
        self.regs = UartRegisterMap(bridge, start_address=HARNESS_BASE, regmap_file=REGMAP)
        self._slot = None

    # ---- identity -----------------------------------------------------------

    def build_id(self) -> int:
        return self.regs.read("BUILD_ID")

    def scratch_check(self, patterns=(0xA5A5_5A5A, 0x0123_4567, 0xFFFF_0000)) -> list:
        out = []
        for p in patterns:
            self.regs.write("SCRATCH", value=p)
            r = self.regs.read("SCRATCH")
            out.append((p, r, r == p))
        return out

    def slot_info(self) -> dict:
        if self._slot is None:
            w = self.regs.read("SLOT_INFO")
            f = lambda name: self.regs.field("SLOT_INFO", name, w)  # noqa: E731
            en = f("en")
            self._slot = {
                "kind": f("kind"),
                "en": {n: bool((en >> i) & 1) for i, n in enumerate(EN_BITS)},
                "add_lat": f("add_lat"), "mul_lat": f("mul_lat"), "mac_lat": f("mac_lat"),
                "pipe_depth": f("pipe_depth"),
            }
            g = self.regs.read("GEOMETRY")
            self._slot["depth"] = self.regs.field("GEOMETRY", "depth", g)
            self._slot["clk_mhz"] = self.regs.field("GEOMETRY", "clk_mhz", g)
        return self._slot

    # ---- commands and runs --------------------------------------------------

    def load(self, cmds: List[Cmd], base: int = 0) -> None:
        """Write commands into the command RAM. CMD_CTL's write commits the
        entry, so A and B go first."""
        depth = self.slot_info()["depth"]
        if base + len(cmds) > depth:
            raise ValueError(f"{len(cmds)} commands at {base} exceed the {depth}-entry RAM")
        for i, c in enumerate(cmds):
            self.regs.write("CMD_INDEX", index=base + i)
            self.regs.write("CMD_A", value=c.a & 0xFFFF_FFFF)
            self.regs.write("CMD_B", value=c.b & 0xFFFF_FFFF)
            self.regs.write("CMD_CTL", imm=c.imm & 0xFFFF, func_sel=c.func_sel & 0x1FF,
                            acc_ctrl=c.acc_ctrl & 3)

    def run(self, count: int, stall_mode: int = STALL_NONE, timeout_s: float = 5.0,
            read_results: bool = True) -> RunResult:
        """Issue commands 0..count-1 back to back and collect every result."""
        self.regs.write("CTRL", clear=1, stall_mode=stall_mode)
        self.regs.write("RUN_COUNT", n=count)
        self.regs.write("CTRL", start=1, stall_mode=stall_mode)
        t0 = time.time()
        while True:
            st = self.regs.read("STATUS")
            if not self.regs.field("STATUS", "busy", st):
                break
            if time.time() - t0 > timeout_s:
                break
        rr = RunResult(
            count=count, stall_mode=stall_mode,
            cycles=self.regs.read("CYCLES"),
            stall_cycles=self.regs.read("STALL_CYCLES"),
            err_count=self.regs.read("ERR_COUNT"),
            issued=self.regs.field("STATUS", "issued", st),
            retired=self.regs.read("RETIRED"),
            done=bool(self.regs.field("STATUS", "done", st)))
        if read_results:
            rr.results = [self.result(i) for i in range(min(count, rr.retired))]
        return rr

    def result(self, index: int) -> Result:
        self.regs.write("CMD_INDEX", index=index)
        t = self.regs.read("RES_TIME")
        return Result(line=self.regs.read("RES_LINE"),
                      flags=self.regs.read("RES_FLAGS"),
                      issue=self.regs.field("RES_TIME", "issue", t),
                      retire=self.regs.field("RES_TIME", "retire", t),
                      err=bool(self.regs.field("RES_STATUS", "err", self.regs.read("RES_STATUS"))))
