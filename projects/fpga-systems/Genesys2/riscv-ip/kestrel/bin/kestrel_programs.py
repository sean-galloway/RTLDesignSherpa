#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host programs for kestrel on the Genesys 2, authored ONCE.

The board host (build-bram/host/host_kestrel.py) and the cocotb UART sim
(dv/tests/test_kestrel_board_uart.py) run these same functions; only the
bridge's transport differs.

  smoke    BUILD_ID, memory write/read with byte strobes, load-mode status
  battery  the riscv-tests rv32ui-p images (vendor/riscv-tests/isa): load,
           run to halt, verdict = halted on ecall with gp == 1 (the core
           halts on the final ecall, so the tohost store never runs -- the
           same rule as the DV battery), or the DV battery's expected halt
           (ma_data: cause 4, the misaligned-load halt)
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from kestrel_board import KestrelBoard, BUILD_ID, Status

_KESTREL_DV = os.path.join(os.environ["REPO_ROOT"], "projects/components/riscv-ip/kestrel-rv32i/dv")
for _p in (_KESTREL_DV, os.path.join(_KESTREL_DV, "tests/programs")):
    if _p not in sys.path:
        sys.path.insert(0, _p)
from tbclasses.kestrel.rv32ui_battery import (  # noqa: E402
    EXPECTED_HALTS, discover_tests, normalize_image)


@dataclass
class Report:
    name: str
    failures: List[str] = field(default_factory=list)
    numbers: Dict[str, float] = field(default_factory=dict)
    rows: List[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.failures

    def line(self) -> str:
        nums = " ".join(f"{k}={v}" for k, v in self.numbers.items())
        return f"{self.name:10} {'PASS' if self.ok else f'FAIL ({len(self.failures)})':10} {nums}"


def smoke(k: KestrelBoard) -> Report:
    r = Report("smoke")
    bid = k.build_id()
    if bid != BUILD_ID:
        r.failures.append(f"BUILD_ID 0x{bid:08X}, expected 0x{BUILD_ID:08X}")
    k.stop()
    for addr, val in ((0x100, 0xAABB_CCDD), (0x1_0100, 0x1234_5678)):
        k.write(addr, val)
        got = k.read_word(addr)
        if got != val:
            r.failures.append(f"mem 0x{addr:05X}: wrote 0x{val:08X} read 0x{got:08X}")
    # Load mode is run = 0. halted/cause keep the previous run's verdict
    # until the next run starts (kestrel_mem_bram clears them on run 0 -> 1).
    st = k.status()
    if st.run:
        r.failures.append(f"not in load mode after stop: {st}")
    return r


def run_image(k: KestrelBoard, words: Dict[int, int], timeout_s: float = 5.0) -> Status:
    k.stop()
    k.load(words)
    return k.run_to_halt(timeout_s)


def battery(k: KestrelBoard, tests: Optional[List[str]] = None) -> Report:
    r = Report("battery")
    repo = os.environ["REPO_ROOT"]
    names = tests or discover_tests(repo)
    cycles = instret = 0
    for name in names:
        st = run_image(k, normalize_image(repo, name))
        cycles += st.cycles
        instret += st.instret
        expected = EXPECTED_HALTS.get(name)
        ok = (st.halted and st.cause == expected[0]) if expected else st.riscv_tests_pass
        r.rows.append(f"{name:8} {'PASS' if ok else 'FAIL'} cause={st.cause} "
                      f"gp=0x{st.gp:08X} instret={st.instret} cycles={st.cycles} cpi={st.cpi:.2f}")
        if not ok:
            r.failures.append(f"{name}: halted={st.halted} cause={st.cause} gp=0x{st.gp:08X}")
    r.numbers.update(tests=len(names), passed=len(names) - len(r.failures),
                     cpi=round(cycles / instret, 3) if instret else 0)
    return r


PROGRAMS = {"smoke": smoke, "battery": battery}
