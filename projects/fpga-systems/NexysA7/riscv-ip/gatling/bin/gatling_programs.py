#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host programs for gatling on the Nexys A7, authored ONCE.

The board host (build-bram/host/host_gatling.py) and the cocotb UART sim
(dv/tests/test_gatling_board_uart.py) run these same functions; only the
bridge's transport differs.

  smoke    BUILD_ID; every hart's bank written and read back distinct at the
           same offset; a running hart's bank refuses writes (a hart parked
           on `j .` keeps its word) while reads are still served
  battery  the riscv-tests rv32ui-p images (vendor/riscv-tests/isa), four
           DIFFERENT images on the four harts at once, rotated so every hart
           runs every image; verdict per (hart, image) = halted on ecall with
           gp == 1, or the DV battery's expected halt (ma_data: cause 4)
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from gatling_board import ALL_HARTS, BUILD_ID, NUM_HARTS, GatlingBoard

_KESTREL_DV = os.path.join(os.environ["REPO_ROOT"], "projects/components/riscv-ip/kestrel-rv32i/dv")
for _p in (_KESTREL_DV, os.path.join(_KESTREL_DV, "tests/programs")):
    if _p not in sys.path:
        sys.path.insert(0, _p)
from tbclasses.kestrel.rv32ui_battery import (  # noqa: E402
    EXPECTED_HALTS, LINK_BASE, discover_tests, normalize_image)

J_SELF = 0x0000_006F          # jal x0, 0: a hart parked in place


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


def smoke(k: GatlingBoard) -> Report:
    r = Report("smoke")
    bid = k.build_id()
    if bid != BUILD_ID:
        r.failures.append(f"BUILD_ID 0x{bid:08X}, expected 0x{BUILD_ID:08X}")
    k.set_run(0)
    for h in range(NUM_HARTS):
        k.write((h << 14) | 0x100, 0xA000_0000 | (h << 16) | 0xBEEF)
    for h in range(NUM_HARTS):
        got = k.read_word(h, 0x100)
        want = 0xA000_0000 | (h << 16) | 0xBEEF
        if got != want:
            r.failures.append(f"hart {h} bank 0x100: read 0x{got:08X}, wrote 0x{want:08X}")
    if k.run_mask() != 0:
        r.failures.append(f"CTRL run mask 0x{k.run_mask():X} after stop")

    # Write protection: park hart 0 on `j .` at the link base, run it, try
    # to overwrite that word, read it back, stop it.
    entry = LINK_BASE % (1 << 14)
    k.write((0 << 14) | entry, J_SELF)
    k.set_run(0b0001)
    k.write((0 << 14) | entry, 0xDEAD_BEEF)
    got = k.read_word(0, entry)
    k.set_run(0)
    if got != J_SELF:
        r.failures.append(f"running hart 0's bank took a write: read 0x{got:08X}")
    return r


def battery(k: GatlingBoard, tests: Optional[List[str]] = None) -> Report:
    r = Report("battery")
    repo = os.environ["REPO_ROOT"]
    names = tests or discover_tests(repo)
    n = len(names)
    images = {name: normalize_image(repo, name) for name in names}
    runs = passed = 0
    sum_instret = sum_round_cycles = 0
    hart_cycles = [0] * NUM_HARTS
    hart_instret = [0] * NUM_HARTS
    for rnd in range(n):
        plan = [names[(rnd + h) % n] for h in range(NUM_HARTS)]
        k.set_run(0)
        for h, name in enumerate(plan):
            k.load(h, images[name])
        statuses = k.run_to_halt(range(NUM_HARTS))
        k.set_run(0)
        round_cycles = 0
        for h, name in enumerate(plan):
            st = statuses[h]
            runs += 1
            expected = EXPECTED_HALTS.get(name)
            ok = (st.halted and st.cause == expected[0]) if expected else st.riscv_tests_pass
            passed += ok
            sum_instret += st.instret
            hart_cycles[h] += st.cycles
            hart_instret[h] += st.instret
            round_cycles = max(round_cycles, st.cycles)
            r.rows.append(f"round {rnd:2} hart {h} {name:8} {'PASS' if ok else 'FAIL'} "
                          f"cause={st.cause} gp=0x{st.gp:08X} instret={st.instret} "
                          f"cycles={st.cycles} cpi={st.cpi:.2f}")
            if not ok:
                r.failures.append(f"round {rnd} hart {h} {name}: halted={st.halted} "
                                  f"cause={st.cause} gp=0x{st.gp:08X}")
        sum_round_cycles += round_cycles
    cpi = [round(c / i, 3) if i else 0 for c, i in zip(hart_cycles, hart_instret)]
    r.numbers.update(images=n, runs=runs, passed=passed,
                     cpi_per_hart="/".join(f"{c}" for c in cpi),
                     ipc_aggregate=round(sum_instret / sum_round_cycles, 3) if sum_round_cycles else 0)
    return r


PROGRAMS = {"smoke": smoke, "battery": battery}
