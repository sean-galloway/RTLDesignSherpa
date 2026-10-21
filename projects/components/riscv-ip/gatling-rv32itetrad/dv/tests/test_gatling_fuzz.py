# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_fuzz
# Purpose: Constrained-random RV32I streams (kestrel's CORE-17 generator),
#          four different streams on the four gatling contexts at once, every
#          stream diffed against the golden interpreter and spike.
#
# Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32itetrad
#
# Created: 2026-10-21

"""gatling fuzz battery.

kestrel's fuzz_gen builds the streams (same constraints, same seed rules:
gate = the committed five-seed corpus, func/full = 25/200 seeds derived from
SEED, so SEED reproduces a failing stream).  Each round puts four DIFFERENT
streams on the four contexts -- random programs interleaved instruction by
instruction are the strongest isolation check the barrel has -- and every
stream is checked by both goldens at every level.
"""

import logging
import os
import random
import shutil
from pathlib import Path

import cocotb
import pytest

import gatling_sim
from TBClasses.shared.test_levels import reg_level_grid

from gatling.gatling_battery import GatlingBattery                 # noqa: E402
from tbclasses.kestrel import fuzz_gen                              # noqa: E402
from tbclasses.kestrel.rv32i_interpreter import load_verilog_hex   # noqa: E402
from tbclasses.kestrel.rv32ui_battery import LINK_BASE             # noqa: E402

LOG = logging.getLogger("gatling_fuzz")


class FuzzBattery(GatlingBattery):
    """GatlingBattery fed by generated streams instead of vendor images."""

    title = "gatling fuzz"
    lockstep_levels = ("gate", "func", "full")
    rotate = False

    def __init__(self, dut, level, work_dir, stream_dir):
        self.stream_dir = Path(stream_dir)
        names = sorted(p.stem for p in self.stream_dir.glob("fuzz_*.hex"))
        if not names:
            raise FileNotFoundError(f"no fuzz_*.hex streams in {self.stream_dir}")
        super().__init__(dut, repo_root=os.environ["REPO_ROOT"], level=level,
                         work_dir=work_dir, tests=names)

    def discover(self):
        return list(self.tests)

    def image_words(self, name):
        words = load_verilog_hex(self.stream_dir / f"{name}.hex")
        return {(idx + (LINK_BASE >> 2)): w for idx, w in words.items()}

    def image_elf(self, name):
        return self.stream_dir / f"{name}.elf"

    def expected_halt(self, name):
        return None


@cocotb.test(timeout_time=600_000, timeout_unit="ms")
async def cocotb_test_gatling_fuzz(dut):
    level = os.environ.get("TEST_LEVEL", "func")
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    battery = FuzzBattery(dut, level=level,
                          work_dir=os.path.join(log_dir, "gatling_fuzz_battery"),
                          stream_dir=os.environ["GATLING_FUZZ_DIR"])
    await battery.run()


def _build_streams(test_level, log_dir):
    cell_seed = os.environ.get("SEED") or str(random.randint(0, 100000))
    stream_dir = Path(log_dir) / "gatling_fuzz" / f"streams_{test_level}"
    if stream_dir.exists():
        shutil.rmtree(stream_dir)
    stream_dir.mkdir(parents=True)
    seeds = fuzz_gen.seeds_for_level(test_level, cell_seed)
    programs = fuzz_gen.build_streams(seeds, stream_dir)
    LOG.info(f"{test_level}: built {len(programs)} fuzz streams in {stream_dir} "
             f"(cell seed {cell_seed})")
    return stream_dir, cell_seed


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_fuzz {lvl}") for lvl in reg_level_grid()])
def test_gatling_fuzz(request, test_level, description):
    from TBClasses.shared.utilities import get_paths
    _, _, _, log_dir, _ = get_paths({})
    os.makedirs(log_dir, exist_ok=True)
    stream_dir, cell_seed = _build_streams(test_level, log_dir)
    gatling_sim.run_cell(
        module="test_gatling_fuzz", testcase="cocotb_test_gatling_fuzz",
        toplevel="gatling_tb_top", filelist=gatling_sim.TB_FILELIST,
        cell=f"test_gatling_fuzz_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": str(LINK_BASE)},
        extra_env={"GATLING_FUZZ_DIR": str(stream_dir), "SEED": cell_seed})
