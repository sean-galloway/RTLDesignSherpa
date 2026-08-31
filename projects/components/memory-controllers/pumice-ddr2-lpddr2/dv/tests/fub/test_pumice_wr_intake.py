# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Pattern-B runner for `pumice_wr_intake` (dumb AXI4 write intake).

  cocotb_test_pumice_wr_intake        - legal BL-sized bursts: decode + data
                                        passthrough + commit-driven B
  cocotb_test_pumice_wr_intake_ragged - ragged burst -> aw_push_err + SLVERR
                                        (RAGGED_ASSERT=0 so the $error doesn't
                                        abort the sim)
"""

import os
import sys
import random

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_wr_intake_tb import (  # noqa: E402
    PumiceWrIntakeTB, RESP_OKAY, RESP_SLVERR,
)

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_wr_intake.f")


# ---------------------------------------------------------------------------
# CocoTB tests
# ---------------------------------------------------------------------------
@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_wr_intake(dut):
    tb = PumiceWrIntakeTB(dut)
    await tb.setup_clocks_and_reset()

    level = os.environ.get("TEST_LEVEL", "basic").lower()
    n = {"basic": 4, "medium": 16, "full": 48}.get(level, 4)
    rng = random.Random(int(os.environ.get("SEED", "1")))

    expected_b = []
    for k in range(n):
        wid  = rng.randint(0, 15)
        addr = rng.randint(0, (1 << 20) - 1) << tb.BYTE_OFFSET_WIDTH
        data = [rng.randrange(1 << tb.AXI_DATA_WIDTH) for _ in range(tb.EXP_BEATS)]

        await tb.write_burst(addr, wid, data)
        await tb.wait_clocks('aclk', tb.EXP_BEATS + 6)
        await tb.pulse_wr_done(wid, RESP_OKAY)
        expected_b.append(wid)

        # aw_push: one decoded command for this burst
        assert len(tb.aw_push) == k + 1, \
            f"burst {k}: aw_push count {len(tb.aw_push)} != {k+1}"
        rank, bank, row, col, pid, err = tb.aw_push[k]
        assert (rank, bank, row, col) == tb.decode(addr), \
            f"burst {k}: decode {(rank,bank,row,col)} != {tb.decode(addr)} (addr {addr:#x})"
        assert pid == wid, f"burst {k}: aw_push id {pid} != {wid}"
        assert err == 0, f"burst {k}: unexpected err on legal burst"

        # wr-data: EXP_BEATS beats, in order, full strobe, last on final beat
        assert len(tb.wdata) == (k + 1) * tb.EXP_BEATS, \
            f"burst {k}: wdata count {len(tb.wdata)} != {(k+1)*tb.EXP_BEATS}"
        chunk = tb.wdata[k * tb.EXP_BEATS:(k + 1) * tb.EXP_BEATS]
        for i, d in enumerate(data):
            gd, gs, gl = chunk[i]
            assert gd == d, f"burst {k} beat {i}: data {gd:#x} != {d:#x}"
            assert gs == (1 << tb.SW) - 1, f"burst {k} beat {i}: strb {gs:#x}"
            assert gl == (1 if i == tb.EXP_BEATS - 1 else 0), \
                f"burst {k} beat {i}: last {gl}"

    await tb.wait_clocks('aclk', 12)
    got_ids = [b[0] for b in tb.bresp]
    assert got_ids == expected_b, f"B id order {got_ids} != {expected_b}"
    assert all(b[1] == RESP_OKAY for b in tb.bresp), \
        f"non-OKAY B: {tb.bresp}"
    tb.log.info(f"PASS: {n} bursts, {len(tb.wdata)} beats, {len(tb.bresp)} B responses")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_pumice_wr_intake_ragged(dut):
    tb = PumiceWrIntakeTB(dut)
    await tb.setup_clocks_and_reset()

    wid = 5
    addr = 0x4000
    ragged = tb.EXP_BEATS + 1          # (ragged)*GEAR != BL -> illegal
    data = [0xDEAD_0000 + i for i in range(ragged)]

    await tb.write_burst(addr, wid, data)
    await tb.wait_clocks('aclk', ragged + 10)

    assert len(tb.aw_push) >= 1, "no aw_push emitted for ragged burst"
    assert tb.aw_push[0][5] == 1, "aw_push_err not set on ragged burst"
    assert len(tb.bresp) >= 1, "no B response for ragged burst"
    assert tb.bresp[0] == (wid, RESP_SLVERR), \
        f"expected SLVERR B (id={wid}), got {tb.bresp[0]}"
    tb.log.info("PASS: ragged burst -> aw_push_err + SLVERR")


# ---------------------------------------------------------------------------
# Pytest wrappers
# ---------------------------------------------------------------------------
def _run(request, testcase, ragged_assert, bl=4):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_wr_intake"
    test_name = f"{testcase}_bl{bl}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "AXI_DATA_WIDTH":  "64",
        "DRAM_BEAT_WIDTH": "64",
        "NUM_RANKS":       "1",
        "NUM_BANKS":       "8",
        "ROW_WIDTH":       "14",
        "COL_WIDTH":       "10",
        "BYTE_OFFSET_WIDTH": "3",
        "AXI_BEATS_PER_BURST":              str(bl),
        "RAGGED_ASSERT":   str(ragged_assert),
    }
    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "basic").lower(),
    }
    extra_env.update({k: v for k, v in params.items()})

    compile_args = ["+define+USE_ASYNC_RESET"]
    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        timescale="1ns/1ps",
    )


def test_pumice_wr_intake(request):
    _run(request, "cocotb_test_pumice_wr_intake", ragged_assert=1, bl=4)


def test_pumice_wr_intake_ragged(request):
    _run(request, "cocotb_test_pumice_wr_intake_ragged", ragged_assert=0, bl=4)


# BL8 variants — the board config (DDR2 BL8 x16 / nphases=4). The stale BL4-only
# coverage let the on-silicon-BL8 sub-DFI-word path (and the AxLEN==BL contract)
# go untested at BL8; these close that gap. EXP_BEATS = BL/GEAR = 8 here.
def test_pumice_wr_intake_bl8(request):
    """Legal BL8 burst: (awlen+1)*GEAR == BL(8) -> decode + full data pass."""
    _run(request, "cocotb_test_pumice_wr_intake", ragged_assert=1, bl=8)


def test_pumice_wr_intake_ragged_bl8(request):
    """Ragged BL8 burst: (awlen+1)*GEAR != BL(8) -> aw_push_err + bresp=SLVERR."""
    _run(request, "cocotb_test_pumice_wr_intake_ragged", ragged_assert=0, bl=8)
