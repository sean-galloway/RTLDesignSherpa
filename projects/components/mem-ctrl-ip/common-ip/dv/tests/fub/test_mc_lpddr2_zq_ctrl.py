# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
FUB test: mc_lpddr2_zq_ctrl (common-ip) — the full Mode-C ZQ policy.

mc_training_plane ties demand_i to 1'b0 (ISSUE-021), which makes the
DEFER/ZQCL/overdue paths unreachable at the plane level. Those paths ARE the
runtime-ZQ feature set (TASK-042), so they are verified here at the fub
boundary with demand TB-driven:

  1. Periodic ZQCS at the interval: row {MR10, 0x56}, hold window, total.
  2. Defer under sustained demand -> overdue cap -> ZQCL: row {MR10, 0xAB},
     obs_overdue_o rises during defer and clears on grant.
  3. Defer exit on demand loss after deferring -> ZQCL (defer_cnt != 0).
  4. Grant-wait overdue: defer disabled, demand held while ungranted ->
     obs_overdue_o rises, next issue is still ZQCS.
  5. Gating: zq_en=0 / init_done=0 / DDR2 / interval=0 -> never requests.

Production change that makes each test fail: re-gate the FSM transitions,
change the MRW row packing, or alter the overdue/defer counting.
"""

import os

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, with_timeout

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_lpddr2_zq_ctrl_fub.f")

OP_MRS = 0x0A
MEMTYPE_DDR2   = 0x0
MEMTYPE_LPDDR2 = 0x4
ZQCS_ROW = (10 << 8) | 0x56
ZQCL_ROW = (10 << 8) | 0xAB
PHASE_TIMEOUT_NS = 200_000


async def _drive(dut, *, zq_en=1, init_done=1, memtype=MEMTYPE_LPDDR2,
                 interval=10, t_zqcs=2, t_zqcl=6, defer=0, overdue_max=0,
                 demand=0):
    dut.zq_en.value = zq_en
    dut.init_done.value = init_done
    dut.memtype.value = memtype
    dut.t_zqcs_interval.value = interval
    dut.t_zqcs.value = t_zqcs
    dut.t_zqcl.value = t_zqcl
    dut.zq_defer_en.value = defer
    dut.overdue_max.value = overdue_max
    dut.demand.value = demand
    dut.zq_grant.value = 0


async def _reset(dut):
    dut.mc_rst_n.value = 0
    for _ in range(5):
        await RisingEdge(dut.mc_clk)
    dut.mc_rst_n.value = 1
    await RisingEdge(dut.mc_clk)


async def _grant_when_req(dut):
    while True:
        await with_timeout(RisingEdge(dut.mc_clk), PHASE_TIMEOUT_NS, "ns")
        if int(dut.zq_req.value):
            row = int(dut.zq_row.value)
            is_zqcl = int(dut.zq_is_zqcl.value)
            dut.zq_grant.value = 1
            await RisingEdge(dut.mc_clk)
            dut.zq_grant.value = 0
            return row, is_zqcl


async def _wait_high(clk, sig, n=10):
    """Poll a (possibly registered) signal high across NBA-update races."""
    for _ in range(n):
        await RisingEdge(clk)
        if int(sig.value):
            return True
    return False


@cocotb.test()
async def cocotb_test_zqcs_interval(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    await _drive(dut, interval=10, t_zqcs=2, t_zqcl=6)
    await _reset(dut)

    row, is_zqcl = await _grant_when_req(dut)
    assert row == ZQCS_ROW and is_zqcl == 0, f"first issue row={row:#x} cl={is_zqcl}"
    assert int(dut.zq_op.value) == OP_MRS
    assert await _wait_high(dut.mc_clk, dut.cal_busy), "cal_busy never set"

    row, is_zqcl = await _grant_when_req(dut)
    assert row == ZQCS_ROW and is_zqcl == 0, f"second issue row={row:#x}"
    for _ in range(10):
        await RisingEdge(dut.mc_clk)
    assert int(dut.zqcs_total.value) == 2
    assert int(dut.obs_overdue.value) == 0


@cocotb.test()
async def cocotb_test_zqcl_on_overdue_cap(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    # defer_en + demand held: expiry -> DEFER; overdue cap 4 -> ZQCL request.
    await _drive(dut, interval=6, defer=1, overdue_max=4, demand=1,
                 t_zqcs=2, t_zqcl=6)
    await _reset(dut)

    row, is_zqcl = await _grant_when_req(dut)
    assert row == ZQCL_ROW and is_zqcl == 1, f"overdue issue row={row:#x} cl={is_zqcl}"
    # overdue rose during the defer window and clears on grant (registered:
    # settle a couple of edges before reading).
    for _ in range(3):
        await RisingEdge(dut.mc_clk)
    assert int(dut.obs_overdue.value) == 0, "overdue stuck after grant"
    assert int(dut.zqcs_total.value) == 1


@cocotb.test()
async def cocotb_test_defer_exit_on_demand_loss(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    # No overdue cap; demand drops mid-defer -> request, ZQCL (defer_cnt!=0).
    await _drive(dut, interval=6, defer=1, overdue_max=0, demand=1)
    await _reset(dut)

    # Defer window: req must not rise while demand holds; overdue sets on
    # DEFER entry. Poll for the defer (interval 6 + registered outputs),
    # accumulate a few defer cycles, then drop demand.
    for _ in range(200):
        await RisingEdge(dut.mc_clk)
        if int(dut.obs_overdue.value):
            break
    assert int(dut.obs_overdue.value) == 1, "never entered DEFER"
    for _ in range(3):
        await RisingEdge(dut.mc_clk)
        assert int(dut.zq_req.value) == 0, "req rose during defer"
    dut.demand.value = 0

    row, is_zqcl = await _grant_when_req(dut)
    assert is_zqcl == 1, f"exit-after-defer should be ZQCL, got cl={is_zqcl}"


@cocotb.test()
async def cocotb_test_grant_wait_overdue(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    # defer disabled, demand held, grant withheld: overdue rises in ZQ_REQ;
    # the eventual issue is still ZQCS.
    await _drive(dut, interval=6, defer=0, demand=1)
    await _reset(dut)

    while True:
        await with_timeout(RisingEdge(dut.mc_clk), PHASE_TIMEOUT_NS, "ns")
        if int(dut.zq_req.value):
            break
    for _ in range(8):
        await RisingEdge(dut.mc_clk)
        assert int(dut.zq_req.value) == 1, "req dropped while ungranted"
    assert int(dut.obs_overdue.value) == 1, "overdue not set under grant wait"

    row, is_zqcl = await _grant_when_req(dut)
    assert row == ZQCS_ROW and is_zqcl == 0
    for _ in range(4):
        await RisingEdge(dut.mc_clk)
    assert int(dut.obs_overdue.value) == 0, "overdue stuck after grant"


@cocotb.test()
async def cocotb_test_gated(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    for kw in (dict(zq_en=0), dict(init_done=0), dict(memtype=MEMTYPE_DDR2),
               dict(interval=0)):
        await _drive(dut, **{**dict(interval=10), **kw})
        await _reset(dut)
        for _ in range(80):
            await RisingEdge(dut.mc_clk)
            assert int(dut.zq_req.value) == 0, f"req with {kw}"
            assert int(dut.cal_busy.value) == 0


TESTS = [
    "cocotb_test_zqcs_interval",
    "cocotb_test_zqcl_on_overdue_cap",
    "cocotb_test_defer_exit_on_demand_loss",
    "cocotb_test_grant_wait_overdue",
    "cocotb_test_gated",
]


@pytest.mark.parametrize("testcase", TESTS)
def test_mc_lpddr2_zq_ctrl(request, testcase):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_lpddr2_zq_ctrl_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml")}
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
