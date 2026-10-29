# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Macro test: mc_training_plane (common-ip) — runtime ZQ + DQ cal.

Pins the plane-boundary behavior per
docs/superpowers/specs/2026-10-15-mc-init-plane-design.md §6 (TASK-042/G-16
verification gap):
  1. Periodic ZQCS at zq_interval_i: OP_MRS with row {MR10, 0x56} on
     trn_cmd_*, grant handshake, zq_busy_o hold window, zqcs_total_o counts.
  2. Demand-gated Mode-C policy through the plane's demand_i (pumice
     ISSUE-021, wired 2026-10-29; before that the plane tied demand to 0 and
     the policy was unreachable): with zq_defer_en and demand held, the
     interval expiry DEFERS (zq_overdue_o high, no request); loss of demand
     releases a ZQCL (row {MR10, 0xAB}); with zq_overdue_max the deferral is
     cut at the limit with demand still high, again as ZQCL. With
     zq_defer_en=0 demand changes nothing: ZQCS at the interval and
     zq_overdue_o stays 0 (the OFF state of the knob, tested on its own).
  3. Gating: no trn_cmd activity before init_done, or for DDR2, or with
     zq_en=0.
  4. DQ cal: cal_start -> MRR32 (row {MR32,0}) -> cal_expect_o pulse ->
     cal_data/cal_valid beat -> MRR40 -> done; mrr32/40_data_o hold the
     captured patterns; cal_err_o stays 0.

Production change that makes each test fail: break the ZQCS row packing,
grant/hold handshake, the run gating, or the MRR/expect/data protocol.
Op codes mirror mc_common_pkg.sv (OP_MRS = 5'h0A).
"""

import os

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, with_timeout

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_training_plane_macro.f")

OP_MRS = 0x0A

MEMTYPE_DDR2   = 0x0
MEMTYPE_LPDDR2 = 0x4

ZQCS_ROW = (10 << 8) | 0x56
ZQCL_ROW = (10 << 8) | 0xAB
MRR32_ROW = (32 << 8)
MRR40_ROW = (40 << 8)

PHASE_TIMEOUT_NS = 200_000
CAL_DATA_W = 128
PAT32 = 0x1234_ABCD_5678_9ABC_DEF0_1234_5678_9ABC & ((1 << CAL_DATA_W) - 1)
PAT40 = 0x0FED_CBA9_8765_4321_0FED_CBA9_8765_4321 & ((1 << CAL_DATA_W) - 1)


async def _drive_config(dut, *, memtype=MEMTYPE_LPDDR2, zq_en=0, zq_interval=0,
                        t_zqcs=2, t_zqcl=8, defer=0, overdue_max=0,
                        init_done=1, demand=0):
    dut.demand.value = demand
    dut.memtype.value = memtype
    dut.zq_en.value = zq_en
    dut.zq_interval.value = zq_interval
    dut.t_zqcs.value = t_zqcs
    dut.t_zqcl.value = t_zqcl
    dut.zq_defer_en.value = defer
    dut.zq_overdue_max.value = overdue_max
    dut.init_done.value = init_done
    dut.cal_start.value = 0
    dut.cal_abort.value = 0
    dut.t_mrr.value = 2
    dut.t_readout.value = 400


async def _reset(dut):
    dut.mc_rst_n.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(5):
        await RisingEdge(dut.mc_clk)
    dut.mc_rst_n.value = 1
    dut.dfi_rstn.value = 1
    await RisingEdge(dut.mc_clk)


async def _grant_when_req(dut):
    """Wait for trn_cmd_req_o, return (op,row,mrr) sampled that cycle, and
    grant for exactly one mc_clk."""
    while True:
        await with_timeout(RisingEdge(dut.mc_clk), PHASE_TIMEOUT_NS, "ns")
        if int(dut.trn_cmd_req.value):
            op = int(dut.trn_cmd_op.value)
            row = int(dut.trn_cmd_row.value)
            mrr = int(dut.trn_cmd_mrr.value)
            dut.trn_cmd_grant.value = 1
            await RisingEdge(dut.mc_clk)
            dut.trn_cmd_grant.value = 0
            return op, row, mrr


async def _wait_high(clk, sig, n=10):
    """Poll a (possibly registered) signal high across NBA-update races."""
    for _ in range(n):
        await RisingEdge(clk)
        if int(sig.value):
            return True
    return False


async def _drive_cal_beat(dut, pattern):
    """DFI-side model: on the cal_expect_o pulse, present one captured beat.

    cal_data crosses through a LEVEL synchronizer (3 flops, mc_clk side) and
    must be stable around the capture; cal_valid crosses through sync_pulse,
    whose source domain TOGGLES EVERY SRC CYCLE THE INPUT IS HIGH -- so valid
    must be a exactly-one-dfi-clk pulse (holding it high multi-fires the
    destination)."""
    while True:
        await with_timeout(RisingEdge(dut.dfi_clk), PHASE_TIMEOUT_NS, "ns")
        if int(dut.cal_expect.value):
            break
    dut.cal_data.value = pattern
    for _ in range(4):   # level-sync settle before the valid pulse
        await RisingEdge(dut.dfi_clk)
    dut.cal_valid.value = 1
    await RisingEdge(dut.dfi_clk)
    dut.cal_valid.value = 0
    for _ in range(4):   # hold data stable a little past the pulse
        await RisingEdge(dut.dfi_clk)
    dut.cal_data.value = 0


@cocotb.test()
async def cocotb_test_zqcs_interval(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 14, units="ns").start())
    await _drive_config(dut, zq_en=1, zq_interval=20, t_zqcs=3, t_zqcl=9)
    await _reset(dut)

    op, row, mrr = await _grant_when_req(dut)
    assert op == OP_MRS and row == ZQCS_ROW and mrr == 0, \
        f"ZQCS cmd op={op:#x} row={row:#x} mrr={mrr}"
    assert await _wait_high(dut.mc_clk, dut.zq_busy), "zq_busy never set"

    op, row, mrr = await _grant_when_req(dut)
    assert op == OP_MRS and row == ZQCS_ROW and mrr == 0, \
        f"second ZQCS cmd op={op:#x} row={row:#x}"
    for _ in range(10):
        await RisingEdge(dut.mc_clk)
    assert int(dut.zqcs_total.value) == 2, f"zqcs_total={int(dut.zqcs_total.value)}"
    # No demand driven in this test -> no deferral, no overdue.
    assert int(dut.zq_overdue.value) == 0


async def _no_req_for(dut, n):
    for _ in range(n):
        await RisingEdge(dut.mc_clk)
        assert int(dut.trn_cmd_req.value) == 0, "request raised while deferring"


@cocotb.test()
async def cocotb_test_zq_defer_releases_zqcl(dut):
    """defer=1, demand held: the interval expiry defers (overdue high, no
    request); dropping demand releases ONE request, and it is ZQCL."""
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 14, units="ns").start())
    await _drive_config(dut, zq_en=1, zq_interval=20, t_zqcs=3, t_zqcl=9,
                        defer=1, overdue_max=0, demand=1)
    await _reset(dut)
    assert await _wait_high(dut.mc_clk, dut.zq_overdue, n=40), \
        "zq_overdue never rose while deferring under demand"
    await _no_req_for(dut, 60)          # held as long as demand holds
    dut.demand.value = 0
    op, row, mrr = await _grant_when_req(dut)
    assert op == OP_MRS and row == ZQCL_ROW and mrr == 0, \
        f"release cmd op={op:#x} row={row:#x} (want ZQCL {ZQCL_ROW:#x})"
    for _ in range(4):
        await RisingEdge(dut.mc_clk)
    assert int(dut.zq_overdue.value) == 0, "overdue stuck after the grant"
    assert int(dut.zq_busy.value) == 1, "zq_busy not holding t_zqcl"


@cocotb.test()
async def cocotb_test_zq_overdue_limit_forces_zqcl(dut):
    """defer=1, overdue_max=6, demand held forever: the deferral is cut at the
    limit and the request is ZQCL with demand still high."""
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 14, units="ns").start())
    await _drive_config(dut, zq_en=1, zq_interval=20, t_zqcs=3, t_zqcl=9,
                        defer=1, overdue_max=6, demand=1)
    await _reset(dut)
    op, row, mrr = await _grant_when_req(dut)
    assert op == OP_MRS and row == ZQCL_ROW and mrr == 0, \
        f"limit cmd op={op:#x} row={row:#x} (want ZQCL {ZQCL_ROW:#x})"
    assert int(dut.demand.value) == 1


@cocotb.test()
async def cocotb_test_zq_defer_off_ignores_demand(dut):
    """defer=0 (the knob's OFF state), demand held: ZQCS at the interval
    exactly as without demand, and zq_overdue stays 0 once granted."""
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 14, units="ns").start())
    await _drive_config(dut, zq_en=1, zq_interval=20, t_zqcs=3, t_zqcl=9,
                        defer=0, overdue_max=6, demand=1)
    await _reset(dut)
    op, row, mrr = await _grant_when_req(dut)
    assert op == OP_MRS and row == ZQCS_ROW and mrr == 0, \
        f"defer-off cmd op={op:#x} row={row:#x} (want ZQCS {ZQCS_ROW:#x})"
    # Let the hold window start before looking for the next request: the
    # granted request stays visible for one more edge (see _wait_high).
    assert await _wait_high(dut.mc_clk, dut.zq_busy), "zq_busy never set"
    op, row, mrr = await _grant_when_req(dut)
    assert row == ZQCS_ROW, f"second cmd row={row:#x}"
    for _ in range(10):
        await RisingEdge(dut.mc_clk)
    assert int(dut.zqcs_total.value) == 2
    assert int(dut.zq_overdue.value) == 0


@cocotb.test()
async def cocotb_test_gated(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 14, units="ns").start())

    # init_done = 0: nothing may issue — and cal_start MUST be pulsed here,
    # or the gate it claims to pin is never exercised (the FSM never leaves
    # CAL_IDLE without cal_start, gate or no gate).
    await _drive_config(dut, zq_en=1, zq_interval=4, init_done=0)
    await _reset(dut)
    dut.cal_start.value = 1
    await RisingEdge(dut.mc_clk)
    dut.cal_start.value = 0
    for _ in range(100):
        await RisingEdge(dut.mc_clk)
        assert int(dut.trn_cmd_req.value) == 0, "req before init_done"
        assert int(dut.cal_busy.value) == 0
        assert int(dut.cal_done.value) == 0

    # DDR2 memtype: ZQ/cal are LPDDR2-only — request both, nothing may issue.
    await _drive_config(dut, zq_en=1, zq_interval=4, memtype=MEMTYPE_DDR2)
    await _reset(dut)
    dut.cal_start.value = 1
    await RisingEdge(dut.mc_clk)
    dut.cal_start.value = 0
    for _ in range(100):
        await RisingEdge(dut.mc_clk)
        assert int(dut.trn_cmd_req.value) == 0, "req for DDR2"
        assert int(dut.cal_busy.value) == 0
        assert int(dut.cal_done.value) == 0

    # zq_en = 0 with LPDDR2: no ZQ requests (cal is gated separately and is
    # exercised by test_dq_cal_mrr32_40).
    await _drive_config(dut, zq_en=0, zq_interval=4)
    await _reset(dut)
    for _ in range(100):
        await RisingEdge(dut.mc_clk)
        assert int(dut.trn_cmd_req.value) == 0, "req with zq_en=0"


@cocotb.test()
async def cocotb_test_dq_cal_mrr32_40(dut):
    cocotb.start_soon(Clock(dut.mc_clk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 14, units="ns").start())
    await _drive_config(dut, zq_en=0)
    await _reset(dut)

    dut.cal_start.value = 1
    await RisingEdge(dut.mc_clk)
    dut.cal_start.value = 0
    assert await _wait_high(dut.mc_clk, dut.cal_busy), "cal_busy never set"

    # MRR32: req + expect pulse + captured beat.
    op, row, mrr = await _grant_when_req(dut)
    assert op == OP_MRS and row == MRR32_ROW and mrr == 1, \
        f"MRR32 cmd op={op:#x} row={row:#x} mrr={mrr}"
    await _drive_cal_beat(dut, PAT32)

    # MRR40: second req.
    op, row, mrr = await _grant_when_req(dut)
    assert op == OP_MRS and row == MRR40_ROW and mrr == 1, \
        f"MRR40 cmd op={op:#x} row={row:#x} mrr={mrr}"
    await _drive_cal_beat(dut, PAT40)

    for _ in range(20):
        await RisingEdge(dut.mc_clk)
    assert int(dut.cal_done.value) == 1, "cal_done not set"
    assert int(dut.cal_err.value) == 0, f"cal_err set ({int(dut.cal_err.value)})"
    assert int(dut.mrr32_data.value) == PAT32, \
        f"mrr32_data={int(dut.mrr32_data.value):#x} != {PAT32:#x}"
    assert int(dut.mrr40_data.value) == PAT40, \
        f"mrr40_data={int(dut.mrr40_data.value):#x} != {PAT40:#x}"
    assert int(dut.cal_busy.value) == 0


TESTS = [
    "cocotb_test_zqcs_interval",
    "cocotb_test_gated",
    "cocotb_test_dq_cal_mrr32_40",
    "cocotb_test_zq_defer_releases_zqcl",
    "cocotb_test_zq_overdue_limit_forces_zqcl",
    "cocotb_test_zq_defer_off_ignores_demand",
]


@pytest.mark.parametrize("testcase", TESTS)
def test_mc_training_plane(request, testcase):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_training_plane_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"ROW_WIDTH": "18", "CAL_DATA_WIDTH": str(CAL_DATA_W)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      FIELD_COMBO_VLT, "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
