# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""
MC-003 residual repro: col_major_bl8_gap against the per-bank core.

The A7 cell that hangs the write engine at BANK_FIFO=1: col-major (same-bank
row thrash) BL8 traffic with an idle gap between txns, refresh firing in the
idle windows. This test drives exactly that shape at the granite_core level
(BANK_FIFO=1 via the core param) with the loopback DFI model:

  - writes: ROUNDS col-major bursts (same bank, 8 KB row stride), GAP idle
    cycles between txns, B awaited per txn (plus a long mid-stream idle);
  - reads: the same addresses in the same order, data checked per beat;
  - t_refi from DBG_TREFI (default 50 -> refresh fires constantly, the
    timing-dependent read-error regime).

A hang shows as a B/R SimTimeoutError; corruption shows as a data mismatch.
Run repeatedly (SEED varies the data) -- the board failure is
timing-dependent.
"""

import os
import sys
from collections import deque

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, with_timeout
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/"
             "rtl/filelists/top/granite.f")

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
_PUMICE_DV = os.path.abspath(os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "..", "..",
    "research-ip", "pumice-ddr2-lpddr2", "dv"))
if _PUMICE_DV not in sys.path:
    sys.path.insert(0, _PUMICE_DV)

from tbclasses.pumice_axi_bfm import PumiceAxiBfm          # noqa: E402
from tbclasses.pumice_top_csr_tb import board_clock_periods  # noqa: E402

_ACLK_NS, _DFI_NS = board_clock_periods()

DFI_RATE, DRAM_BEAT = 2, 64
DW = DRAM_BEAT * DFI_RATE
BL = 8
BL_WORDS = BL // DFI_RATE
ROW_STRIDE = 0x2000          # same-bank next row at bank_lsb=10 (col-major)
PHASE_TIMEOUT_US = 200


def _idle(dut):
    dut.memtype_i.value = 0
    dut.page_policy_i.value = 0          # OPEN
    dut.page_mode_i.value = 0
    dut.page_tr_init_i.value = 0
    dut.sched_order_mode_i.value = 0
    dut.sched_row_sel_i.value = 0
    dut.sched_col_sel_i.value = 0
    dut.sched_access_pref_i.value = 0
    dut.sched_wr_high_wm_i.value = 0
    dut.sched_wr_batch_max_i.value = 0
    dut.sched_wr_low_wm_i.value = 0
    dut.sched_prio_sub_i.value = 0
    dut.sched_qos_en_i.value = 0
    dut.sched_age_thresh_i.value = 0
    dut.bank_lsb_i.value = 10
    dut.hash_en_i.value = 0
    dut.hash_seed_i.value = 0
    for t, v in [("t_rcd_i", 2), ("t_rp_i", 2), ("t_ras_i", 3), ("t_rc_i", 4),
                 ("t_wr_i", 2), ("t_rtp_i", 2), ("t_faw_i", 4), ("t_rrd_i", 1),
                 ("t_wtr_i", 1), ("t_rtw_i", 1), ("t_ccd_i", 1)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = int(os.environ.get("DBG_TREFI", "50"), 0)
    dut.t_rfc_i.value = 8
    dut.refresh_burst_i.value = 1
    for t in ("t_init_wait_i", "t_dll_wait_i"):
        getattr(dut, t).value = 0
    for t in ("t_mrd_wait_i", "t_rp_wait_i", "t_rfc_wait_i"):
        getattr(dut, t).value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    dut.t_phy_wrlat_i.value = 1
    dut.t_rddata_en_i.value = 1
    dut.lp_mr1_op_i.value = 0x23
    dut.lp_mr2_op_i.value = 0x01
    dut.lp_mr3_op_i.value = 0x02
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.dfi_init_complete_i.value = 0


async def _dfi_model(dut, cap):
    """Order-loopback model with a read cursor: write beats accumulate in
    order; each read burst consumes the next BL_WORDS beats (reads arrive in
    write order in this test). Address-keyed would need the phase-split DFI
    address bus; order+cursor is exact for this traffic shape."""
    ret, returning, ri, gap = [], False, 0, 0
    pend = deque()
    rd_cursor = 0
    while True:
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_init_start_o.value):
            dut.dfi_init_complete_i.value = 1
        if int(dut.dfi_wrdata_en_o.value) != 0:
            cap.append(int(dut.dfi_wrdata_o.value))
        if int(dut.dfi_rddata_en_o.value) != 0 and not returning and not pend:
            pend.append(cap[rd_cursor:rd_cursor + BL_WORDS])
            rd_cursor += BL_WORDS
        if pend and not returning:
            gap += 1
            if gap >= 3:
                ret = pend.popleft(); returning = True; ri = 0; gap = 0
        if returning:
            dut.dfi_rddata_i.value = ret[ri]
            dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
            ri += 1
            if ri >= len(ret):
                returning = False
        else:
            dut.dfi_rddata_valid_i.value = 0


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_col_major_gap(dut):
    import random as _random
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units="ns").start())
    _idle(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)

    bfm = PumiceAxiBfm(dut, data_width=DW, bl_words=BL_WORDS)
    cap = []
    cocotb.start_soon(_dfi_model(dut, cap))

    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"

    rounds = int(os.environ.get("ROUNDS", "24"), 0)
    gap = int(os.environ.get("GAP", "8"), 0)
    seed = int(os.environ.get("SEED", "1"), 0)
    rng = _random.Random(seed)
    base = 0x2000

    wr_data = []
    for i in range(rounds):
        addr = base + i * ROW_STRIDE
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        wr_data.append((addr, data))
        try:
            await with_timeout(bfm.write(addr, data, wid=1),
                               PHASE_TIMEOUT_US, "us")
        except cocotb.result.SimTimeoutError:
            raise AssertionError(
                f"WRITE HANG at txn {i} (addr {addr:#x}): B never returned")
        await ClockCycles(dut.aclk, gap)
        if i == rounds // 2:               # the board's long idle window
            await ClockCycles(dut.aclk, 100)

    rd_back = []
    for i, (addr, data) in enumerate(wr_data):
        try:
            rd = await with_timeout(bfm.read(addr, rid=1),
                                    PHASE_TIMEOUT_US, "us")
        except cocotb.result.SimTimeoutError:
            raise AssertionError(
                f"READ HANG at txn {i} (addr {addr:#x}): R never returned")
        assert list(rd) == data, (
            f"READ MISMATCH at txn {i} (addr {addr:#x}): "
            f"got {[hex(x) for x in rd]} want {[hex(x) for x in data]}")
        rd_back.append(rd)
        await ClockCycles(dut.aclk, gap)

    dut._log.info("PASS col_major_gap: %d wr+rd txns, gap=%d, tREFI=%d, seed=%d",
                  rounds, gap, int(dut.t_refi_i.value), seed)


def test_granite_col_major_gap(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = "cocotb_test_col_major_gap"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module, testcase=test_name,
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "-Wno-PINMISSING",
                      "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        keep_files=True, timescale="1ns/1ps")
