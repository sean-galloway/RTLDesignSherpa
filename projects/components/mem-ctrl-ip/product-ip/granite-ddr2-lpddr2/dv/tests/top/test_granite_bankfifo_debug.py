# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""
MC-003 debug: cycle-accurate trace of the granite BANK_FIFO head path around
the rd-slot lifetime race (issue of an already-freed slot). Clone of
test_granite_core's bring-up with a file-based state logger (the proven
close-drain idiom) tracing, per aclk edge:
  skid[0] (packed head_t slice), rd head view (valid/slot), bh2 valid,
  w_fire, cmd op/bank, rd_issue valid/slot, store r_rd_valid[0..1].
NOT a regression gate -- delete or fold into the real tests after MC-003.
"""

import os
import sys
import random
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
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

from tbclasses.pumice_axi_bfm import PumiceAxiBfm      # noqa: E402
from tbclasses.pumice_top_csr_tb import board_clock_periods  # noqa: E402
_ACLK_NS, _DFI_NS = board_clock_periods()

DFI_RATE, DRAM_BEAT = 2, 64
DW = DRAM_BEAT * DFI_RATE
BL = 8
BL_WORDS = BL // DFI_RATE


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
    dut.bank_lsb_i.value  = 10   # ROW_MAJOR
    dut.hash_en_i.value   = 0
    dut.hash_seed_i.value = 0
    for t, v in [("t_rcd_i", 2), ("t_rp_i", 2), ("t_ras_i", 3), ("t_rc_i", 4),
                 ("t_wr_i", 2), ("t_rtp_i", 2), ("t_faw_i", 4), ("t_rrd_i", 1),
                 ("t_wtr_i", 1), ("t_rtw_i", 1), ("t_ccd_i", 1)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = int(os.environ.get("DBG_TREFI", "32767"), 0)
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
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.dfi_init_complete_i.value = 0


async def _dfi_model(dut, cap):
    ret, returning, ri, gap = [], False, 0, 0
    pend = deque()
    while True:
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_init_start_o.value):
            dut.dfi_init_complete_i.value = 1
        if int(dut.dfi_wrdata_en_o.value) != 0:
            cap.append(int(dut.dfi_wrdata_o.value))
        if int(dut.dfi_rddata_en_o.value) != 0 and not returning and not pend:
            pend.append(list(cap))
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
async def cocotb_test_bankfifo_race(dut):
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())
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

    # The skid trace probes the per-bank core (g_bank_sched), which only
    # exists when the core is built with BANK_FIFO=1. Granite ships parked
    # at BANK_FIFO=0 (MC-003), so the trace disables itself there and the
    # test degrades to an init + traffic smoke.
    bs = None
    try:
        bs = dut.u_sched_plane.g_bank_sched.u_bank_sched
    except AttributeError:
        dut._log.info("BANK_FIFO=0 (parked): g_bank_sched absent, skid trace disabled")
    fh = open("/tmp/race_trace.txt", "w")
    n = {"n": 0}

    async def _trace():
        prev = None
        while True:
            await RisingEdge(dut.aclk)
            n["n"] += 1
            wv = int(bs.r_rs[1].value)
            vv = [int(dut.u_entry_store.r_rd_valid[i].value) for i in range(8)]
            if n["n"] > 20:
                fh.write("T%d skid(v%ds%d) bh1v%d bh1s%d bh2_1v%d fire%d op%02x bk%d iss(v%ds%d) valids%s\n"
                         % (n["n"], (wv >> 36) & 1, (wv >> 33) & 7,
                            (int(dut.w_rd_bh_v.value) >> 1) & 1,
                            (int(dut.w_rd_bh_slot.value) >> 3) & 7,
                            (int(dut.w_rd_bh2_v.value) >> 1) & 1,
                            int(bs.w_fire.value), int(bs.cmd_op_o.value), int(bs.cmd_bank_o.value),
                            int(bs.rd_issue_valid_o.value), int(bs.rd_issue_slot_o.value),
                            "".join(map(str, vv))))
                fh.flush()
            prev = None
    if bs is not None:
        cocotb.start_soon(_trace())

    # the failing pattern: one write, then 8 reads to one address
    await bfm.write(0x2000, [0xAAAA_0000_0000_0000 + i for i in range(BL_WORDS)], wid=1)
    for i in range(8):
        await bfm.read(0x2000, rid=1)

    for _ in range(200):
        await RisingEdge(dut.aclk)
    fh.close()
    dut._log.info("race trace complete, cycles=%d", n["n"])


def test_granite_bankfifo_debug(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = "cocotb_test_bankfifo_race"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": str(DFI_RATE), "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "DRAM_BL": str(BL),
              "NUM_ENTRIES": "8"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_bankfifo_race",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "-Wno-PINMISSING",
                      "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        keep_files=True, timescale="1ns/1ps")
