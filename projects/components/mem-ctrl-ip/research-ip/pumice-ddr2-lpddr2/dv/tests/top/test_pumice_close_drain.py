# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""
Directed probe for CLOSE_ON_DRAIN (common-ip mc_cmd_arbiter).

Stimulus: one write (so the DFI read model has data to return), then 8 reads
to the SAME {bank,row,col} (a same-row group that fully drains), then 1 read
to a different row. Decisive observation: stat_pre_o must stay ZERO -- the
first row's close must ride the last column's auto-precharge (RDA), never an
explicit PRE. stat_act_o must be 2 (one per row). Also counts the qualified
AP emits on the command stream (u_sched_plane.u_arbiter.cmd_ap_o at
cmd_valid_o) to discriminate candidate-raised from fire-qualified.

Undirected benches showed col_major unchanged at 195 MB/s with PRE == ACT ==
1/txn on the board: this test narrows whether the candidate is raised at all
or always downgraded/inert at this geometry.
"""

import os
import sys

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/"
             "rtl/filelists/top/pumice_core.f")

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

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
    dut.sched_col_sel_i.value = 0        # age-ordered columns: CLOSE_ON_DRAIN gate
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
    # Board-geometry JEDEC timings (75 MHz, ck_per_mc=2)
    for t, v in [("t_rcd_i", 2), ("t_rp_i", 2), ("t_ras_i", 4), ("t_rc_i", 5),
                 ("t_wr_i", 4), ("t_rtp_i", 2), ("t_faw_i", 4), ("t_rrd_i", 2),
                 ("t_wtr_i", 4), ("t_rtw_i", 20), ("t_ccd_i", 1)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = 0x7FFF
    dut.t_rfc_i.value = 11
    dut.refresh_burst_i.value = 1
    dut.ref_postpone_i.value = 0
    dut.ref_pullin_i.value = 0
    dut.ref_mode_i.value = 0
    dut.ref_trefi_pb_i.value = 0
    dut.ref_trfc_pb_i.value = 0
    dut.refi_reload_i.value = 0
    for t in ("t_init_wait_i", "t_dll_wait_i"):
        getattr(dut, t).value = 0
    for t in ("t_mrd_wait_i", "t_rp_wait_i", "t_rfc_wait_i"):
        getattr(dut, t).value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    dut.t_phy_wrlat_i.value = 1
    dut.t_rddata_en_i.value = 1
    dut.gear_i.value = 1            # log2(DFI_RATE)
    dut.bl_i.value = BL
    dut.mr0_i.value = 0
    dut.mr1_i.value = 0
    dut.mr2_i.value = 0
    dut.mr3_i.value = 0
    dut.init_restart_i.value = 0
    dut.zq_en_i.value = 0
    dut.zq_defer_en_i.value = 0
    dut.zq_interval_i.value = 0
    dut.t_zqcs_i.value = 0
    dut.t_zqcl_i.value = 0
    dut.zq_overdue_max_i.value = 0
    dut.cal_start_i.value = 0
    dut.cal_abort_i.value = 0
    dut.t_mrr_i.value = 0
    dut.t_readout_i.value = 0
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.dfi_init_complete_i.value = 0


async def _dfi_model(dut, cap):
    from collections import deque
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
async def cocotb_test_close_drain(dut):
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

    arb = dut.u_sched_plane.u_arbiter
    ap_emits = []
    ops = []
    OP_NAMES = {0: "NOP", 1: "ACT", 2: "RD", 3: "RDA", 4: "WR", 5: "WRA",
                6: "PRE", 7: "PREA", 8: "REF"}
    cyc = {"n": 0}
    bt = dut.u_sched_plane.u_bank_timers.g_rank[0].g_bank[0].u_bt
    async def _tick():
        prev = None
        while True:
            await RisingEdge(dut.aclk)
            cyc["n"] += 1
            if cyc["n"] >= 30 and cyc["n"] <= 80:
                cur = (int(bt.r_row_valid.value), int(bt.r_ap_pending.value),
                       int(bt.r_rp.value), int(bt.r_ras.value), int(bt.r_preblk.value),
                       int(arb.r_pick_valid.value), int(arb.r_op.value),
                       int(arb.r_bank.value), int(arb.r_row.value),
                       int(arb.r_ap_out.value), int(arb.w_ap_sibling.value),
                       int(arb.w_ap_fire.value), int(arb.w_out_hold.value),
                       int(arb.w_out_safe.value), int(arb.r_do_act.value))
                if cur != prev:
                    dut._log.info("c%0d bt(v,ap,rp,ras,pblk)=(%d,%d,%d,%d,%d) "
                                  "out(pv,op,bk,rw,ap,sib,fire,hold,safe,act)=(%d,%02x,%d,%04x,%d,%d,%d,%d,%d,%d)",
                                  cyc["n"], *cur)
                    prev = cur
    cocotb.start_soon(_tick())
    async def _ap_monitor():
        while True:
            await RisingEdge(dut.aclk)
            if int(arb.cmd_valid_o.value):
                op = int(arb.cmd_op_o.value)
                ops.append(f"{cyc['n']}:{OP_NAMES.get(op, str(op))}")
                if int(arb.cmd_ap_o.value):
                    ap_emits.append(int(arb.cmd_bank_o.value))
    cocotb.start_soon(_ap_monitor())

    # seed the read model (its own row closes via WRA -- outside the window)
    await bfm.write(0x0, [0x1111_2222_3333_4444 + i for i in range(BL_WORDS)], wid=1)
    # let the seed write's commands leave the stat counters before snapshot
    for _ in range(20):
        await RisingEdge(dut.aclk)

    pre0  = int(dut.stat_pre_o.value)
    act0  = int(dut.stat_act_o.value)
    miss0 = int(dut.stat_page_miss_o.value)

    # Group drain: 8 reads, SAME {bank,row,col} (one row-group), then 1 read
    # to a different row. The group's LAST column must carry the only close.
    N_ROWS = 1
    REPS = 8
    addrs = [0x0] * REPS + [0x8000]
    results = await bfm.read_many(addrs, axid_fn=lambda k: (k & 0xF) or 1)
    bad = [(a, d) for a, d in results if any(int(x) != 0x1111222233334444 for x in d[:1])]
    dut._log.info("read back %d bursts, %d with unexpected first word", len(results), len(bad))

    for _ in range(400):
        await RisingEdge(dut.aclk)

    pre  = int(dut.stat_pre_o.value) - pre0
    act  = int(dut.stat_act_o.value) - act0
    miss = int(dut.stat_page_miss_o.value) - miss0

    # Phase 2: board-shape col_major -- 64 reads, row+1 each, SAME bank.
    # (Core mapper: 16B offset, bank=unit[11:9] -> byte 0x8000 was BANK 4;
    # same-bank row stride is 0x10000.)
    pre0b, act0b = int(dut.stat_pre_o.value), int(dut.stat_act_o.value)
    ops.clear()
    addrs2 = [k * 0x10000 for k in range(64)]
    await bfm.read_many(addrs2, axid_fn=lambda k: (k & 0xF) or 1)
    for _ in range(400):
        await RisingEdge(dut.aclk)
    n_rd2   = sum(1 for o in ops if o.endswith(":RD"))
    n_rda2  = sum(1 for o in ops if o.endswith(":RDA"))
    n_pre2  = int(dut.stat_pre_o.value) - pre0b
    n_act2  = int(dut.stat_act_o.value) - act0b
    dut._log.info("COL_MAJOR64: ACT=%d PRE=%d RD=%d RDA=%d (64 reads, 64 rows, "
                  "1 bank) -> ACT/txn=%.2f PRE/txn=%.2f",
                  n_act2, n_pre2, n_rd2, n_rda2, n_act2 / 64.0, n_pre2 / 64.0)
    dut._log.info("col_major stream: %s", " ".join(ops[:40]))
    with open("/tmp/close_drain_metrics.txt", "w") as fh:
        fh.write(f"COL_MAJOR64 ACT={n_act2} PRE={n_pre2} RD={n_rd2} RDA={n_rda2}\n")
        fh.write("stream: " + " ".join(ops) + "\n")
        fh.write(f"PHASE1 ACT={act} PRE={pre}\n")
    assert n_pre2 == 0, f"explicit PREs in steady col_major: {n_pre2}"
    # Phase 1 asserts -- group drain: row 0's 8 reads -> 1 ACT + 7 RD + 1 RDA
    # (the close); the 0x8000 read -> bank 4 (16B offset mapping), 1 ACT +
    # 1 RDA. Explicit PRE must be ZERO in both cases.
    assert pre == 0, (f"expected 0 explicit PREs (drained rows must close via "
                      f"the last column's auto-precharge), got {pre}")
    assert act == 2, f"expected 2 ACTs, got {act}"


def test_pumice_close_drain(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_core"
    test_name = "cocotb_test_close_drain"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": str(DFI_RATE), "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "DRAM_BL": str(BL),
              "NUM_ENTRIES": os.environ.get("PUMICE_NUM_ENTRIES", "8"),
              "N_SRAM_SLOTS": os.environ.get("PUMICE_NUM_ENTRIES", "8")}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_close_drain",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
