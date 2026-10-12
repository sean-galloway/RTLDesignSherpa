# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
End-to-end smoke for `granite_core` (the storage-lite product controller).

Cloned from research-ip/pumice-ddr2-lpddr2/dv/tests/top/test_pumice_core.py —
same DFI-domain memory model, same AXI BFM, same board clock parity. The
ONLY differences are the DUT, its filelist, and its parameter set (no
N_SRAM_PORTS knob; NUM_ENTRIES defaults to GRANITE_SEAM_N=1).

Why this test exists: the A7 bring-up (FINDINGS_granite_bringup_2026-10-11.md)
showed init_done=1 then a silent read hang. Lint and every fub sim were green
because none of them closes the read-return contract through the entry store.
This test is the missing reproduction: one AXI write burst + one read burst
against a DFI model, with signal probes dumped on either phase's timeout so
the stall boundary is visible in the log.
"""

import os
import sys
import random
from collections import deque

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, SimTimeoutError, with_timeout
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

_FILELIST = ("projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/"
             "rtl/filelists/top/granite.f")

# dv/ on sys.path so `tbclasses.*` resolves; import AFTER the insert.
# granite has no tbclasses of its own yet -- the BFM is the pumice one, shared
# verbatim (it binds generic s_axi_* ports, nothing pumice-specific).
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
_PUMICE_DV = os.path.abspath(os.path.join(
    os.path.dirname(__file__), "..", "..", "..", "..", "..",
    "research-ip", "pumice-ddr2-lpddr2", "dv"))
if _PUMICE_DV not in sys.path:
    sys.path.insert(0, _PUMICE_DV)

from tbclasses.pumice_axi_bfm import PumiceAxiBfm      # noqa: E402
from tbclasses.pumice_levels import depth as _profile_depth  # noqa: E402

from tbclasses.pumice_top_csr_tb import board_clock_periods  # noqa: E402
_ACLK_NS, _DFI_NS = board_clock_periods()   # BOARD parity, not literals

DFI_RATE, DRAM_BEAT = 2, 64
DW = DRAM_BEAT * DFI_RATE          # 128 (host AXI = DFI word)
SW = DW // 8
BL = 8
BL_WORDS = BL // DFI_RATE          # 4  (host AXI burst beats)
BURST_INCR = 1

_PHASE_TIMEOUT_US = 200


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_granite_core(dut):
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

    bfm = _init_masters(dut)

    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))

    # wait for init to complete
    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"

    rng = random.Random(int(os.environ.get("SEED", "1")))
    roundtrips = _profile_depth('core_roundtrips')
    dut._log.info("depth: TEST_LEVEL=%s core_roundtrips=%d",
                  os.environ.get("TEST_LEVEL", "gate"), roundtrips)
    for rnd in range(roundtrips):
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        addr = 0x2000 + rnd * 0x1000
        captured.clear()

        # ---- AXI write burst, then read the same address back ----
        mon = cocotb.start_soon(_cmd_monitor(dut))
        try:
            await with_timeout(bfm.write(addr, data, wid=1), _PHASE_TIMEOUT_US, "us")
        except SimTimeoutError:
            mon.kill()
            await _dump_probes(dut, "WRITE")
            raise AssertionError(f"round {rnd}: AXI write never returned B")
        mon.kill()

        if len(captured) < BL_WORDS:
            # B fires when the entry store's staging FIFO drains into the DFI
            # plane's wd FIFO -- the WR command itself lands CMD_DELAY cycles
            # later, behind whatever maintenance the scheduler is draining.
            # Poll the DFI bus for the burst instead of sampling the same
            # delta cycle (which fails on a healthy design).
            async def _wait_wrdma():
                while len(captured) < BL_WORDS:
                    await RisingEdge(dut.dfi_clk)
            try:
                await with_timeout(_wait_wrdma(), _PHASE_TIMEOUT_US, "us")
            except SimTimeoutError:
                await _dump_probes(dut, "WRITE-NODATA")
                raise AssertionError(
                    f"round {rnd}: only {len(captured)} words hit the DFI write bus")

        assert len(captured) >= BL_WORDS, \
            (f"round {rnd}: only {len(captured)} words hit the DFI write bus; "
             f"entry wr state / cmd activity dumped above")
        assert captured[:BL_WORDS] == data, \
            f"round {rnd}: DFI write burst {[hex(x) for x in captured[:BL_WORDS]]} != {[hex(x) for x in data]}"

        trace = []
        dut._rd_trace = trace
        tracer = cocotb.start_soon(_rd_pin_tracer(dut, trace))
        try:
            rd = await with_timeout(bfm.read(addr, rid=1), _PHASE_TIMEOUT_US, "us")
        except SimTimeoutError:
            tracer.kill()
            for rec in trace[:80]:
                dut._log.info("RDTRACE %s", rec)
            await _dump_probes(dut, "READ")
            raise AssertionError(f"round {rnd}: AXI read never returned R data")
        tracer.kill()

        if rd[:BL_WORDS] != data:
            # replay the captured DFI return window
            for rec in getattr(dut, "_rd_trace", [])[:80]:
                dut._log.info("RDTRACE %s", rec)
            await _dump_probes(dut, "READ-BADDATA")
        assert rd[:BL_WORDS] == data, \
            f"round {rnd}: AXI read-back {[hex(x) for x in rd[:BL_WORDS]]} != {[hex(x) for x in data]}"
    dut._log.info("PASS: init done; AXI write burst -> DFI -> read burst back == written data, x%d",
                  roundtrips)


async def _cmd_monitor(dut):
    """Count command-stream fires by op while a phase runs. Killed by the caller
    when the phase ends; results are read by _dump_probes via dut._cmd_log."""
    log = {"fires": {}, "schv_cycles": 0, "cycles": 0}
    dut._cmd_log = log
    prev_v = 0
    while True:
        await RisingEdge(dut.aclk)
        log["cycles"] += 1
        try:
            v = int(dut.w_cmd_v.value) and int(dut.w_cmd_rdy.value)
            if v and not prev_v:
                op = int(dut.w_cmd_op.value)
                log["fires"][op] = log["fires"].get(op, 0) + 1
            prev_v = v
            if int(dut.w_wr_sch_v.value) & 1:
                log["schv_cycles"] += 1
        except Exception:
            pass


async def _rd_pin_tracer(dut, trace, max_cyc=400):
    """Record the DFI read-return window, one row per dfi_clk edge."""
    for _ in range(max_cyc):
        await RisingEdge(dut.dfi_clk)
        try:
            trace.append({
                "en":   int(dut.dfi_rddata_en_o.value),
                "vld":  int(dut.dfi_rddata_valid_i.value),
                "data": int(dut.dfi_rddata_i.value) & 0xffffffff,
                "ret_v": int(dut.w_ret_v.value),
                "ret_r": int(dut.w_ret_rdy.value),
            })
        except Exception:
            pass


async def _dump_probes(dut, phase):
    """Sample the write/read-path seams for a few cycles so the log shows WHERE the
    stall lives. Every probe is guarded -- Verilator may optimize an internal
    net; a missing probe must not hide the ones that survive."""
    cmd_log = getattr(dut, "_cmd_log", None)
    if cmd_log is not None:
        dut._log.info("HANG[%s] cmd_log: %s", phase, cmd_log)
    for _ in range(8):
        await RisingEdge(dut.aclk)
        snap = {}
        for s in ("ar_push_valid", "ar_push_ready", "rt_alloc_ready",
                  "rd_iss_valid", "rd_iss_ready",
                  "w_rd_issue_v", "w_rd_issue_rdy",
                  "w_wr_commit_v", "w_wr_commit_rdy",
                  "aw_push_valid", "aw_push_ready",
                  "w_ret_v", "w_ret_rdy", "w_cmd_v", "w_cmd_rdy"):
            try:
                snap[s] = int(getattr(dut, s).value)
            except Exception:
                snap[s] = None
        for s in ("r_wr_valid", "r_wr_fdone", "r_wr_sched",
                  "r_rd_valid", "r_rd_issued"):
            try:
                snap[f"entry.{s}"] = int(getattr(dut.u_entry_store, s).value)
            except Exception:
                snap[f"entry.{s}"] = None
        # DFI pin + return-path activity: how many rddata windows, how many
        # valid words actually reached the ring, what drained.
        pins = {"en": 0, "valid": 0}
        for _ in range(64):
            await RisingEdge(dut.dfi_clk)
            try:
                if int(dut.dfi_rddata_en_o.value) != 0:
                    pins["en"] += 1
                if int(dut.dfi_rddata_valid_i.value) != 0:
                    pins["valid"] += 1
            except Exception:
                pass
        snap["dfi_pins_64cyc"] = pins
        for s in ("stall_noreq_o", "stall_banktimer_o", "stall_refresh_o",
                  "stall_bp_o", "stall_turnaround_o"):
            try:
                snap[f"sched.{s}"] = int(getattr(dut.u_sched_plane, s).value)
            except Exception:
                snap[f"sched.{s}"] = None
        try:
            snap["ring.occ"] = int(dut.u_axi_plane.u_rd_ring.r_occ.value)
        except Exception:
            snap["ring.occ"] = None
        dut._log.info("HANG[%s] %s", phase, snap)


def _idle(dut):
    dut.memtype_i.value = 0
    dut.page_policy_i.value = 0          # OPEN
    dut.bank_lsb_i.value  = 10   # ROW_MAJOR
    dut.hash_en_i.value   = 0
    dut.hash_seed_i.value = 0
    for t, v in [("t_rcd_i", 2), ("t_rp_i", 2), ("t_ras_i", 3), ("t_rc_i", 4),
                 ("t_wr_i", 2), ("t_rtp_i", 2), ("t_faw_i", 4), ("t_rrd_i", 1),
                 ("t_wtr_i", 1), ("t_rtw_i", 1), ("t_ccd_i", 1)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = 0x7FFF
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
    """DFI-domain model: finish init, capture writes, serve reads.

    One rddata_en window == one DRAM burst == BL_WORDS words, served in write
    order after a 3-cycle gap. Strict per-edge signal discipline: each signal
    is assigned exactly once per dfi_clk edge, so valid never glitches mid-
    burst (the previous coroutine form raced the clock and corrupted a beat)."""
    chunks = 0
    in_window = False
    rd_q = deque()
    state = "idle"
    gap_left = 0
    beat_left = 0
    while True:
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_init_start_o.value):
            dut.dfi_init_complete_i.value = 1
        if int(dut.dfi_wrdata_en_o.value) != 0:
            cap.append(int(dut.dfi_wrdata_o.value))
        # A read's rddata_en window spans several dfi cycles (BL8 over rate 2
        # = 4); the whole window is ONE request. Count only the rising edge.
        if int(dut.dfi_rddata_en_o.value) != 0:
            if not in_window:
                chunks += 1
                in_window = True
        else:
            in_window = False
        if state == "idle":
            if chunks > 0 and not rd_q and cap:
                # Refill once at the FIRST window after the write (cap is
                # complete by then); later windows of the same read set drain
                # rd_q in order. Re-snapshotting per window would replay word
                # 0 for every read.
                rd_q = deque(cap)
            if chunks > 0 and rd_q:
                chunks -= 1
                state = "gap"
                gap_left = 2
            dut.dfi_rddata_valid_i.value = 0
        elif state == "gap":
            gap_left -= 1
            if gap_left == 0:
                state = "data"
                beat_left = min(BL_WORDS, len(rd_q))
            dut.dfi_rddata_valid_i.value = 0
        else:
            dut.dfi_rddata_i.value = rd_q.popleft()
            dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
            beat_left -= 1
            if beat_left == 0:
                state = "idle"


def _init_masters(dut):
    """AXI4 master BFMs on s_axi -- the ONLY thing that drives that port."""
    return PumiceAxiBfm(dut, data_width=DW, bl_words=BL_WORDS)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_granite_core(request, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_core"
    test_name = f"cocotb_test_granite_core_{test_level}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": str(DFI_RATE), "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "DRAM_BL": str(BL)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env(test_level)}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_core",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"], waves=False, keep_files=True, timescale="1ns/1ps")
