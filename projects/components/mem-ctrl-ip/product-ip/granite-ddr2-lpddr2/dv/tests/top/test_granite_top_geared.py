# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Integration smoke for `granite_top_geared` — the layer test_granite_core
does not cover: PeakRDL CSR regfile -> core config wiring, GEAR-1 converter
bypass (HOST_AXI_DATA_WIDTH == DW), and the init handshake driven exactly the
way the A7 host drives it (CTRL.soft_reset, poll STATUS.init_done).

A7 geometry: AXI 64b host, DRAM_BEAT_WIDTH 32, DFI_RATE 2, DRAM_BL 4,
DRAM_DEVICE_WIDTH 32 -> core DW 64, BURST_WORDS 2. Same loose DFI memory
model as the core test: capture writes, return them on reads.

If this passes while the board hangs, the granite controller stack is
exonerated and the defect lives above it (char harness or host flow).
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
             "rtl/filelists/top/granite_top_geared.f")

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
_ACLK_NS, _DFI_NS = board_clock_periods()

DFI_RATE, DRAM_BEAT = 2, 32
DW = DRAM_BEAT * DFI_RATE          # 64
SW = DW // 8
BL = 4
DRAM_DEV = int(os.environ.get("GRANITE_DRAM_DEV", "16"))   # A7 board: x16 devices
# AXI beats per host burst the engines use. With DEV=16: BL_SHIFT=1,
# BL_PUMICE=2, BURST_WORDS=1 -- every engine burst is split into 1-beat
# DRAM sub-bursts (the path the board exercises and the earlier sims did not).
BL_WORDS = int(os.environ.get("GRANITE_BL_WORDS", "8"))
# DFI words per DRAM burst -- what the aligner captures per read (the host
# burst BL_WORDS is a different quantity once DRAM_DEVICE_WIDTH < BEAT width).
_BL_SHIFT = (DRAM_BEAT // DRAM_DEV).bit_length() - 1 if DRAM_DEV < DRAM_BEAT else 0
BURST_WORDS = max(1, (BL >> _BL_SHIFT) // DFI_RATE)

CSR_CTRL = 0x000
CSR_STATUS = 0x004
CTRL_SOFT_RESET = 1 << 31
STATUS_INIT_DONE = 1 << 0

_PHASE_TIMEOUT_US = 200


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_granite_top_geared(dut):
    cocotb.start_soon(Clock(dut.aclk, _ACLK_NS, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, _DFI_NS, units='ns').start())

    dut.s_cpuif_req.value = 0
    dut.s_cpuif_req_is_wr.value = 0
    dut.s_cpuif_addr.value = 0
    dut.s_cpuif_wr_data.value = 0
    dut.s_cpuif_wr_biten.value = 0
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.dfi_init_complete_i.value = 0

    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)

    bfm = PumiceAxiBfm(dut, data_width=DW, bl_words=BL_WORDS)

    captured = []
    cocotb.start_soon(_dfi_model(dut, captured))

    # init, host-style: soft_reset kick, then poll STATUS.init_done
    await _csr_write(dut, CSR_CTRL, CTRL_SOFT_RESET)
    for _ in range(2000):
        await RisingEdge(dut.aclk)
        st = await _csr_read(dut, CSR_STATUS)
        if st & STATUS_INIT_DONE:
            break
    assert st & STATUS_INIT_DONE, f"init never completed (STATUS={st:#x})"

    # Mirror the char engines: N back-to-back host bursts, write then read.
    # A single BFM burst cannot reproduce the engines' multi-outstanding
    # pipelining (the board wedge needed ~6 bursts in flight).
    many = int(os.environ.get("GRANITE_MANY", "0"))
    rng = random.Random(int(os.environ.get("SEED", "1")))
    roundtrips = _profile_depth('core_roundtrips')
    dut._log.info("depth: TEST_LEVEL=%s core_roundtrips=%d",
                  os.environ.get("TEST_LEVEL", "gate"), roundtrips)
    for rnd in range(roundtrips):
        data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
        addr = 0x2000 + rnd * 0x1000
        captured.clear()

        try:
            if many:
                reqs = [(addr + i * 0x100, [rng.randrange(1 << DW) for _ in range(BL_WORDS)])
                        for i in range(many)]
                await with_timeout(bfm.write_many(reqs), _PHASE_TIMEOUT_US, "us")
            else:
                await with_timeout(bfm.write(addr, data, wid=1), _PHASE_TIMEOUT_US, "us")
        except SimTimeoutError:
            await _dump_probes(dut, "WRITE")
            raise AssertionError(f"round {rnd}: AXI write never returned B")

        n_wr = many * BL_WORDS if many else BL_WORDS
        async def _wait_wrdma():
            while len(captured) < n_wr:
                await RisingEdge(dut.dfi_clk)
        await with_timeout(_wait_wrdma(), _PHASE_TIMEOUT_US, "us")

        exp_wr = [beat for _, beats in reqs for beat in beats] if many else data
        assert captured[:len(exp_wr)] == exp_wr, \
            f"round {rnd}: DFI write burst {[hex(x) for x in captured[:len(exp_wr)]]} != {[hex(x) for x in exp_wr]}"

        try:
            if many:
                results = await with_timeout(
                    bfm.read_many([a for a, _ in reqs]), _PHASE_TIMEOUT_US, "us")
                rd = [beat for _, beats in results for beat in beats]
                exp = [beat for _, beats in reqs for beat in beats]
            else:
                rd = await with_timeout(bfm.read(addr, rid=1), _PHASE_TIMEOUT_US, "us")
                exp = data
        except SimTimeoutError:
            await _dump_probes(dut, "READ")
            raise AssertionError(f"round {rnd}: AXI read never returned R data")

        n_exp = len(exp) if many else BL_WORDS
        assert rd[:n_exp] == exp[:n_exp], \
            f"round {rnd}: AXI read-back {[hex(x) for x in rd[:n_exp]]} != {[hex(x) for x in exp[:n_exp]]}"
    dut._log.info("PASS: CSR init; AXI write burst -> DFI -> read burst back == written data, x%d",
                  roundtrips)


async def _csr_write(dut, addr, data):
    dut.s_cpuif_addr.value = addr
    dut.s_cpuif_wr_data.value = data
    dut.s_cpuif_wr_biten.value = 0xFFFFFFFF
    dut.s_cpuif_req_is_wr.value = 1
    dut.s_cpuif_req.value = 1
    for _ in range(100):
        await RisingEdge(dut.aclk)
        if int(dut.s_cpuif_wr_ack.value) or int(dut.s_cpuif_wr_err.value):
            break
    else:
        raise AssertionError(f"CSR write {addr:#x} never acked")
    dut.s_cpuif_req.value = 0
    dut.s_cpuif_req_is_wr.value = 0
    await RisingEdge(dut.aclk)


async def _csr_read(dut, addr):
    dut.s_cpuif_addr.value = addr
    dut.s_cpuif_req_is_wr.value = 0
    dut.s_cpuif_req.value = 1
    val = 0
    for _ in range(100):
        await RisingEdge(dut.aclk)
        if int(dut.s_cpuif_rd_ack.value) or int(dut.s_cpuif_rd_err.value):
            val = int(dut.s_cpuif_rd_data.value)
            break
    else:
        raise AssertionError(f"CSR read {addr:#x} never acked")
    dut.s_cpuif_req.value = 0
    await RisingEdge(dut.aclk)
    return val


async def _dump_probes(dut, phase):
    for _ in range(8):
        await RisingEdge(dut.aclk)
        snap = {}
        for s in ("s_axi_rvalid", "s_axi_rready", "s_axi_arvalid", "s_axi_arready",
                  "dfi_rddata_en_o", "dfi_rddata_valid_i", "dfi_wrdata_en_o",
                  "init_done_o", "s_cpuif_req_stall_rd", "s_cpuif_req_stall_wr"):
            try:
                snap[s] = int(getattr(dut, s).value)
            except Exception:
                snap[s] = None
        for s in ("w_ret_v", "w_ret_rdy", "w_wr_sch_v", "w_wr_commit_v",
                  "w_wr_commit_rdy", "w_cmd_v", "w_cmd_rdy"):
            try:
                snap[f"core.{s}"] = int(getattr(dut.u_core, s).value)
            except Exception:
                snap[f"core.{s}"] = None
        for s in ("r_wr_valid", "r_wr_fdone", "r_wr_sched"):
            try:
                snap[f"entry.{s}"] = int(getattr(dut.u_core.u_entry_store, s).value)
            except Exception:
                snap[f"entry.{s}"] = None
        for s in ("stall_noreq_o", "stall_banktimer_o", "stall_refresh_o"):
            try:
                snap[f"sched.{s}"] = int(getattr(dut.u_core.u_sched_plane, s).value)
            except Exception:
                snap[f"sched.{s}"] = None
        try:
            snap["core.ring.occ"] = int(dut.u_core.u_axi_plane.u_rd_ring.r_occ.value)
        except Exception:
            snap["core.ring.occ"] = None
        dut._log.info("HANG[%s] %s", phase, snap)


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
                beat_left = min(BURST_WORDS, len(rd_q))
            dut.dfi_rddata_valid_i.value = 0
        else:
            dut.dfi_rddata_i.value = rd_q.popleft()
            dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
            beat_left -= 1
            if beat_left == 0:
                state = "idle"


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_granite_top_geared(request, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_top_geared"
    test_name = f"cocotb_test_granite_top_geared_{test_level}"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32",
              "HOST_AXI_DATA_WIDTH": str(DW),
              "NUM_RANKS": "1", "NUM_BANKS": "8",
              "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": str(DFI_RATE), "DRAM_BEAT_WIDTH": str(DRAM_BEAT),
              "DRAM_DEVICE_WIDTH": str(DRAM_DEV), "DRAM_BL": str(BL),
              "NUM_ENTRIES": os.environ.get("GRANITE_NUM_ENTRIES", "1"),
              "RD_RET_DEPTH": "32", "CSR_ADDR_W": "16"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 **level_env(test_level)}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_granite_top_geared",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
