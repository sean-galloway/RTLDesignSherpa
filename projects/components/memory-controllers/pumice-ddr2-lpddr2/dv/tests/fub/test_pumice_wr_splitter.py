# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Pattern-B runner for `pumice_wr_splitter` (write-side burst splitter).

Directly exercises the AxLEN -> DRAM-burst mapping — the "one AXI burst maps to
an integer number of DRAM bursts" contract that was previously untested. The
splitter chops the host AW into CHUNK_BEATS-sized sub-commands (CHUNK_BEATS =
AXI beats per DRAM burst) and re-frames WLAST every CHUNK_BEATS beats.

  cocotb_test_wr_splitter_single  - AxLEN == CHUNK_BEATS-1  -> ONE sub-command,
                                    agg=0, last=1, one re-framed WLAST.
  cocotb_test_wr_splitter_split   - AxLEN == 2*CHUNK_BEATS-1 -> TWO sub-commands
                                    of CHUNK_BEATS, agg=1 on both, last only on
                                    the 2nd; WLAST re-framed every CHUNK_BEATS.
  cocotb_test_wr_splitter_ragged  - AxLEN not a multiple of CHUNK_BEATS -> a full
                                    sub-command + a RAGGED tail sub-command
                                    (< CHUNK_BEATS); the tail's WLAST is the
                                    host's own final beat. (The tail then SLVERRs
                                    at pumice_wr_intake — see that test.)
"""

import os
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_wr_splitter.f")

CHUNK_BEATS = 4          # AXI beats per DRAM burst (must match the param below)


async def _reset(dut):
    dut.aresetn.value = 0
    for sig in ("fub_awvalid", "fub_wvalid", "fub_wlast", "m_awready",
                "m_wready", "fub_awlen", "fub_wdata"):
        if hasattr(dut, sig):
            getattr(dut, sig).value = 0
    dut.m_awready.value = 1          # sink always ready
    dut.m_wready.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)


async def _drive_aw(dut, awlen):
    """Present one AW; hold until accepted."""
    dut.fub_awid.value = 3
    dut.fub_awaddr.value = 0x1000
    dut.fub_awlen.value = awlen
    dut.fub_awsize.value = 3
    dut.fub_awburst.value = 1
    dut.fub_awvalid.value = 1
    await RisingEdge(dut.aclk)
    while dut.fub_awready.value == 0:
        await RisingEdge(dut.aclk)
    dut.fub_awvalid.value = 0


async def _drive_w(dut, nbeats):
    """Stream nbeats W beats, host WLAST on the final beat."""
    for i in range(nbeats):
        dut.fub_wdata.value = 0xA0 + i
        dut.fub_wstrb.value = 0xFF          # AXI_DATA_WIDTH=64 -> SW=8
        dut.fub_wlast.value = 1 if i == nbeats - 1 else 0
        dut.fub_wvalid.value = 1
        await RisingEdge(dut.aclk)
        while dut.fub_wready.value == 0:
            await RisingEdge(dut.aclk)
    dut.fub_wvalid.value = 0
    dut.fub_wlast.value = 0


async def _collect(dut, n_subs_expected, n_wbeats_expected):
    """Run one burst; collect sub-commands (awlen, agg, last) + W-beat WLASTs."""
    subs = []
    wlasts = []

    async def mon_aw():
        while len(subs) < n_subs_expected:
            await RisingEdge(dut.aclk)
            if dut.m_awvalid.value == 1 and dut.m_awready.value == 1:
                subs.append((int(dut.m_awlen.value),
                             int(dut.m_aw_agg.value),
                             int(dut.m_aw_last.value)))

    async def mon_w():
        while len(wlasts) < n_wbeats_expected:
            await RisingEdge(dut.aclk)
            if dut.m_wvalid.value == 1 and dut.m_wready.value == 1:
                wlasts.append(int(dut.m_wlast.value))

    cocotb.start_soon(mon_aw())
    cocotb.start_soon(mon_w())
    return subs, wlasts


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_wr_splitter_single(dut):
    """AxLEN = CHUNK_BEATS-1 -> exactly one DRAM burst, no split."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    await _reset(dut)
    nbeats = CHUNK_BEATS
    subs, wlasts = await _collect(dut, 1, nbeats)
    cocotb.start_soon(_drive_aw(dut, nbeats - 1))
    await _drive_w(dut, nbeats)
    for _ in range(20):
        await RisingEdge(dut.aclk)
    assert len(subs) == 1, f"expected 1 sub-command, got {subs}"
    awlen, agg, last = subs[0]
    assert awlen == CHUNK_BEATS - 1, f"sub awlen {awlen} != {CHUNK_BEATS-1}"
    assert agg == 0, "single (unsplit) burst must NOT set agg"
    assert last == 1, "single burst must set last"
    assert wlasts.count(1) == 1 and wlasts[-1] == 1, \
        f"exactly one WLAST at the end, got {wlasts}"
    dut._log.info("PASS: AxLEN=%d -> 1 DRAM burst (no split)", nbeats - 1)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_wr_splitter_split(dut):
    """AxLEN = 2*CHUNK_BEATS-1 -> two DRAM bursts (integer multiple split)."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    await _reset(dut)
    nbeats = 2 * CHUNK_BEATS
    subs, wlasts = await _collect(dut, 2, nbeats)
    cocotb.start_soon(_drive_aw(dut, nbeats - 1))
    await _drive_w(dut, nbeats)
    for _ in range(20):
        await RisingEdge(dut.aclk)
    assert len(subs) == 2, f"expected 2 sub-commands, got {subs}"
    for i, (awlen, agg, last) in enumerate(subs):
        assert awlen == CHUNK_BEATS - 1, f"sub{i} awlen {awlen} != {CHUNK_BEATS-1}"
        assert agg == 1, f"sub{i} of a split must set agg"
        assert last == (1 if i == 1 else 0), f"sub{i} last wrong: {last}"
    # WLAST re-framed every CHUNK_BEATS: at beat CHUNK_BEATS-1 and 2*CHUNK_BEATS-1
    want = [1 if (j + 1) % CHUNK_BEATS == 0 else 0 for j in range(nbeats)]
    assert wlasts == want, f"WLAST re-framing {wlasts} != {want}"
    dut._log.info("PASS: AxLEN=%d -> 2 DRAM bursts (split)", nbeats - 1)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_wr_splitter_ragged(dut):
    """AxLEN not a multiple of CHUNK_BEATS -> full sub + ragged tail sub."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    await _reset(dut)
    nbeats = CHUNK_BEATS + 2          # 6: one full (4) + ragged tail (2)
    subs, wlasts = await _collect(dut, 2, nbeats)
    cocotb.start_soon(_drive_aw(dut, nbeats - 1))
    await _drive_w(dut, nbeats)
    for _ in range(20):
        await RisingEdge(dut.aclk)
    assert len(subs) == 2, f"expected 2 sub-commands (full+ragged), got {subs}"
    assert subs[0][0] == CHUNK_BEATS - 1, f"full sub awlen {subs[0][0]}"
    assert subs[1][0] == (nbeats - CHUNK_BEATS) - 1, \
        f"ragged tail awlen {subs[1][0]} != {(nbeats-CHUNK_BEATS)-1}"
    # tail is SHORTER than CHUNK_BEATS -> intake will SLVERR it (see wr_intake).
    want = [1 if (j + 1) % CHUNK_BEATS == 0 or j == nbeats - 1 else 0
            for j in range(nbeats)]
    assert wlasts == want, f"ragged WLAST {wlasts} != {want}"
    dut._log.info("PASS: AxLEN=%d -> full + ragged tail (intake SLVERRs tail)",
                  nbeats - 1)


# ---------------------------------------------------------------------------
# Pytest wrappers
# ---------------------------------------------------------------------------
def _run(request, testcase):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_wr_splitter"
    test_name = testcase

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "AXI_DATA_WIDTH": "64",
        "AXI_USER_WIDTH": "1", "CHUNK_BEATS": str(CHUNK_BEATS),
    }
    extra_env = {
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    extra_env.update(params)
    compile_args = ["+define+USE_ASYNC_RESET"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))), keep_files=True,
        timescale="1ns/1ps")


def test_pumice_wr_splitter_single(request):
    _run(request, "cocotb_test_wr_splitter_single")


def test_pumice_wr_splitter_split(request):
    _run(request, "cocotb_test_wr_splitter_split")


def test_pumice_wr_splitter_ragged(request):
    _run(request, "cocotb_test_wr_splitter_ragged")
