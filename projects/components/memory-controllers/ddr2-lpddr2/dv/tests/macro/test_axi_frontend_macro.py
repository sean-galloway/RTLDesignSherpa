# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-17

"""
Test runner for axi_frontend_macro.

Methodology mirrors stream's macro-level test runners (e.g.,
projects/components/stream/dv/tests/macro/test_datapath_rd_test.py):

  - pytest parametrize generates the test matrix
  - cocotb_test.simulator.run invokes Verilator/Icarus
  - One cocotb test function dispatches to per-TEST_TYPE handlers
  - TB class encapsulates DUT interactions (see tbclasses/)

Test types (initial set):
  - smoke         : push one AW, push a matching AR -> expect forward hit
  - miss          : push one AW, push a non-matching AR -> expect rd push
  - partial_strb  : AW with full_strb=0, matching AR -> expect rd push
  - len_mismatch  : AW for 8 beats, AR for 4 beats -> expect rd push
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add the component's dv/ directory to sys.path so `tbclasses.*` is importable.
# Hyphens in the path (memory-controllers, ddr2-lpddr2) preclude a dotted-import
# from repo root, so we keep the import root-relative to the component dv dir.
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.axi_frontend_macro_tb import (  # noqa: E402
    AxiFrontendMacroTB,
    WriteEntry,
)


# ---------------------------------------------------------------------------
# CocoTB top-level test (dispatches by TEST_TYPE)
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_axi_frontend(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    log = logging.getLogger("axi_frontend_test")
    log.info(f"TEST_TYPE = {test_type}")

    tb = AxiFrontendMacroTB(dut)
    await tb.setup()

    if test_type == "smoke":
        await _run_smoke(tb)
    elif test_type == "miss":
        await _run_miss(tb)
    elif test_type == "partial_strb":
        await _run_partial_strb(tb)
    elif test_type == "len_mismatch":
        await _run_len_mismatch(tb)
    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


# ---------------------------------------------------------------------------
# Test scenarios
# ---------------------------------------------------------------------------

async def _run_smoke(tb):
    """Push one AW; push a same-address AR with same length and full_strb.
    Expect: forward hit (no rd CAM push)."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=4,
                    w_buf_ptr=0, strb_ptr=0, full_strb=True)
    aw_slot = await tb.push_aw(aw)

    # Let snapshot stabilize one cycle before driving the AR
    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "forward", f"expected forward, got {outcome}"
    assert outcome["src_slot"] == aw_slot, \
        f"src_slot {outcome['src_slot']} != aw_slot {aw_slot}"
    assert outcome["w_buf_ptr"] == aw.w_buf_ptr, \
        f"w_buf_ptr {outcome['w_buf_ptr']} != aw.w_buf_ptr {aw.w_buf_ptr}"
    assert await tb.rd_cam_occupancy() == 0, "rd CAM should be empty on forward hit"
    assert await tb.wr_cam_occupancy() == 1, "wr CAM should hold the in-flight write"
    tb.log.info("smoke PASS")


async def _run_miss(tb):
    """Push one AW; push a different-address AR. Expect: rd CAM push."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=4,
                    w_buf_ptr=0, strb_ptr=0, full_strb=True)
    await tb.push_aw(aw)

    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_8080, axi_id=5, length=4)
    assert outcome["kind"] == "rd_push", f"expected rd_push, got {outcome}"
    assert await tb.rd_cam_occupancy() == 1, "rd CAM should hold the read"
    assert await tb.wr_cam_occupancy() == 1, "wr CAM still holds the write"
    tb.log.info("miss PASS")


async def _run_partial_strb(tb):
    """AW with full_strb=False; matching AR. Expect: rd CAM push (no forward)."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=4,
                    w_buf_ptr=0, strb_ptr=0, full_strb=False)
    await tb.push_aw(aw)

    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "rd_push", \
        f"partial-strb writes must NOT forward; got {outcome}"
    tb.log.info("partial_strb PASS")


async def _run_len_mismatch(tb):
    """AW for 8 beats; AR for 4 beats. Expect: rd CAM push (no forward)."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=8,
                    w_buf_ptr=0, strb_ptr=0, full_strb=True)
    await tb.push_aw(aw)

    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "rd_push", \
        f"length mismatch must NOT forward; got {outcome}"
    tb.log.info("len_mismatch PASS")


# ---------------------------------------------------------------------------
# Pytest wrapper
# ---------------------------------------------------------------------------

params = [
    "smoke",
    "miss",
    "partial_strb",
    "len_mismatch",
]


@pytest.mark.parametrize("test_type", params)
def test_axi_frontend_macro(request, test_type):
    """Pytest wrapper for the axi_frontend_macro tests."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi_frontend_macro"
    test_name = f"test_axi_frontend_macro_{test_type}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/macro/axi_frontend_macro.f"
    )
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path
    )

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)

    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED": str(random.randint(0, 100000)),
        "TEST_TYPE": test_type,
    }

    # Enable waves with WAVES=1
    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace", "--trace-structs"]
        extra_env["VERILATOR_TRACE"] = "1"

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_axi_frontend",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args,
        plus_args=plus_args,
        timescale="1ns/1ps",
    )
