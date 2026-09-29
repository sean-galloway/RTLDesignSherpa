# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B integration runner for `pumice_axi4_ifc`."""

import os
import sys
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_axi4_ifc_tb import PumiceAxi4IfcTB  # noqa: E402
from tbclasses.pumice_levels import depth as _profile_depth  # noqa: E402

_FILELIST = ("projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/"
             "rtl/filelists/macro/pumice_axi4_ifc.f")


@cocotb.test(timeout_time=8, timeout_unit="ms")
async def cocotb_test_pumice_axi4_ifc(dut):
    tb = PumiceAxi4IfcTB(dut)
    await tb.setup_clocks_and_reset()
    N = tb.EXP_BEATS

    # The write/snarf/cross-id/miss/commit scenario ends with the CAM drained
    # and every response collected, so it repeats cleanly; each round uses
    # fresh, BL-aligned addresses with distinct decode keys and fresh data.
    rounds = _profile_depth('axi4_ifc_rounds')
    # The wrapper reads TEST_LEVEL itself, beside its knob: bin/review/check_test_levels.py
    # follows only TBClasses/projects imports, and this area imports tbclasses.* (a
    # hyphenated component path cannot be a package import), so a read hidden inside
    # pumice_levels.depth() would be invisible to the gate. Forced, not chosen (BUG-004).
    tb.log.info("depth: TEST_LEVEL=%s axi4_ifc_rounds=%d",
                os.environ.get("TEST_LEVEL", "gate"), rounds)
    for rnd in range(rounds):
        await _round(tb, N, rnd)

    tb.log.info("PASS: write->same-id snarf-read (DX), cross-id read via DFI (DXX), "
                "miss-read via DFI (DY), commit cm_rd (DX) + commit-driven B(id3)")


async def _round(tb, N, rnd):
    DX  = [0xAA00 + 0x100 * rnd + i for i in range(N)]
    DY  = [0xBB00 + 0x100 * rnd + i for i in range(N)]
    DXX = [0xCC00 + 0x100 * rnd + i for i in range(N)]   # DFI-fed data for the cross-id read
    X = 0x1000 * (2 * rnd + 1)       # BL-aligned, distinct decode keys (0x1000, 0x3000, ...)
    Y = 0x1000 * (2 * rnd + 2)       #                                  (0x2000, 0x4000, ...)
    n_b0 = len(tb.b_ids)             # B strobes seen before this round

    # 1. host write to X (id 3) -> lands in wr CAM. B is commit-driven, so NOT yet.
    await tb.write(X, wid=3, data=DX)
    await tb.wait_clocks('aclk', 12)
    assert len(tb.b_ids) == n_b0, "B fired before commit (should be commit-driven)"

    # 2. host read to X with the SAME id (3) -> SNARF hit -> R == DX (uncommitted).
    #    Snarf is now limited to same-id, matching-length, unscheduled writes.
    await tb.read_ar(X, rid=3)
    r = await tb.wait_r()
    assert r is not None, "no R for snarf read"
    assert [b[1] for b in r] == DX, f"snarf R data {[b[1] for b in r]} != {DX}"
    assert all(b[0] == 3 for b in r), "snarf R id != 3"
    assert r[-1][2] == 1, "snarf R last not set on final beat"

    # 2b. host read to X with a DIFFERENT id (5) -> must NOT snarf (cross-id has no
    #     AXI ordering); it takes the MISS/DFI path and returns the DFI-fed data.
    await tb.read_ar(X, rid=5)
    await tb.service_rd(DXX)
    r = await tb.wait_r()
    assert r is not None, "no R for cross-id read"
    assert [b[1] for b in r] == DXX, f"cross-id read must use DFI path, got {[b[1] for b in r]}"
    assert all(b[0] == 5 for b in r), "cross-id R id != 5"

    # 3. host read to Y (unwritten) -> MISS -> scheduler issues + DFI returns DY
    await tb.read_ar(Y, rid=6)
    await tb.service_rd(DY)
    r = await tb.wait_r()
    assert r is not None, "no R for miss read"
    assert [b[1] for b in r] == DY, f"miss R data {[b[1] for b in r]} != {DY}"
    assert all(b[0] == 6 for b in r), "miss R id != 6"

    # 4. commit the write -> cm_rd stream == DX, and B(id=3) now fires
    cm = await tb.commit_wr()
    assert cm == DX, f"commit cm_rd {cm} != {DX}"
    for _ in range(200):
        if len(tb.b_ids) > n_b0:
            break
        await tb.wait_clocks('aclk', 1)
    assert len(tb.b_ids) == n_b0 + 1 and tb.b_ids[-1] == 3, \
        f"round {rnd}: B ids {list(tb.b_ids)[n_b0:]} != [3]"


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_pumice_axi4_ifc(request, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_axi4_ifc"
    test_name = f"cocotb_test_pumice_axi4_ifc_{test_level}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "AXI_ID_WIDTH":   "8",
        "AXI_ADDR_WIDTH": "32",
        "AXI_DATA_WIDTH": "64",
        "DRAM_BEAT_WIDTH": "64",
        "NUM_BANKS":      "8",
        "ROW_WIDTH":      "14",
        "COL_WIDTH":      "10",
        "BYTE_OFFSET_WIDTH": "3",
        "AXI_BEATS_PER_BURST":             "4",
        "NUM_ENTRIES":    "8",
        "N_SRAM_SLOTS":   "8",
        "N_SCHED_LU":     "4",
    }
    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        **level_env(test_level),
    }
    extra_env.update(params)

    compile_args = ["+define+USE_ASYNC_RESET"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_pumice_axi4_ifc",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        timescale="1ns/1ps",
    )
