# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_mode_register` -- MR0-MR6 images and derived outputs.

Authority split (MAS ch02 03_mode_register.md): image storage and readback
are absolute; the six review-verified bit selects are asserted absolutely;
the Q1-placeholder selects are asserted relative to the shared constants in
the tbclass (wiring test -- Q1 changes one constant on both sides, per the
HAS Q1 recording).
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_mode_register_tb import (  # noqa: E402
    AndesiteModeRegisterTB, Q1_MR5_RD_DBI_BIT, Q1_MR5_WR_DBI_BIT,
    Q1_MR3_MPR_PAGE_LSB,
)


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_andesite_mode_register(dut):
    tb = AndesiteModeRegisterTB(dut)
    await tb.setup_clock()
    await tb.reset()

    # Reset posture: images clear, derived outputs at zero.
    for addr in range(7):
        assert await tb.read_mr(addr) == 0, f"MR{addr} must read 0 out of reset"
    assert int(dut.fgr_factor_o.value) == 0
    assert int(dut.rtt_nom_o.value) == 0
    assert int(dut.rtt_wr_o.value) == 0
    assert int(dut.rtt_park_o.value) == 0
    assert int(dut.ca_parity_lat_o.value) == 0
    assert int(dut.wrlvl_en_o.value) == 0

    # Round-trip every DDR4 MR image.
    for addr, data in enumerate([0x05, 0x12, 0x2A, 0xC4, 0x08, 0x96, 0x3F]):
        await tb.write_mr(addr, data)
        assert await tb.read_mr(addr) == data, f"MR{addr} round-trip failed"

    # Review-verified derivations (absolute).
    await tb.write_mr(3, 0x0002 << 6)          # MR3[8:6] = 2 (3'b010 = 4x) -> FGR
    assert int(dut.fgr_factor_o.value) == 2, "FGR factor must decode MR3[8:6]"
    await tb.write_mr(3, 0x0007 << 6)          # illegal 3'b111 clamps to 4x
    assert int(dut.fgr_factor_o.value) == 2, "illegal FGR encoding clamps to 4x"
    await tb.write_mr(1, 0x0005 << 8)          # MR1[10:8] = 5 -> RTT_NOM
    assert int(dut.rtt_nom_o.value) == 5, "RTT_NOM must decode MR1[10:8]"
    await tb.write_mr(2, 0x0003 << 9)          # MR2[11:9] = 3 -> RTT_WR
    assert int(dut.rtt_wr_o.value) == 3, "RTT_WR must decode MR2[11:9]"
    await tb.write_mr(5, (0x0001 << 6) | 0x0005)  # MR5[8:6]=1 park, [2:0]=5 parity
    assert int(dut.rtt_park_o.value) == 1, "RTT_PARK must decode MR5[8:6]"
    # Wiring check only: the output is the [1:0] slice of MR5[2:0]; the
    # encoding-to-latency map itself is Q1 (cold-storage read).
    assert int(dut.ca_parity_lat_o.value) == 1, "parity latency output tracks MR5[1:0] slice"
    await tb.write_mr(1, (0x0005 << 8) | (1 << 7))  # MR1[7] write leveling
    assert int(dut.wrlvl_en_o.value) == 1, "write leveling must decode MR1[7]"

    # Q1-placeholder derivations (relative to the shared constants).
    await tb.write_mr(5, (1 << Q1_MR5_RD_DBI_BIT) | (1 << Q1_MR5_WR_DBI_BIT))
    assert int(dut.rd_dbi_en_o.value) == 1, "rd_dbi_en must track image[Q1 bit]"
    assert int(dut.wr_dbi_en_o.value) == 1, "wr_dbi_en must track image[Q1 bit]"
    await tb.write_mr(3, (0x2 << Q1_MR3_MPR_PAGE_LSB))
    assert int(dut.mpr_page_o.value) == 2, "mpr_page must decode image[Q1 field]"

    # MRS command presentation: registered copy of the last write.
    await tb.write_mr(6, 0x00AB)
    assert int(dut.mr_sel_o.value) == 6, "mr_sel_o presents the written MR index"
    assert int(dut.mr_data_o.value) == 0x00AB, "mr_data_o presents the written image"


@pytest.mark.parametrize("seed", [None])
def test_andesite_mode_register(seed):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_mode_register"
    test_name = "test_andesite_mode_register"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_mode_register.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_mode_register",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
