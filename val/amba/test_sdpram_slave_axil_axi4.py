# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_sdpram_slave_axil_axi4
# Purpose: Coverage for rtl/amba/shared/sdpram_slave_axil_axi4.sv -- AXIL4
#          write slave + AXI4 read slave over the shared sdpram_core.
#
# All driver/monitor logic lives in the shared
# TBClasses.amba.sdpram_slave_mixed_tb.SdpramSlaveMixedTB class (RDS-DV
# AXI4/AXIL4 master factories -- no hand-rolled signal pokes). This file is
# a thin pytest/cocotb wrapper.
#
# Subsystem: tests
# Author: sean galloway

import os
import random

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.amba.sdpram_slave_mixed_tb import SdpramSlaveMixedTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_sdpram_slave_axil_axi4(dut):
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    tb = SdpramSlaveMixedTB(dut, wr_protocol="AXIL", rd_protocol="AXI4",
                             aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.setup_clocks_and_reset()

    tb.log.info(f"sdpram_slave_axil_axi4: TEST_LEVEL={test_level}")
    await tb.run_standard_suite(test_level=test_level)
    tb.log.info("ALL PHASES PASSED")


# ============================================================================
# pytest wrapper
# ============================================================================

def generate_sdpram_axil_axi4_params():
    """REG_LEVEL -> (test_level, data_width, mem_depth) rows.

    GATE: 1 row (quick smoke).
    FUNC/FULL: 3 rows -- gate/func at DATA_WIDTH=64, full at DATA_WIDTH=256.
    mem_depth is held >=64 across all rows: phase_axi4_write_burst /
    phase_axi4_read_burst use fixed word offsets up to index 40.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [('gate', 64, 64)]
    return [('gate', 64, 64), ('func', 64, 64), ('full', 256, 64)]


@pytest.mark.parametrize("test_level,data_width,mem_depth", generate_sdpram_axil_axi4_params())
def test_sdpram_slave_axil_axi4(request, test_level, data_width, mem_depth):
    """Pytest wrapper -- exercises sdpram_slave_axil_axi4 (AXIL wr / AXI4 rd)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, _ = get_paths({})

    dut_name = "sdpram_slave_axil_axi4"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    tag = f"{worker_id}_{dut_name}_dw{data_width}_d{mem_depth}_{test_level}_{reg_level}"
    log_path = os.path.join(log_dir, f'test_{tag}.log')
    sim_build = sim_build_path(tests_dir, f'test_{tag}')
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/sdpram_slave_axil_axi4.f")

    parameters = {
        "AXI_ID_WIDTH": 4,
        "ADDR_WIDTH":   32,
        "DATA_WIDTH":   data_width,
        "USER_WIDTH":   1,
        "MEM_DEPTH":    mem_depth,
    }

    extra_env = {
        "DUT_DATA_WIDTH": str(data_width),
        "DUT_MEM_DEPTH":  str(mem_depth),
        "DUT_ADDR_WIDTH": "32",
        "DUT_ID_WIDTH":   "4",
        "LOG_PATH":       log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "TEST_LEVEL":     test_level,
        "SEED":           os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, tag)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_sdpram_slave_axil_axi4",
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator=os.environ.get("SIM", "verilator"),
            keep_files=True,
            compile_args=[
                "-Wno-WIDTHEXPAND",
                "-Wno-WIDTHTRUNC",
                "-Wno-TIMESCALEMOD",
                "-Wno-DECLFILENAME",
                "-Wno-UNUSED",
                "-Wno-UNUSEDPARAM",
                "-Wno-CASEINCOMPLETE",
            ],
        )
    except Exception:
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
