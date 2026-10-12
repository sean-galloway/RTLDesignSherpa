# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Reproduce the axi4_to_axil4_rd combinational-response outstanding-count bug.

import os
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb.clock import Clock
from cocotb_test.simulator import run

repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..', '..', '..'))

from TBClasses.shared.utilities import create_view_cmd, sim_build_path
from TBClasses.shared.test_levels import reg_level_grid, level_env


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def combo_read_two_beats(dut):
    """Two back-to-back reads with a combinational AXIL slave.

    The first read returns data, but the converter's r_rd_outstanding flag
    stays high when AR and R happen in the same cycle. The second read then
    hangs because s_axi_arready is forced low.
    """
    clk = dut.aclk
    cocotb.start_soon(Clock(clk, 10, units='ns').start())

    dut.s_axi_arvalid.value = 0
    dut.s_axi_araddr.value = 0
    dut.s_axi_arlen.value = 0
    dut.s_axi_rready.value = 1
    dut.aresetn.value = 0
    for _ in range(5):
        await RisingEdge(clk)
    dut.aresetn.value = 1
    for _ in range(2):
        await RisingEdge(clk)

    # First read at address 0x1234_0000.
    dut.s_axi_araddr.value = 0x1234_0000
    dut.s_axi_arlen.value = 0
    dut.s_axi_arvalid.value = 1
    await RisingEdge(clk)
    while not int(dut.s_axi_arready.value):
        await RisingEdge(clk)
    dut.s_axi_arvalid.value = 0

    # Wait for the first R handshake.
    while not (int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value)):
        await RisingEdge(clk)
    rdata0 = int(dut.s_axi_rdata.value)
    dut._log.info(f"first read rdata=0x{rdata0:08x} outstanding={int(dut.probe_rd_outstanding.value)}")

    # Deassert rready for one cycle to let the slave idle, then try a second read.
    dut.s_axi_rready.value = 0
    await RisingEdge(clk)
    dut.s_axi_rready.value = 1

    dut.s_axi_araddr.value = 0x5678_0000
    dut.s_axi_arlen.value = 0
    dut.s_axi_arvalid.value = 1

    timeout = 50
    for i in range(timeout):
        await RisingEdge(clk)
        if int(dut.s_axi_arready.value):
            break
    else:
        outstanding = int(dut.probe_rd_outstanding.value)
        raise AssertionError(
            f"second read hung: arready never asserted, r_rd_outstanding={outstanding}"
        )

    dut.s_axi_arvalid.value = 0
    while not (int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value)):
        await RisingEdge(clk)
    rdata1 = int(dut.s_axi_rdata.value)
    dut._log.info(f"second read rdata=0x{rdata1:08x}")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi4_to_axil4_rd_combo(request, test_level):
    module = "test_axi4_to_axil4_rd_combo"
    dut_name = "axi4_to_axil4_rd_combo_tb"
    toplevel = dut_name

    dv_root = os.path.join(
        repo_root, "projects", "components", "utility-ip", "converters", "dv")
    log_dir = os.path.join(dv_root, "tests", "log")
    tests_dir = os.path.join(dv_root, "tests")
    test_name = f"{module}_{test_level}"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    verilog_sources = [
        os.path.join(dv_root, "axi4_to_axil4_rd_combo_tb.sv"),
        os.path.join(repo_root, "rtl", "amba", "includes", "reset_defs.svh"),
        os.path.join(repo_root, "projects", "components", "utility-ip", "converters", "rtl", "axi4_to_axil4_rd.sv"),
    ]
    includes = [os.path.join(repo_root, "rtl", "amba", "includes")]

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': '600000',
        **level_env(test_level),
    }

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    compile_args = [
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",
    ]

    run(
        python_search=[tests_dir, repo_root],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
        keep_files=True,
        compile_args=compile_args,
    )
