# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_master_stub
# Purpose: Test runner for APB5 master stub variant
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-23

"""
APB5 Master Stub Test Runner

Tests APB5 master stub with packed command/response interfaces.
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.apb5_master_stub_tb import APB5MasterStubBasicTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_master_stub_basic(dut):
    """Basic APB5 master stub test."""
    tb = APB5MasterStubBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Simulate slave side
    dut.m_apb_PREADY.value = 1
    dut.m_apb_PRDATA.value = 0xDEADBEEF
    dut.m_apb_PSLVERR.value = 0
    dut.m_apb_PWAKEUP.value = 0

    if hasattr(dut, 'm_apb_PRUSER'):
        dut.m_apb_PRUSER.value = 0xA
    if hasattr(dut, 'm_apb_PBUSER'):
        dut.m_apb_PBUSER.value = 0xB

    # Initialize command interface
    dut.cmd_valid.value = 0
    dut.cmd_data.value = 0

    # Response ready
    dut.rsp_ready.value = 1

    await tb.wait_clocks('pclk', 10)

    tb.log.info("=== APB5 Master Stub Basic Test PASSED ===")


def _pack_cmd(f, last, first, pwrite, addr, data):
    """Pack the stub's cmd_data: {last, first, pwrite, pprot, pstrb, paddr,
    pwdata, pauser, pwuser}, MSB first (see apb5_master_stub.sv)."""
    v = 0
    for val, w in ((last, 1), (first, 1), (pwrite, 1), (0, f['PW']),
                   ((1 << f['SW']) - 1, f['SW']), (addr, f['AW']),
                   (data, f['DW']), (0, f['AUW']), (0, f['WUW'])):
        v = (v << w) | (val & ((1 << w) - 1))
    return v


def _unpack_rsp(f, v):
    """Unpack rsp_data: {last, first, pslverr, prdata, pruser, pbuser}."""
    v >>= f['BUW'] + f['RUW']
    prdata = v & ((1 << f['DW']) - 1)
    v >>= f['DW'] + 1                   # prdata, pslverr
    first = v & 1
    last = (v >> 1) & 1
    return last, first, prdata


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_apb5_master_stub_framing(dut):
    """Issue #111: every response must carry ITS command's {last, first}.

    Phase 1 holds rsp_ready low so several commands are accepted before any
    response is consumed, then moves cmd_data to unrelated framing and drains.
    Phase 2 streams commands under random response backpressure, changing
    cmd_data the cycle after each acceptance. The slave returns PRDATA =
    PADDR so the response order is checked too.
    """
    tb = APB5MasterStubBasicTB(dut)
    await tb.setup_clocks_and_reset()

    dw = int(os.environ['TEST_DATA_WIDTH'])
    auw = int(os.environ['TEST_AUSER_WIDTH'])
    f = dict(AW=int(os.environ['TEST_ADDR_WIDTH']), DW=dw, SW=dw // 8, PW=3,
             AUW=auw, WUW=auw, RUW=auw, BUW=auw)
    level = os.environ.get('TEST_LEVEL', 'func').lower()
    n_stream = {'gate': 8, 'func': 32, 'full': 128}.get(level, 32)

    dut.m_apb_PREADY.value = 1
    dut.m_apb_PSLVERR.value = 0
    if hasattr(dut, 'm_apb_PRUSER'):
        dut.m_apb_PRUSER.value = 0
    if hasattr(dut, 'm_apb_PBUSER'):
        dut.m_apb_PBUSER.value = 0
    dut.cmd_valid.value = 0
    dut.cmd_data.value = 0
    dut.rsp_ready.value = 0

    async def slave_echo():
        # PRDATA follows PADDR so each response identifies its command.
        while True:
            await RisingEdge(dut.pclk)
            dut.m_apb_PRDATA.value = int(dut.m_apb_PADDR.value) & ((1 << dw) - 1)
    cocotb.start_soon(slave_echo())

    async def send(cmds):
        for (last, first, addr) in cmds:
            dut.cmd_data.value = _pack_cmd(f, last, first, 0, addr, 0)
            dut.cmd_valid.value = 1
            while True:
                await RisingEdge(dut.pclk)
                if int(dut.cmd_ready.value):
                    break
            # Move cmd_data immediately: the bug paired responses with
            # whatever framing was presented on the live input.
            dut.cmd_data.value = _pack_cmd(f, 1 - last, 1 - first, 1, 0x3F0, 0)
            dut.cmd_valid.value = 0

    errors = []

    async def collect(expected, backpressure):
        got = 0
        while got < len(expected):
            dut.rsp_ready.value = (random.random() > 0.4) if backpressure else 1
            await RisingEdge(dut.pclk)
            if int(dut.rsp_valid.value) and int(dut.rsp_ready.value):
                last, first, prdata = _unpack_rsp(f, int(dut.rsp_data.value))
                e_last, e_first, e_addr = expected[got]
                if (last, first) != (e_last, e_first) or prdata != e_addr:
                    errors.append(
                        f"rsp {got}: got last={last} first={first} prdata=0x{prdata:X}, "
                        f"want last={e_last} first={e_first} prdata=0x{e_addr:X}")
                got += 1
        dut.rsp_ready.value = 0

    # Phase 1: queue four commands with distinct framing, then drain.
    p1 = [(0, 1, 0x010), (0, 0, 0x020), (1, 0, 0x030), (1, 1, 0x040)]
    await send(p1)
    await tb.wait_clocks('pclk', 20)            # let APB finish all four
    await collect(p1, backpressure=False)

    # Phase 2: stream with random response backpressure.
    p2 = [(random.randint(0, 1), random.randint(0, 1), 0x100 + 4 * i)
          for i in range(n_stream)]
    collector = cocotb.start_soon(collect(p2, backpressure=True))
    await send(p2)
    await collector

    for e in errors[:10]:
        tb.log.error(e)
    assert not errors, f"{len(errors)} response(s) carried the wrong framing (issue #111)"
    tb.log.info(f"=== framing test PASSED: {len(p1) + len(p2)} responses checked ===")


def generate_apb5_master_stub_params():
    """Generate test parameters for APB5 master stub."""
    return [
        (12, 32, 4, 0),  # Basic
        (16, 32, 8, 0),  # 16-bit address
        (12, 64, 4, 1),  # With parity
    ]


def _run_apb5_master_stub(addr_width, data_width, auser_width, enable_parity, testcase, tag):
    """APB5 master stub test runner (one exact cocotb testcase per run)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_master_stub"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module='apb5_master_stub')

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    pr_str = 'pr' if enable_parity else 'np'
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_apb5_master_stub_{tag}aw{aw_str}_dw{dw_str}_au{au_str}_{pr_str}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes=includes

    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AUSER_WIDTH': str(auser_width),
        'WUSER_WIDTH': str(auser_width),
        'RUSER_WIDTH': str(auser_width),
        'BUSER_WIDTH': str(auser_width),
        'ENABLE_PARITY': str(enable_parity),
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AUSER_WIDTH': str(auser_width),
        'TEST_ENABLE_PARITY': str(enable_parity),
        'TEST_LEVEL': os.environ.get('REG_LEVEL', 'FUNC').lower(),
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
            testcase=testcase,
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, enable_parity",
    generate_apb5_master_stub_params()
)
def test_apb5_master_stub(request, addr_width, data_width, auser_width, enable_parity):
    """Basic smoke run."""
    _run_apb5_master_stub(addr_width, data_width, auser_width, enable_parity,
                          "cocotb_test_apb5_master_stub_basic", "")


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, enable_parity",
    generate_apb5_master_stub_params()
)
def test_apb5_master_stub_framing(request, addr_width, data_width, auser_width, enable_parity):
    """Issue #111: response first/last framing follows its own command."""
    _run_apb5_master_stub(addr_width, data_width, auser_width, enable_parity,
                          "cocotb_test_apb5_master_stub_framing", "framing_")
