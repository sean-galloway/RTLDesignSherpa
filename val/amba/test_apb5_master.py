# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_master
# Purpose: Test runner for APB5 master with AMBA5 extensions
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Master Test Runner

Tests APB5 master functionality with AMBA5 extensions:
- User signals (PAUSER, PWUSER)
- Wake-up signaling (PWAKEUP)
- Parity support (optional)
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.apb5_wakeup import check_requester_pwakeup
from TBClasses.amba.apb5_master_tb import APB5MasterBasicTB
from TBClasses.amba.apb5_parity import APB5Parity
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_master_basic(dut):
    """Basic APB5 master test - verifies command to APB transaction conversion."""
    tb = APB5MasterBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Simulate slave side (drive PREADY high for quick response)
    dut.m_apb_PREADY.value = 1
    dut.m_apb_PRDATA.value = 0xDEADBEEF
    dut.m_apb_PSLVERR.value = 0

    # Drive APB5 slave response signals if available
    if hasattr(dut, 'm_apb_PRUSER'):
        dut.m_apb_PRUSER.value = 0xA
    if hasattr(dut, 'm_apb_PBUSER'):
        dut.m_apb_PBUSER.value = 0xB

    await tb.wait_clocks('pclk', 5)

    # Test 1: Basic write
    tb.log.info("=== Test 1: Basic Write ===")
    await tb.drive_command(pwrite=1, paddr=0x100, pwdata=0x12345678, pauser=0x5, pwuser=0x3)
    success = await tb.wait_for_transaction()
    assert success, "Write transaction timeout"
    await tb.wait_clocks('pclk', 10)

    # Test 2: Basic read
    tb.log.info("=== Test 2: Basic Read ===")
    await tb.drive_command(pwrite=0, paddr=0x100, pauser=0x7)
    success = await tb.wait_for_transaction()
    assert success, "Read transaction timeout"
    await tb.wait_clocks('pclk', 10)

    # Test 3: Multiple transactions
    tb.log.info("=== Test 3: Multiple Transactions ===")
    for i in range(5):
        pwrite = i % 2
        paddr = 0x200 + (i * 4)
        pwdata = 0xABCD0000 + i
        pauser = i & 0xF
        pwuser = (i + 1) & 0xF

        await tb.drive_command(pwrite=pwrite, paddr=paddr, pwdata=pwdata,
                              pauser=pauser, pwuser=pwuser)
        success = await tb.wait_for_transaction()
        assert success, f"Transaction {i} timeout"
        await tb.wait_clocks('pclk', 5)

    tb.log.info("=== APB5 Master Basic Test PASSED ===")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_master_rsp_backpressure(dut):
    """TASK-068 witness: PENABLE must never be held past a completed transfer.

    Ported in spirit from apb4_master's equivalent. The unfixed apb5_master
    launched on r_cmd_valid alone and, on PREADY with a full response skid,
    sat in ACCESS still asserting PSEL and PENABLE. Against the always-ready
    slave this TB models that is not a wedge -- it is worse: the slave sees a
    completed transfer on every held cycle, so one command is executed many
    times over.

    APB completes a transfer when PSEL && PENABLE && PREADY. The FSM must then
    leave ACCESS, so PENABLE cannot still be high on the next edge with PREADY
    still high. This watches for that and stalls the response consumer to
    provoke it. Commands are driven inline rather than through
    drive_command(), which blocks on cmd_ready and would deadlock here once
    the stalled master backs the command skid up.
    """
    tb = APB5MasterBasicTB(dut)
    await tb.setup_clocks_and_reset()

    dut.m_apb_PREADY.value = 1
    dut.m_apb_PRDATA.value = 0xDEADBEEF
    dut.m_apb_PSLVERR.value = 0

    violations = 0
    completions = 0

    async def watch_bus():
        nonlocal violations, completions
        prev_completed = False
        while True:
            await RisingEdge(dut.pclk)
            completed = bool(dut.m_apb_PSEL.value and dut.m_apb_PENABLE.value
                             and dut.m_apb_PREADY.value)
            if completed:
                completions += 1
                if prev_completed:
                    violations += 1
            prev_completed = completed

    cocotb.start_soon(watch_bus())

    # Stall the response consumer, then push commands in without blocking.
    dut.rsp_ready.value = 0
    for i in range(12):
        waited = 0
        while not dut.cmd_ready.value and waited < 8:
            await RisingEdge(dut.pclk)
            waited += 1
        if not dut.cmd_ready.value:
            break          # skid full: enough is in flight to provoke the bug
        dut.cmd_valid.value = 1
        dut.cmd_pwrite.value = 1
        dut.cmd_paddr.value = 0x400 + i * 4
        dut.cmd_pwdata.value = 0xC0DE0000 + i
        dut.cmd_pstrb.value = 0xF
        await RisingEdge(dut.pclk)
        dut.cmd_valid.value = 0

    await tb.wait_clocks('pclk', 60)
    dut.rsp_ready.value = 1
    await tb.wait_clocks('pclk', 200)

    assert violations == 0, (
        f"PENABLE held asserted across {violations} completed transfer(s) "
        f"({completions} bus completions seen). The FSM stayed in ACCESS with "
        f"a full response skid, so the slave re-executed the transfer.")


@cocotb.test(timeout_time=400, timeout_unit="us")
async def cocotb_test_apb5_master_parity(dut):
    """IHI 0024E ch. 5 interface parity, requester side (issue #102 item 1).

    Checks every cycle that each requester *CHK the master drives is ODD
    parity over the spec's coverage set at the spec's granularity (one bit
    per byte on PADDR/PWDATA/PAUSER/PWUSER, PCTRLCHK over PPROT+PWRITE,
    PSTRBCHK over PSTRB, inversion on PSEL/PENABLE) while its Check Enable
    term holds. Then corrupts each completer *CHK in turn and requires the
    matching error flag -- and only that one -- to fire. The pre-#102 RTL
    computed EVEN parity, so the first transfer fails the requester check.
    """
    tb = APB5MasterBasicTB(dut)
    if os.environ.get('TEST_ENABLE_PARITY', '0') != '1':
        tb.log.info("ENABLE_PARITY=0: parity test not applicable")
        return
    par = APB5Parity(dut, 'm_apb_', tb.ADDR_WIDTH, tb.DATA_WIDTH,
                     auser_width=tb.AUSER_WIDTH, wuser_width=tb.WUSER_WIDTH,
                     ruser_width=tb.RUSER_WIDTH, buser_width=tb.BUSER_WIDTH)
    rng = random.Random(int(os.environ.get('SEED', '1')))
    dw_mask = (1 << tb.DATA_WIDTH) - 1

    await tb.setup_clocks_and_reset()
    dut.m_apb_PREADY.value = 1
    dut.m_apb_PRDATA.value = 0
    dut.m_apb_PSLVERR.value = 0
    dut.m_apb_PRUSER.value = 0
    dut.m_apb_PBUSER.value = 0
    par.start_driver(APB5Parity.COMPLETER, dut.pclk)

    req_errors = []      # (time, [names]) requester checks the DUT got wrong
    flag_hits = set()    # error flags seen during the current window
    checked = {'cycles': 0}

    async def watch():
        while True:
            await FallingEdge(dut.pclk)
            bad = par.mismatches(APB5Parity.REQUESTER)
            if bad:
                req_errors.append((get_sim_time('ns'), bad))
            if int(dut.m_apb_PSEL.value):
                checked['cycles'] += 1
            if int(dut.parity_error_rdata.value):
                flag_hits.add('rdata')
            if int(dut.parity_error_ctrl.value):
                flag_hits.add('ctrl')

    cocotb.start_soon(watch())

    async def one_xfer(pwrite):
        dut.m_apb_PRDATA.value = rng.getrandbits(tb.DATA_WIDTH) & dw_mask
        dut.m_apb_PRUSER.value = rng.getrandbits(tb.RUSER_WIDTH)
        dut.m_apb_PBUSER.value = rng.getrandbits(tb.BUSER_WIDTH)
        dut.m_apb_PSLVERR.value = rng.getrandbits(1)
        dut.cmd_pprot.value = rng.getrandbits(3)
        await tb.drive_command(
            pwrite=pwrite,
            paddr=rng.getrandbits(tb.ADDR_WIDTH),
            pwdata=rng.getrandbits(tb.DATA_WIDTH),
            pstrb=rng.getrandbits(tb.DATA_WIDTH // 8),
            pauser=rng.getrandbits(tb.AUSER_WIDTH),
            pwuser=rng.getrandbits(tb.WUSER_WIDTH))
        assert await tb.wait_for_transaction(), "transfer timeout"
        await tb.wait_clocks('pclk', 2)

    # Phase 1: clean traffic. Requester checks must be correct; no flag.
    for i in range(40):
        await one_xfer(i % 2)
    assert checked['cycles'] > 0, "no PSEL cycles observed -- check is vacuous"
    assert not req_errors, (
        f"{len(req_errors)} cycle(s) with a wrong requester check bit "
        f"(odd parity, IHI 0024E 5.3); first: {req_errors[0]}")
    assert not flag_hits, f"error flag(s) {flag_hits} raised on clean traffic"

    # Phase 2: corrupt one completer check at a time.
    sw = tb.DATA_WIDTH // 8
    injections = [
        ('PRDATACHK',  1 << (sw - 1), 0, 'rdata'),   # top byte lane
        ('PRDATACHK',  1,             0, 'rdata'),   # bottom byte lane
        ('PRUSERCHK',  1,             0, 'rdata'),
        ('PREADYCHK',  1,             1, 'ctrl'),
        ('PSLVERRCHK', 1,             1, 'ctrl'),
        ('PBUSERCHK',  1,             1, 'ctrl'),
    ]
    for name, mask, pwrite, flag in injections:
        await tb.wait_clocks('pclk', 2)
        flag_hits.clear()
        par.corrupt = {name: mask}
        await one_xfer(pwrite)
        par.corrupt = {}
        await tb.wait_clocks('pclk', 2)
        assert flag_hits == {flag}, (
            f"corrupting {name} (mask {mask:#x}) raised {flag_hits or 'nothing'}, "
            f"expected only parity_error_{flag}")

    # A wrong PRDATACHK on a WRITE is outside its Check Enable term
    # (PSEL & PENABLE & PREADY & !PWRITE) and must not be flagged.
    flag_hits.clear()
    par.corrupt = {'PRDATACHK': 1}
    await one_xfer(1)
    par.corrupt = {}
    await tb.wait_clocks('pclk', 2)
    assert not flag_hits, f"PRDATACHK flagged on a write: {flag_hits}"

    tb.log.info(f"=== APB5 master parity PASSED ({checked['cycles']} PSEL cycles) ===")


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_apb5_master_pwakeup(dut):
    """PWAKEUP is a Requester OUTPUT (IHI 0024E 3.7.2, Table 3-7; issue #102
    item 7). The master must raise it at least a cycle before PSEL, hold it
    through PREADY, and drop it once nothing is pending. The pre-fix RTL
    had PWAKEUP as a master INPUT, so it never drove it and this fails."""
    tb = APB5MasterBasicTB(dut)
    await tb.setup_clocks_and_reset()
    dut.rsp_ready.value = 1

    async def drive_command(i):
        while not int(dut.cmd_ready.value):
            await RisingEdge(dut.pclk)
        dut.cmd_valid.value = 1
        dut.cmd_pwrite.value = i & 1
        dut.cmd_paddr.value = (0x40 + 4 * i) & 0xFF
        dut.cmd_pwdata.value = 0x1000 + i
        dut.cmd_pstrb.value = 0xF
        await RisingEdge(dut.pclk)
        dut.cmd_valid.value = 0

    await check_requester_pwakeup(dut, tb.log, drive_command)


def generate_apb5_master_params():
    """Generate test parameters for APB5 master."""
    return [
        # addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width, enable_parity
        (12, 32, 4, 4, 4, 4, 0),
        (16, 32, 8, 8, 8, 8, 0),
        (12, 64, 4, 4, 4, 4, 0),
        # Parity: AW=12 and the user widths leave a short top byte, so the
        # per-byte granularity and the partial-byte rule are both exercised.
        (12, 32, 4, 4, 4, 4, 1),
        (20, 64, 12, 9, 13, 16, 1),
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width, enable_parity",
    generate_apb5_master_params()
)
def test_apb5_master(request, addr_width, data_width, auser_width, wuser_width,
                     ruser_width, buser_width, enable_parity):
    """APB5 master test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_master"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module='apb5_master')

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    pr_str = 'pr' if enable_parity else 'np'
    test_name_plus_params = (f"test_{worker_id}_apb5_master_aw{aw_str}_dw{dw_str}_au{au_str}"
                             f"_wu{wuser_width}_ru{ruser_width}_bu{buser_width}_{pr_str}")
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes=includes

    # RTL parameters
    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AUSER_WIDTH': str(auser_width),
        'WUSER_WIDTH': str(wuser_width),
        'RUSER_WIDTH': str(ruser_width),
        'BUSER_WIDTH': str(buser_width),
        'ENABLE_PARITY': str(enable_parity),
    }

    # Environment variables
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
        'TEST_WUSER_WIDTH': str(wuser_width),
        'TEST_RUSER_WIDTH': str(ruser_width),
        'TEST_BUSER_WIDTH': str(buser_width),
        'TEST_ENABLE_PARITY': str(enable_parity),
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

    # One run() per cocotb test. A comma-joined testcase string selects
    # NOTHING under the conftest exact-name anchor (BUG-015 patch), and an
    # empty selection reports PASS -- this file ran zero tests that way.
    testcases = ["cocotb_test_apb5_master_basic",
                 "cocotb_test_apb5_master_rsp_backpressure",
                 "cocotb_test_apb5_master_pwakeup"]
    if enable_parity:
        testcases.append("cocotb_test_apb5_master_parity")
    try:
        for testcase in testcases:
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
