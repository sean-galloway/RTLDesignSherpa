# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_char_top_kick
# Purpose: Close the coverage gap that let the board kick sequencer ship broken
#          (RAPIDS TASK-081).
#
# Every other test in this flow tops out at `rapids_char_harness`. The on-chip
# kick sequencer lives one level ABOVE that, in `rapids_char_top`, so no
# simulation could execute it -- `verify-sim` was fully green while the board
# could not launch a single channel. The sequencer staged CHx_DESC_ADDR_{LOW,
# HIGH} and never wrote KICK_ENABLE, exactly like the cocotb harness TB did.
#
# This drives the BOARD top over a simulated UART at a raised baud, through the
# REAL host transport (RapidsCharIO over UARTAxiBridge with an injected byte
# channel), and asserts on the APB writes the sequencer actually emits. Host
# code and RTL are exercised together, because the defect lived exactly in that
# seam: the host staged, and the RTL never pulled the trigger.
#
# Subsystem: rapids_char_top
# Author: sean galloway
# Created: 2026-09-22

import os
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import (get_paths, create_view_cmd,
                                        get_repo_root, sim_build_path)
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.harness.harness import UartSimHarness

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
_HOST = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'host')
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

# UART bit rate in system clocks. Passed to the RTL as UART_BAUD = FPGA_CLK_HZ /
# CLKS_PER_BIT so the RTL divisor and this constant cannot drift apart (the trap
# pumice's ddr2_char_uart documents).
CLKS_PER_BIT = int(os.environ.get('TEST_CLKS_PER_BIT', '16'))
FPGA_CLK_HZ = 100_000_000
UART_BAUD = FPGA_CLK_HZ // CLKS_PER_BIT

# Harness CSR offsets. These mirror run_characterization.py: the hand-maintained
# rapids_harness_csr_regmap.py carries only the OBS_* registers, so the kick
# sequencer's own CSRs have no by-name entry to resolve through.
CSR_KICK_CFG = 0x064   # [0]=half(0 SRC/1 SNK) [1]=start_gen_on_go
CSR_KICK_MASK = 0x068
CSR_KICK_BASE_LO = 0x06C
CSR_KICK_BASE_HI = 0x070
CSR_KICK_STRIDE = 0x074
CSR_GO = 0x078

DESC_BASE = 0x3000_0000
KICK_STRIDE = 0x1000

APB_SRC_BASE = 0x0000
APB_SNK_BASE = 0x1000
# rapids_beats_top: staged CHx_DESC_ADDR_{LOW,HIGH} + rising-edge KICK_ENABLE.
DUT_KICK_ENABLE = 0x040


def _apb_recorder(dut, sink):
    """Record every ACCEPTED APB write the DUT emits.

    Only the kick sequencer can produce these here: the test writes the CSR
    region (region 2) exclusively, which terminates in char_top's own register
    block and never reaches the APB.
    """
    async def _run():
        while True:
            await RisingEdge(dut.CLK100MHZ)
            try:
                if (int(dut.apb_cmd_valid.value) and int(dut.apb_cmd_ready.value)
                        and int(dut.apb_cmd_pwrite.value)):
                    sink.append((int(dut.apb_cmd_paddr.value),
                                 int(dut.apb_cmd_pwdata.value)))
            except ValueError:
                pass          # X during reset
    return _run


async def _bringup(dut):
    h = UartSimHarness(dut,
                       clk='CLK100MHZ', clk_period_ns=10,
                       resetn='CPU_RESETN', active_low_reset=True,
                       uart_rx='UART_TXD_IN', uart_tx='UART_RXD_OUT',
                       clks_per_bit=CLKS_PER_BIT)
    await h.start()
    from rapids_char_io import RapidsCharIO
    return RapidsCharIO(bridge=h.make_bridge())


def _stage_and_go(io, half_is_snk: int, mask: int):
    """The board's launch sequence, byte-for-byte what run_characterization.py
    does via _stage_kicks() + go()."""
    io.csr_write(CSR_KICK_CFG, (1 if half_is_snk else 0))
    io.csr_write(CSR_KICK_MASK, mask)
    io.csr_write(CSR_KICK_BASE_LO, DESC_BASE & 0xFFFF_FFFF)
    io.csr_write(CSR_KICK_BASE_HI, (DESC_BASE >> 32) & 0xFFFF_FFFF)
    io.csr_write(CSR_KICK_STRIDE, KICK_STRIDE)
    io.csr_write(CSR_GO, 1)


@cocotb.test(timeout_time=60, timeout_unit='ms')
async def cocotb_test_kick_enable_written(dut):
    """GO must stage every masked channel AND then write KICK_ENABLE."""
    io = await _bringup(dut)
    writes = []
    cocotb.start_soon(_apb_recorder(dut, writes)())

    mask = 0b0101                      # channels 0 and 2
    await cocotb.external(lambda: _stage_and_go(io, 1, mask))()
    await ClockCycles(dut.CLK100MHZ, 4000)   # let the sequencer drain

    dut._log.info("APB writes: %s", [(hex(a), hex(d)) for a, d in writes])
    assert writes, "the sequencer emitted no APB writes at all"

    # Every masked channel is staged, LOW then HIGH.
    for ch in (0, 2):
        lo = APB_SNK_BASE + ch * 8
        hi = lo + 4
        assert any(a == lo for a, _ in writes), f"ch{ch} DESC_ADDR_LOW never staged"
        assert any(a == hi for a, _ in writes), f"ch{ch} DESC_ADDR_HIGH never staged"

    # THE regression guard: staging alone launches nothing.
    kick_addr = APB_SNK_BASE + DUT_KICK_ENABLE
    kicks = [(a, d) for a, d in writes if a == kick_addr]
    assert kicks, (
        f"KICK_ENABLE (0x{kick_addr:03X}) was never written -- the sequencer "
        "staged the descriptor addresses and never launched. This is TASK-081.")
    assert len(kicks) == 1, f"KICK_ENABLE written {len(kicks)} times, expected once"
    assert kicks[0][1] == mask, \
        f"KICK_ENABLE carried 0x{kicks[0][1]:X}, expected the staged mask 0x{mask:X}"

    # ...and it must be LAST, after every address is staged.
    assert writes[-1][0] == kick_addr, (
        f"KICK_ENABLE must be the FINAL write; last was 0x{writes[-1][0]:03X}. "
        "Launching before staging completes starts a channel on a stale address.")


@cocotb.test(timeout_time=60, timeout_unit='ms')
async def cocotb_test_empty_mask_is_a_noop(dut):
    """GO with mask=0 must not pulse KICK_ENABLE with nothing staged."""
    io = await _bringup(dut)
    writes = []
    cocotb.start_soon(_apb_recorder(dut, writes)())

    await cocotb.external(lambda: _stage_and_go(io, 1, 0))()
    await ClockCycles(dut.CLK100MHZ, 4000)

    kick_addr = APB_SNK_BASE + DUT_KICK_ENABLE
    assert not [a for a, _ in writes if a == kick_addr], \
        "KICK_ENABLE pulsed with an empty mask; GO with mask=0 must be a no-op"


def _run(request, testcase: str):
    module, repo_root_local, tests_dir, log_dir, _ = get_paths({})
    dut_name = 'rapids_char_top'

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path=('projects/fpga-systems/Genesys2/rapids_characterization/'
                       'flows-rapids-beats/flists/rapids_char_top.f'))

    test_name = request.node.name.replace('[', '_').replace(']', '').replace('-', '_')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f'{test_name}_{worker_id}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': 8,
        'APB_ADDR_WIDTH': 13,
        'APB_DATA_WIDTH': 32,
        # Keep the RTL's UART divisor locked to the TB's clks_per_bit.
        'FPGA_CLK_HZ': FPGA_CLK_HZ,
        'UART_BAUD': UART_BAUD,
    }
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'TEST_CLKS_PER_BIT': str(CLKS_PER_BIT),
    }
    compile_args = [
        '-Wno-fatal',
        '-Wno-TIMESCALEMOD', '-Wno-WIDTH', '-Wno-UNOPTFLAT', '-Wno-CASEINCOMPLETE',
        '-Wno-MULTIDRIVEN', '-Wno-SELRANGE', '-Wno-UNUSEDSIGNAL', '-Wno-DECLFILENAME',
        '-Wno-PINMISSING', '-Wno-UNUSED', '-Wno-UNDRIVEN', '-Wno-VARHIDDEN',
    ]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    try:
        run(python_search=[tests_dir, os.path.abspath(_HOST)],
            verilog_sources=verilog_sources, includes=includes,
            toplevel=dut_name, module=module, testcase=testcase,
            parameters=rtl_parameters, simulator='verilator',
            sim_build=sim_build, results_xml=results_path,
            extra_env=extra_env, compile_args=compile_args, keep_files=True)
        print(f'Test completed! Logs: {log_path}')
    except Exception as e:
        print(f'Test failed: {e}\nLogs: {log_path}')
        if os.path.exists(cmd_filename):
            print(f'View: {cmd_filename}')
        raise


@pytest.mark.rapids_char_top
def test_rapids_char_top_kick_enable(request):
    _run(request, 'cocotb_test_kick_enable_written')


@pytest.mark.rapids_char_top
def test_rapids_char_top_empty_mask(request):
    _run(request, 'cocotb_test_empty_mask_is_a_noop')
