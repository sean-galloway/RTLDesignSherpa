# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SimpleAPBMonitorTB
# Purpose: APB Monitor Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Monitor Test Runner

Comprehensive test for the updated APB monitor module with minimal dependencies.
Tests APB transaction monitoring with error detection, timeout detection, and
performance monitoring capabilities.

Features:
- Self-contained testbench (no complex external dependencies)
- Basic functionality verification
- Monitor bus packet collection and analysis
- Transaction timeout testing
- Multiple test levels support
- Clean integration with updated RTL
"""

import os
import random
import asyncio
import cocotb
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.apb_monitor_tb import SimpleAPBMonitorTB
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=120, timeout_unit="sec")
async def simple_apb_monitor_test(dut):
    """Simple APB monitor test"""
    tb = SimpleAPBMonitorTB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f'Starting simple APB monitor test with seed {seed}')

    # Setup
    await tb.setup_clocks_and_reset()

    # Run tests
    basic_passed = await tb.run_basic_test()
    timeout_passed = await tb.run_timeout_test()

    passed = basic_passed and timeout_passed

    if passed:
        tb.log.info("🎉 SIMPLE APB MONITOR TEST PASSED! 🎉")
    else:
        tb.log.error("❌ Test failed")
        assert False, "Simple APB monitor test failed"


def test_apb_monitor():
    """Simple parametrized test for APB monitor"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_gaxi':          'rtl/amba/gaxi',
        'rtl_apb':           'rtl/amba/apb',
        'rtl_amba_shared':   'rtl/amba/shared',
        'rtl_monitor':       'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # Test parameters
    aw, dw = 32, 32
    unit_id, agent_id = 4, 8
    max_transactions = 4

    test_name = f"test_{worker_id}_apb_monitor_basic"
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    log_path = os.path.join(log_dir, f'{test_name}.log')

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL sources (validated from compilation test)
    # NOTE: Monitor packages must be in dependency order!
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb_monitor.f")

    # Parameters
    parameters = {
        'UNIT_ID': str(unit_id),
        'AGENT_ID': str(agent_id),
        'MAX_TRANSACTIONS': str(max_transactions),
        'ADDR_WIDTH': str(aw),
        'DATA_WIDTH': str(dw),
        'MONITOR_FIFO_DEPTH': '8',
        'AW': str(aw),
        'DW': str(dw),
        'SW': str(dw // 8),
    }

    # Environment
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_AW': str(aw),
        'TEST_DW': str(dw),
        'TEST_UNIT_ID': str(unit_id),
        'TEST_AGENT_ID': str(agent_id),
        'TEST_MAX_TRANSACTIONS': str(max_transactions),
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'LOG_PATH': log_path
    }

    # Compile settings
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace", "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE", "-Wno-PINCONNECTEMPTY", "--no-timing"
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    print(f"\n{'='*60}")
    print(f"Running Working APB Monitor Test")
    print(f"Parameters: AW={aw}, DW={dw}, Unit={unit_id}, Agent={agent_id}")
    print(f"Max Transactions: {max_transactions}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel='apb_monitor',
            module='test_apb_monitor',
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            plus_args=(['--trace'] if enable_waves else []),
            compile_args=compile_args,
            # Pin the testcase: this module also holds apb_monitor_addr_range_test,
            # which needs N_ADDR_RANGES > 0 and its own stimulus.
            testcase="simple_apb_monitor_test",
        )
        print("✅ APB Monitor Test PASSED")

    except Exception as e:
        print(f"❌ APB Monitor Test FAILED: {e}")
        print(f"Logs at: {log_path}")
        raise


def decode_monbus_packet(pkt: int) -> dict:
    """Decode a 128-bit monbus packet (monitor_package_spec.md).

    [127:124] packet_type  [123:109] reserved   [108:105] protocol
    [104: 97] event_code   [ 96: 88] channel_id [ 87: 72] agent_id
    [ 71: 64] unit_id      [ 63:  0] event_data
    """
    # Decode via the house chokepoint (TBClasses.monbus.parse): keeps the
    # field layout in ONE place and feeds the MONBUS_COVERAGE recorder.
    from TBClasses.monbus import parse as _monbus_parse
    _mp = _monbus_parse(pkt)
    return {
        'packet_type': int(_mp.packet_type),
        'protocol': int(_mp.protocol),
        'event_code': int(_mp.event_code),
        'channel_id': int(_mp.channel_id),
        'agent_id': int(_mp.agent_id),
        'unit_id': int(_mp.unit_id),
        'event_data': int(_mp.event_data),
    }


@cocotb.test(timeout_time=100, timeout_unit="us")
async def apb_monitor_addr_range_test(dut):
    """Address-range violation through apb_monitor -- the KNOWN-GOOD control.

    apb_monitor already carries the correct 128-bit addr_check path. This test
    pins that behaviour so the reference cannot silently regress while
    apb5_monitor is migrated onto the same format (issue #41). The apb5 side of
    the same stimulus lives in test_apb5_monitor.py::test_apb5_monitor_addr_range.
    """
    tb = SimpleAPBMonitorTB(dut)

    dut.i_mon_time.value = 0
    await tb.setup_clocks_and_reset()

    async def mon_time_driver():
        count = 0
        while True:
            await RisingEdge(dut.aclk)
            count = (count + 1) & ((1 << 64) - 1)
            dut.i_mon_time.value = count

    cocotb.start_soon(mon_time_driver())

    # Silence every event source except the range checker
    for sig in ('cmd_valid', 'cmd_ready', 'cmd_pwrite', 'cmd_paddr', 'cmd_pwdata',
                'cmd_pstrb', 'cmd_pprot', 'rsp_valid', 'rsp_ready', 'rsp_prdata',
                'rsp_pslverr', 'cfg_error_enable', 'cfg_timeout_enable',
                'cfg_protocol_enable', 'cfg_slverr_enable', 'cfg_perf_enable',
                'cfg_latency_enable', 'cfg_throughput_enable', 'cfg_debug_enable',
                'cfg_trans_debug_enable', 'cfg_debug_level', 'cfg_cmd_timeout_cnt',
                'cfg_rsp_timeout_cnt', 'cfg_latency_threshold',
                'cfg_throughput_threshold'):
        getattr(dut, sig).value = 0

    dut.monbus_ready.value = 1

    n_ranges = 4
    aw = tb.AW
    ranges = [(0x1000 * (i + 1), 0x1000 * (i + 1) + 0xFFF) for i in range(n_ranges)]

    def pack(values):
        word = 0
        for i, v in enumerate(values):
            word |= (v & ((1 << aw) - 1)) << (i * aw)
        return word

    dut.cfg_addr_check_enable.value = 1
    dut.cfg_addr_range_enable.value = (1 << n_ranges) - 1
    dut.cfg_addr_range_low.value = pack([lo for lo, _ in ranges])
    dut.cfg_addr_range_high.value = pack([hi for _, hi in ranges])

    await tb.wait_clocks('aclk', 5)

    async def issue_cmd(addr, is_write):
        dut.cmd_paddr.value = addr
        dut.cmd_pwrite.value = 1 if is_write else 0
        dut.cmd_valid.value = 1
        dut.cmd_ready.value = 1
        await RisingEdge(dut.aclk)
        dut.cmd_valid.value = 0
        dut.cmd_ready.value = 0

        captured = []
        for _ in range(12):
            await RisingEdge(dut.aclk)
            if dut.monbus_valid.value:
                captured.append((int(dut.monbus_packet.value),
                                 int(dut.monbus_timestamp.value)))
        return captured

    for idx, (lo, _hi) in enumerate(ranges):
        for is_write in (True, False):
            addr = lo + 0x123
            pkts = await issue_cmd(addr, is_write)

            assert len(pkts) == 1, \
                f"range {idx} addr 0x{addr:X}: expected 1 packet, got {len(pkts)}"

            raw, ts = pkts[0]
            f = decode_monbus_packet(raw)
            tb.log.info(f"apb_monitor range {idx} {'WR' if is_write else 'RD'} "
                        f"addr=0x{addr:X} -> {f}")

            assert f['packet_type'] == 0x0, f"packet_type 0x{f['packet_type']:X} != 0x0"
            assert f['protocol'] == 0x2, f"protocol 0x{f['protocol']:X} != 0x2 (APB)"
            assert f['event_code'] == 0x08, \
                f"event_code 0x{f['event_code']:02X} != 0x08 (APB_ERR_ADDR_RANGE)"

            ev = f['event_data']
            assert (ev >> 60) & 0xF == idx, f"range index {(ev >> 60) & 0xF} != {idx}"
            assert (ev >> 59) & 0x1 == (0 if is_write else 1), "is_read bit wrong"
            assert ev & ((1 << 59) - 1) == addr, "address field wrong"
            assert ts != 0, "monbus_timestamp is zero - i_mon_time not connected"

    outside = await issue_cmd(ranges[-1][1] + 0x1000, True)
    assert not outside, f"out-of-range address emitted {len(outside)} packet(s)"

    tb.log.info("=== APB Monitor Address-Range Control Test PASSED ===")


def test_apb_monitor_addr_range():
    """APB monitor address-range control test runner (N_ADDR_RANGES > 0)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_gaxi':          'rtl/amba/gaxi',
        'rtl_apb':           'rtl/amba/apb',
        'rtl_amba_shared':   'rtl/amba/shared',
        'rtl_monitor':       'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    aw, dw = 32, 32
    unit_id, agent_id = 4, 8

    test_name = f"test_{worker_id}_apb_monitor_addr_range"
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    log_path = os.path.join(log_dir, f'{test_name}.log')

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb_monitor.f")

    parameters = {
        'UNIT_ID': str(unit_id),
        'AGENT_ID': str(agent_id),
        'MAX_TRANSACTIONS': '4',
        'ADDR_WIDTH': str(aw),
        'DATA_WIDTH': str(dw),
        'MONITOR_FIFO_DEPTH': '8',
        'N_ADDR_RANGES': '4',
        'AW': str(aw),
        'DW': str(dw),
        'SW': str(dw // 8),
    }

    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_AW': str(aw),
        'TEST_DW': str(dw),
        'TEST_UNIT_ID': str(unit_id),
        'TEST_AGENT_ID': str(agent_id),
        'TEST_MAX_TRANSACTIONS': '4',
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'LOG_PATH': log_path
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-PINCONNECTEMPTY", "--no-timing"
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel='apb_monitor',
            module='test_apb_monitor',
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            compile_args=compile_args,
            testcase="apb_monitor_addr_range_test",
        )
    except Exception as e:
        print(f"APB Monitor addr-range control test FAILED: {e}")
        print(f"Logs at: {log_path}")
        raise


if __name__ == "__main__":
    test_apb_monitor()