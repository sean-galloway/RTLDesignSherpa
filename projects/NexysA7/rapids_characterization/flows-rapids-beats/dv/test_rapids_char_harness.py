# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_char_harness
# Purpose: pytest runner for the RAPIDS beats characterization harness self-check
#          (Pattern B: cocotb_test_* functions + pytest wrappers).
#
# Documentation: projects/NexysA7/rapids_characterization/flows-rapids-beats/
# Subsystem: rapids_char_harness
#
# Author: sean galloway
# Created: 2026-07-03

"""
Multi-channel self-check tests for rapids_char_harness.

  cocotb_test_sink_selfcheck   : AXIS gen -> DUT sink -> m_axi_wr CRC. Asserts
    per active channel wr_crc_value[ch] == o_gen_expected_crc[ch] (s_axis -> sink
    -> m_axi_wr integrity), 100%.
  cocotb_test_source_selfcheck : m_axi_rd LFSR -> DUT source -> m_axis chk. Asserts
    per active channel o_chk_actual_crc[ch] == rd_crc_value[ch] with
    o_data_error == 0 (m_axi_rd -> source -> m_axis integrity), 100%.

Config is programmed BY NAME over the 13-bit APB register chain (two RegisterMap
instances, SRC @ 0x0000 / SNK @ 0x1000); descriptors are loaded into the on-chip
descriptor RAM through its exposed host write port (256-bit AXI4 write master) and
kicked off through the per-half apbtodescr kick windows.
"""

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
# The TB lives next to this runner in a hyphenated dir (not import-safe as a
# package), so put this file's directory on sys.path for a flat import.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from rapids_char_harness_tb import RapidsCharHarnessTB  # noqa: E402


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_sink_selfcheck(dut):
    """Multi-channel SINK self-check: s_axis -> sink -> m_axi_wr per-channel CRC."""
    tb = RapidsCharHarnessTB(dut)
    await tb.setup_clocks_and_reset()

    active = list(range(tb.NUM_ACTIVE))
    ok, stats = await tb.run_sink_selfcheck(active_channels=active, beats=tb.NUM_BEATS)

    assert ok, f"SINK self-check failed: {stats.get('errors')}"
    tb.log.info("rapids_char_harness SINK self-check PASSED")


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_source_selfcheck(dut):
    """Multi-channel SOURCE self-check: m_axi_rd -> source -> m_axis per-channel CRC."""
    tb = RapidsCharHarnessTB(dut)
    await tb.setup_clocks_and_reset()

    active = list(range(tb.NUM_ACTIVE))
    ok, stats = await tb.run_source_selfcheck(active_channels=active, beats=tb.NUM_BEATS)

    assert ok, f"SOURCE self-check failed: {stats.get('errors')}"
    tb.log.info("rapids_char_harness SOURCE self-check PASSED")


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

def _run_harness(testcase, test_name):
    """Compile rapids_char_harness (via its filelist) and run one testcase.

    13-bit APB (address bit[12] selects SRC/SNK), so both the RTL build
    (-G APB_ADDR_WIDTH=13) and the TB (TEST_APB_ADDR_WIDTH=13) are pinned to 13."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root_local, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_regmap': '../../../../components/rapids/rtl',
    })
    dut_name = "rapids_char_harness"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path=('projects/NexysA7/rapids_characterization/'
                       'flows-rapids-beats/flists/rapids_char_harness.f')
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    num_channels = int(os.environ.get('TEST_NUM_CHANNELS', '8'))
    num_active = int(os.environ.get('TEST_NUM_ACTIVE', '4'))
    num_beats = int(os.environ.get('TEST_NUM_BEATS', '8'))

    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'DATA_WIDTH': 512,
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': 8,
        'SRAM_DEPTH': 512,
        'APB_ADDR_WIDTH': 13,
        'APB_DATA_WIDTH': 32,
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': str(num_channels),
        'TEST_NUM_ACTIVE': str(num_active),
        'TEST_NUM_BEATS': str(num_beats),
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': '512',
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_APB_ADDR_WIDTH': '13',
        'TEST_APB_DATA_WIDTH': '32',
    }

    compile_args = [
        "-Wno-fatal",
        "-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE",
        "-Wno-MULTIDRIVEN", "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL",
    ]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            results_xml=results_path,
            extra_env=extra_env,
            compile_args=compile_args,
            waves=enable_waves,
            keep_files=True,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View: {cmd_filename}")
        raise


@pytest.mark.rapids_char_harness
def test_rapids_char_harness_sink(request):
    """Multi-channel SINK self-check (s_axis -> sink -> m_axi_wr per-channel CRC)."""
    _run_harness("cocotb_test_sink_selfcheck", "test_rapids_char_harness_sink")


@pytest.mark.rapids_char_harness
def test_rapids_char_harness_source(request):
    """Multi-channel SOURCE self-check (m_axi_rd -> source -> m_axis per-channel CRC)."""
    _run_harness("cocotb_test_source_selfcheck", "test_rapids_char_harness_source")


if __name__ == "__main__":
    class MockRequest:
        pass
    test_rapids_char_harness_sink(MockRequest())
    test_rapids_char_harness_source(MockRequest())
