# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_byte_harness
# Purpose: pytest runner for the byte-granular RAPIDS characterization harness self-check
#          (Pattern B: cocotb_test_* functions + pytest wrappers).
#
# Documentation: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/
# Subsystem: rapids_byte_harness
#
# Author: sean galloway
# Created: 2026-07-03

"""
Multi-channel self-check tests for rapids_byte_harness.

  cocotb_test_sink_selfcheck   : AXIS gen -> DUT sink -> m_axi_wr CRC. Asserts
    per active channel wr_crc_value[ch] == o_gen_expected_crc[ch] (s_axis -> sink
    -> m_axi_wr integrity), 100%.
  cocotb_test_source_selfcheck : m_axi_rd LFSR -> DUT source -> m_axis chk. Asserts
    per active channel o_chk_actual_crc[ch] == rd_crc_value[ch] with
    o_data_error == 0 (m_axi_rd -> source -> m_axis integrity), 100%.

Config is programmed BY NAME over the 13-bit APB register chain (two RegisterMap
instances, SRC @ 0x0000 / SNK @ 0x1000); descriptors are loaded into the on-chip
descriptor RAM through its exposed host write port (256-bit AXI4 write master) and
kicked off through the per-half kick windows.
"""

import os
import sys

import pytest
import cocotb
from cocotb._bridge import bridge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
# The TB lives next to this runner in a hyphenated dir (not import-safe as a
# package), so put this file's directory on sys.path for a flat import.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from rapids_byte_harness_tb import RapidsByteHarnessTB  # noqa: E402


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_sink_selfcheck(dut):
    """Multi-channel SINK self-check: s_axis -> sink -> m_axi_wr per-channel CRC."""
    tb = RapidsByteHarnessTB(dut)
    await tb.setup_clocks_and_reset()

    active = list(range(tb.NUM_ACTIVE))
    ok, stats = await tb.run_sink_selfcheck(active_channels=active, beats=tb.NUM_BEATS)

    assert ok, f"SINK self-check failed: {stats.get('errors')}"
    tb.log.info("rapids_byte_harness SINK self-check PASSED")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_byte_selfcheck(dut):
    """Byte-granular RAPIDS (rapids TASK-019): packets of
    TEST_PKT_BYTES bytes at byte offset TEST_OFFSET, sink then source, scored
    against the byte-wise goldens. The whole host program runs unchanged."""
    tb = RapidsByteHarnessTB(dut)
    await tb.setup_clocks_and_reset()
    active = list(range(tb.NUM_ACTIVE))
    nbytes = int(os.environ.get('TEST_PKT_BYTES', '77'))
    offset = int(os.environ.get('TEST_OFFSET', '5'))
    ok_s, st_s = await tb.run_sink_selfcheck(active_channels=active, beats=0,
                                             pkt_bytes=nbytes, offset=offset)
    ok_r, st_r = await tb.run_source_selfcheck(active_channels=active, beats=0,
                                               pkt_bytes=nbytes, offset=offset)
    assert ok_s, f"byte SINK self-check failed ({nbytes} B @ {offset}): {st_s.get('errors')}"
    assert ok_r, f"byte SOURCE self-check failed ({nbytes} B @ {offset}): {st_r.get('errors')}"
    tb.log.info(f"rapids_byte_harness BYTE self-check PASSED ({nbytes} B at offset {offset})")


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_byte_perf(dut):
    """Byte-perf campaign point runner (byte_perf.py) end to end over the sim
    UART: one byte-path point and one beat-aligned point, both directions.
    Asserts the derived report fields: bytes moved, beats moved, efficiency
    = payload / (beats x lanes), and that the bus-meter counts match."""
    import byte_perf
    tb = RapidsByteHarnessTB(dut)
    await tb.setup_clocks_and_reset()
    bpb = tb.campaign.ensure_build()['beat_bytes']
    pts = [byte_perf._pt('size', 1, payload=77, offset=5),
           byte_perf._pt('beat', 1, beats=4)]
    for pt in pts:
        row = await bridge(lambda pt=pt: byte_perf.run_point(tb.campaign, pt, 60.0))()
        assert row['pass'], f"{pt['id']}: {row}"
        for d in ('sink', 'source'):
            r = row[d]
            assert r['counts_match'], f"{pt['id']} {d}: meter counts differ from expected"
            exp_payload = pt['payload'] if pt['payload'] is not None else pt['beats'] * bpb
            assert r['bytes'] == exp_payload * pt['channels'] * pt['descs'], f"{pt['id']} {d}: bytes {r['bytes']}"
            assert r['eff_axis'] == pytest.approx(
                r['bytes'] / (r['axis_beats'] * bpb)), f"{pt['id']} {d}: eff"
    tb.log.info("rapids_byte_harness BYTE-PERF point runner PASSED")


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_source_selfcheck(dut):
    """Multi-channel SOURCE self-check: m_axi_rd -> source -> m_axis per-channel CRC."""
    tb = RapidsByteHarnessTB(dut)
    await tb.setup_clocks_and_reset()

    active = list(range(tb.NUM_ACTIVE))
    ok, stats = await tb.run_source_selfcheck(active_channels=active, beats=tb.NUM_BEATS)

    assert ok, f"SOURCE self-check failed: {stats.get('errors')}"
    tb.log.info("rapids_byte_harness SOURCE self-check PASSED")


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

def _run_harness(testcase, test_name, *, test_level='gate', extra_env=None,
                 build_name=None, compile_first=None, module_name=None):
    """Compile rapids_byte_harness (via its filelist) and run one testcase.

    build_name shares one sim_build between cases (a Verilator build is minutes);
    compile_first is a context-manager factory that serialises that compile.

    13-bit APB (address bit[12] selects SRC/SNK), so both the RTL build
    (-G APB_ADDR_WIDTH=13) and the TB (TEST_APB_ADDR_WIDTH=13) are pinned to 13."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root_local, tests_dir, log_dir, _ = get_paths({})
    module = module_name or module
    dut_name = "rapids_byte_harness"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path=('projects/fpga-systems/Genesys2/dma-ip/rapids/'
                       'flows-rapids/filelists/rapids_byte_harness.f')
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = sim_build_path(tests_dir, build_name or test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    num_channels = int(os.environ.get('TEST_NUM_CHANNELS', '8'))
    num_active = int(os.environ.get('TEST_NUM_ACTIVE', '4'))
    num_beats = int(os.environ.get('TEST_NUM_BEATS', '8'))

    # UART bit rate in system clocks. MEASURED floor is 4 (ddr2_char: 3 and 2
    # fail; uart_rx samples at (CLKS_PER_BIT-1)/2). UART_BAUD is DERIVED from it
    # so the RTL divisor and the TB constant cannot drift apart.
    clks_per_bit = int(os.environ.get('TEST_CLKS_PER_BIT', '4'))
    fpga_clk_hz = 100_000_000

    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'FPGA_CLK_HZ': fpga_clk_hz,
        'UART_BAUD': fpga_clk_hz // clks_per_bit,
        # 512 is the RTL default; the Genesys 2 build is 256 (Makefile DATA_WIDTH),
        # and verify-sim passes the build's value so sim == board.
        'DATA_WIDTH': int(os.environ.get('TEST_DATA_WIDTH', '512')),
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': 8,
        # 512 by default; the Genesys 2 build is 256 (rapids_byte_genesys2_top), so
        # TEST_SRAM_DEPTH=256 reproduces the board's sink buffering (rapids ISSUE-006).
        'SRAM_DEPTH': int(os.environ.get('TEST_SRAM_DEPTH', '512')),
        'APB_ADDR_WIDTH': 13,
        'APB_DATA_WIDTH': 32,
        # Shared interface observers (rapids TASK-001). Default OUT, as on the
        # board; TEST_USE_OBSERVERS=1 builds them so verify-sim covers that flavour.
        'USE_OBSERVERS': int(os.environ.get('TEST_USE_OBSERVERS', '0')),
        'OBS_ENABLE_MON_TAPS': int(os.environ.get('TEST_OBS_ENABLE_MON_TAPS', '0')),
        # 1 = byte-wise checkers (every campaign); 0 = the word-wide flavour the
        # aligned performance build uses (BUILD.WORD_CRC = 1).
        'BYTE_CRC': int(os.environ.get('TEST_BYTE_CRC', '1')),
    }

    env = {
        **level_env(test_level),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(12345),
        'TEST_CLKS_PER_BIT': str(clks_per_bit),
        'TEST_NUM_CHANNELS': str(num_channels),
        'TEST_NUM_ACTIVE': str(num_active),
        'TEST_NUM_BEATS': str(num_beats),
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': os.environ.get('TEST_DATA_WIDTH', '512'),
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_APB_ADDR_WIDTH': '13',
        'TEST_APB_DATA_WIDTH': '32',
        'TEST_PKT_BYTES': os.environ.get('TEST_PKT_BYTES', '77'),
        'TEST_OFFSET': os.environ.get('TEST_OFFSET', '5'),
        **(extra_env or {}),
    }

    compile_args = [
        "-Wno-fatal",
        "-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE",
        "-Wno-MULTIDRIVEN", "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL",
    ]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    build_args = dict(
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
            extra_env=env,
            compile_args=compile_args,
            waves=enable_waves,
            keep_files=True,
            plus_args=['--trace'] if enable_waves else [],
        )
    try:
        if compile_first is not None:
            with compile_first(sim_build):
                run(compile_only=True, **build_args)
        run(**build_args)
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View: {cmd_filename}")
        raise


@pytest.mark.rapids_byte_harness
def test_rapids_byte_harness_sink(request):
    """Multi-channel SINK self-check (s_axis -> sink -> m_axi_wr per-channel CRC)."""
    _run_harness("cocotb_test_sink_selfcheck", "test_rapids_byte_harness_sink")


@pytest.mark.rapids_byte_harness
@pytest.mark.parametrize("pkt_bytes, offset", [(1, 1), (77, 5), (33, 31), (6 * 32 + 11, 0x1000 - 2 * 32 + 3), (203, 1)])
def test_rapids_byte_harness_bytes(request, pkt_bytes, offset):
    """Byte-granular RAPIDS on the harness (rapids TASK-019): sink and source
    with byte lengths and offsets, byte-wise goldens."""
    saved = {k: os.environ.get(k) for k in ('TEST_PKT_BYTES', 'TEST_OFFSET')}
    os.environ['TEST_PKT_BYTES'] = str(pkt_bytes)
    os.environ['TEST_OFFSET'] = str(offset)
    try:
        _run_harness("cocotb_test_byte_selfcheck", f"test_rapids_byte_harness_bytes_{pkt_bytes}_{offset}")
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


@pytest.mark.rapids_byte_harness
def test_rapids_byte_harness_perf(request):
    """byte_perf.run_point over the sim UART: derived bytes/beats/efficiency."""
    _run_harness("cocotb_test_byte_perf", "test_rapids_byte_harness_perf")


@pytest.mark.rapids_byte_harness
def test_rapids_byte_harness_source(request):
    """Multi-channel SOURCE self-check (m_axi_rd -> source -> m_axis per-channel CRC)."""
    _run_harness("cocotb_test_source_selfcheck", "test_rapids_byte_harness_source")


if __name__ == "__main__":
    class MockRequest:
        pass
    test_rapids_byte_harness_sink(MockRequest())
    test_rapids_byte_harness_source(MockRequest())
