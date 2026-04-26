"""
Stream Characterization Harness Test Runner

End-to-end test of the stream_char_harness through its UART interface.
Verifies UART → AXIL decode → CSR / desc_ram / APB paths in simulation
before committing to FPGA hardware.

Test Types (dispatched via TEST_TYPE env var):
  'ping'       : Scratch register write/readback + build ID check
  'desc_load'  : Descriptor loading into desc_ram via UART
  'csr_read'   : Read status, wr_ptr, CRC registers
  'apb_config' : Write/readback through axil2apb to STREAM APB space

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches on TEST_TYPE)
  - Single parameter generator (test_type × config)
  - Single pytest wrapper (fully parametrised)

Simulation speed: UART_BAUD is overridden to 12.5 MHz (CLKS_PER_BIT=8)
so that UART transfers take ~80 ns/byte instead of ~87 us/byte.

Author: RTL Design Sherpa
Created: 2026-04-10
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.NexysA7.stream_characterization.dv.tbclasses.stream_char_tb import (
    StreamCharTB,
)

# ==========================================================================
# CocoTB test function
# ==========================================================================

# 50 ms caps the entire test. Realistic breakdown: UART setup ~2.5 ms of
# sim time, poll window ~500 us, plus margin. Was 2000 ms; lowered so a
# broken DMA surfaces as a cocotb timeout in seconds, not minutes.
@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_stream_char(dut):
    """Unified stream characterization test — dispatches on TEST_TYPE."""
    test_type = os.environ.get('TEST_TYPE', 'ping')

    tb = StreamCharTB(dut)
    await tb.setup_clocks_and_reset()

    if test_type == 'ping':
        tb.log.info("=== Ping test (UART -> decode -> CSR) ===")
        ok = await tb.run_ping_test()

    elif test_type == 'desc_load':
        tb.log.info("=== Descriptor load test ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_descriptor_load_test()

    elif test_type == 'csr_read':
        tb.log.info("=== CSR readback test ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_csr_readback_test()

    elif test_type == 'apb_config':
        tb.log.info("=== APB config path test ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_apb_config_test()

    elif test_type.startswith('dma_'):
        # dma_1ch, dma_2ch, ..., dma_8ch
        num_ch = int(test_type.split('_')[1].replace('ch', ''))
        desc_per_ch = int(os.environ.get('DMA_DESC_PER_CH', '2'))
        xfer_bytes = int(os.environ.get('DMA_XFER_BYTES', '8192'))
        tb.log.info(f"=== DMA test: {num_ch}ch x {desc_per_ch}desc x {xfer_bytes}B ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_dma_test(
            num_channels=num_ch,
            descriptors_per_channel=desc_per_ch,
            transfer_bytes=xfer_bytes,
        )

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    report = tb.get_report()
    tb.log.info(f"Report: {report}")
    assert ok, f"Test '{test_type}' failed with {report['errors']} errors"


# ==========================================================================
# Parameter generation
# ==========================================================================

# Simulation-fast UART baud (CLKS_PER_BIT = 100MHz / 12.5MHz = 8)
SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD   = 12_500_000

# RTL parameters for the harness
BASE_RTL_PARAMS = {
    'DATA_WIDTH': 128,
    'ADDR_WIDTH': 32,
    'SRAM_DEPTH': 256,
    # NUM_CHANNELS shrunk from 8 to 4 to fit the Artix-7 100T BRAM budget.
    # Keep in lockstep with rtl/stream_char_top.sv.
    'NUM_CHANNELS': 4,
    # Harness memories were the dominant BRAM consumers. Mirror the FPGA
    # values so sim exercises the same sizes as silicon. Bump either when a
    # test needs deeper descriptor chains or longer trace captures.
    'DESC_RAM_ENTRIES': 128,    # 128 × 256 b =  4 KB
    'DEBUG_SRAM_WORDS': 4096,   # 4K × 32 b   = 16 KB
}


def generate_stream_char_params():
    """
    Generate (test_type,) tuples.  Each level is CUMULATIVE:

    gate: ping                                               (1 test)
    func: gate + desc_load + csr_read + apb_config +
          dma_1ch + dma_2ch                                  (6 tests)
    full: func + dma_3ch + dma_4ch + ... + dma_<NCH>ch

    DMA tests: 2 descriptors/channel, 8 KB each = 16 KB moved per channel.
    The FULL set is capped at BASE_RTL_PARAMS['NUM_CHANNELS'] so we don't
    ask the harness to kick channels it doesn't have (FPGA build is 4-ch).
    """
    max_channels = BASE_RTL_PARAMS.get('NUM_CHANNELS', 8)
    gate_types = ['ping']
    func_types = ['desc_load', 'csr_read', 'apb_config',
                  'dma_1ch', 'dma_2ch']
    full_types = [f'dma_{n}ch' for n in range(3, max_channels + 1)]

    # Accept both TEST_LEVEL (Makefile convention) and REG_LEVEL (legacy)
    level = os.environ.get('TEST_LEVEL',
                os.environ.get('REG_LEVEL', 'FUNC')).upper()

    types = list(gate_types)                  # gate always included
    if level in ('FUNC', 'FULL'):
        types += func_types
    if level == 'FULL':
        types += full_types

    return [(t,) for t in types]


stream_char_params = generate_stream_char_params()


# ==========================================================================
# Pytest wrapper
# ==========================================================================

@pytest.mark.parametrize("test_type", [p[0] for p in stream_char_params])
def test_stream_char(request, test_type, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for stream characterization harness tests."""
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_char': 'projects/NexysA7/stream_characterization',
    })

    dut_name = "stream_char_harness"

    # Build source list via filelist.
    # Environment variables needed by the filelist:
    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root_path, 'projects/NexysA7/stream_characterization')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/NexysA7/stream_characterization/rtl/filelists/stream_char_harness.f',
    )

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_{test_type}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':   str(SIM_UART_BAUD),
        **{k: str(v) for k, v in BASE_RTL_PARAMS.items()},
    }

    extra_env = {
        'TEST_TYPE':        test_type,
        'FPGA_CLK_HZ':     str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':        str(SIM_UART_BAUD),
        'TEST_LEVEL':       test_level,
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':             str(random.randint(0, 100000)),
        # DMA test parameters: 2 descriptors/ch x 8KB = 16KB moved per channel
        'DMA_DESC_PER_CH':  '2',
        'DMA_XFER_BYTES':   '8192',
    }

    # Use Verilator by default
    simulator = os.environ.get('SIM', 'verilator').lower()

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params)

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "-Wno-TIMESCALEMOD",
        "-Wno-MULTIDRIVEN",    # PeakRDL stream_regs.sv
        "-Wno-WIDTHEXPAND",    # minor width warnings in STREAM hierarchy
        "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE",       # descriptor_engine pre-existing slice warning
        "-Wno-UNOPTFLAT",      # dataint_crc combinational cascade (structural CRC)
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_stream_char",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator=simulator,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"PASS {test_type}! Logs: {log_path}")
    except Exception as e:
        print(f"FAIL {test_type}: {e}")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        raise
