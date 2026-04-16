"""
DMA Address Generator Test Runner

Test runner for the dma_address_gen.sv module using the CocoTB framework.
Tests 2D strided address generation with signed strides, wrap masks,
and pipeline backpressure.

Test Types:
- 'linear':       Linear/incremental addressing (stride_1=0)
- 'row_major':    2D row-major addressing
- 'reverse':      Reverse traversal with negative strides
- 'wrap':         Circular buffer (1D wrap)
- 'wrap_2d':      2D circular buffer (both dims wrap)
- 'fixed':        Fixed address (FIFO mode, stride=0)
- 'backpressure': Pipeline stall/backpressure testing
- 'throughput':   Back-to-back throughput verification

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)

Author: RTL Design Sherpa
Created: 2025-04-08
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.misc.dv.tbclasses.dma_address_gen_tb import DMAAddressGenTB

# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_dma_address_gen(dut):
    """Unified DMA address generator test - dispatches on TEST_TYPE env var."""
    test_type = os.environ.get('TEST_TYPE', 'linear')

    tb = DMAAddressGenTB(dut)
    await tb.setup_clocks_and_reset()

    cfg = tb.config

    if test_type == 'linear':
        tb.log.info("=== Linear/Incremental Addressing ===")
        ok = await tb.run_linear_test(
            base_addr=0x8000_0000,
            stride=4,
            count=cfg['linear_count']
        )

    elif test_type == 'row_major':
        tb.log.info("=== 2D Row-Major Addressing ===")
        ok = await tb.run_row_major_test(
            base_addr=0x9000_0000,
            elem_size=4,
            row_pitch=512,
            rows=cfg['row_major_rows'],
            cols=cfg['row_major_cols']
        )

    elif test_type == 'reverse':
        tb.log.info("=== Reverse Traversal (Negative Stride) ===")
        ok = await tb.run_reverse_test(
            base_addr=0xA000_0000,
            stride=8,
            count=cfg['linear_count']
        )

    elif test_type == 'wrap':
        tb.log.info("=== 1D Circular Buffer (Wrap) ===")
        ok = await tb.run_wrap_test(
            base_addr=0xB000_0000,
            stride=2,
            wrap_size=256,  # 256-byte ring
            count=cfg['wrap_count']
        )

    elif test_type == 'wrap_2d':
        tb.log.info("=== 2D Circular Buffer (Both Dims Wrap) ===")
        wrap_rows = min(cfg['row_major_rows'], 8)
        wrap_cols = min(cfg['row_major_cols'], 8)
        ok = await tb.run_wrap_2d_test(
            base_addr=0xC000_0000,
            stride_0=4,
            stride_1=64,
            wrap_0=0xFF,    # 256-byte inner wrap
            wrap_1=0x1FF,   # 512-byte outer wrap
            dim0_count=wrap_cols,
            dim1_count=wrap_rows
        )

    elif test_type == 'fixed':
        tb.log.info("=== Fixed Address (FIFO Mode) ===")
        ok = await tb.run_fixed_addr_test(
            base_addr=0xD000_0000,
            count=cfg['linear_count']
        )

    elif test_type == 'backpressure':
        tb.log.info("=== Pipeline Backpressure ===")
        ok = await tb.run_backpressure_test(
            count=cfg['backpressure_count']
        )

    elif test_type == 'throughput':
        tb.log.info("=== Pipeline Throughput ===")
        ok = await tb.run_pipeline_throughput_test(
            count=cfg['stress_count']
        )

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"Test {test_type} failed with {report['mismatches']} mismatches"


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_dma_address_gen_params():
    """
    Generate test parameters for DMA address generator.

    Returns:
        List of tuples: (test_type, addr_width, index_width, stride_width, tag_width)
    """
    test_types = [
        'linear', 'row_major', 'reverse', 'wrap', 'wrap_2d',
        'fixed', 'backpressure', 'throughput',
    ]
    base_params = [
        # (addr_width, index_width, stride_width, tag_width)
        (40, 16, 24, 8),      # Default (typical DMA)
        (32, 12, 16, 4),      # Narrow (smaller DMA)
    ]

    params = []
    for test_type in test_types:
        for base in base_params:
            params.append((test_type,) + base)

    return params


dma_address_gen_params = generate_dma_address_gen_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTION
# ===========================================================================

@pytest.mark.parametrize(
    "test_type, addr_width, index_width, stride_width, tag_width",
    dma_address_gen_params
)
def test_dma_address_gen(request, test_type, addr_width, index_width,
                         stride_width, tag_width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for DMA address generator tests."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_misc': 'projects/components/misc/rtl',
    })

    dut_name = "dma_address_gen"

    # Build verilog sources directly (simple single-file module)
    rtl_path = os.path.join(rtl_dict['rtl_misc'], 'dma_address_gen.sv')
    verilog_sources = [rtl_path]
    includes = []

    # Format parameters for unique test name
    aw_str = TBBase.format_dec(addr_width, 2)
    iw_str = TBBase.format_dec(index_width, 2)
    sw_str = TBBase.format_dec(stride_width, 2)
    tw_str = TBBase.format_dec(tag_width, 2)

    test_name_plus_params = (
        f"test_{dut_name}_{test_type}"
        f"_aw{aw_str}_iw{iw_str}_sw{sw_str}_tw{tw_str}"
    )

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'INDEX_WIDTH': index_width,
        'STRIDE_WIDTH': stride_width,
        'TAG_WIDTH': tag_width,
    }

    extra_env = {
        'TEST_TYPE': test_type,
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_DEBUG': '0',
    }

    simulator = os.environ.get('SIM', 'verilator').lower()

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params
    )

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "-Wno-TIMESCALEMOD",
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_dma_address_gen",
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
            plus_args=['--trace'] if enable_waves else []
        )
        print(f"PASS {test_type} test completed! Logs: {log_path}")
    except Exception as e:
        print(f"FAIL {test_type} test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
