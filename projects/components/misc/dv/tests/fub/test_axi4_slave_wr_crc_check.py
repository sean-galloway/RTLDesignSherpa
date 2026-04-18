"""
AXI4 Slave Write CRC Check - FUB Test Runner

Tests the axi4_slave_wr_crc_check module independently:
  - Single-beat AXI4 write + B response
  - Multi-beat burst writes
  - Back-to-back transactions
  - CRC and beat counter verification

Author: RTL Design Sherpa
Created: 2026-04-18
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

from projects.components.misc.dv.tbclasses.axi4_slave_wr_crc_check_tb import (
    AXI4SlaveWrCrcCheckTB,
)


# ===========================================================================
# COCOTB TEST FUNCTION
# ===========================================================================

@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_axi4_slave_wr_crc_check(dut):
    """Unified test for axi4_slave_wr_crc_check."""
    test_type = os.environ.get('TEST_TYPE', 'single')

    tb = AXI4SlaveWrCrcCheckTB(dut)
    await tb.setup_clocks_and_reset()

    if test_type == 'single':
        await tb.run_single_beat_test()

    elif test_type == 'burst':
        await tb.run_burst_test(burst_len=4)

    elif test_type == 'back_to_back':
        await tb.run_back_to_back_test(num_writes=4, burst_len=4)

    elif test_type == 'crc':
        await tb.run_crc_test(burst_len=16)

    elif test_type == 'all':
        await tb.run_single_beat_test()
        await tb.run_burst_test(burst_len=4)
        await tb.run_burst_test(burst_len=16)
        await tb.run_back_to_back_test(num_writes=4, burst_len=4)
        await tb.run_crc_test(burst_len=16)

    else:
        raise ValueError(f"Unknown test_type: {test_type}")


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_params():
    test_types = ['single', 'burst', 'back_to_back', 'crc', 'all']
    configs = [
        # (data_width, id_width, user_width)
        (128, 8, 3),   # Match characterization harness
        (64, 4, 1),    # Smaller config
    ]
    params = []
    for test_type in test_types:
        for dw, iw, uw in configs:
            params.append((test_type, dw, iw, uw))
    return params


wr_crc_check_params = generate_params()


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

@pytest.mark.parametrize(
    "test_type, data_width, id_width, user_width",
    wr_crc_check_params,
)
def test_axi4_slave_wr_crc_check(request, test_type, data_width, id_width,
                                  user_width):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_misc': 'projects/components/misc/rtl',
        'rtl_amba_axi4': 'rtl/amba/axi4',
        'rtl_amba_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
    })

    dut_name = "axi4_slave_wr_crc_check"

    verilog_sources = [
        # Common primitives
        os.path.join(rtl_dict['rtl_common'], 'dataint_crc_xor_shift.sv'),
        os.path.join(rtl_dict['rtl_common'], 'dataint_crc_xor_shift_cascade.sv'),
        os.path.join(rtl_dict['rtl_common'], 'dataint_crc.sv'),
        # AMBA infrastructure
        os.path.join(rtl_dict['rtl_amba_gaxi'], 'gaxi_skid_buffer.sv'),
        os.path.join(rtl_dict['rtl_amba_axi4'], 'axi4_slave_wr.sv'),
        # DUT
        os.path.join(rtl_dict['rtl_misc'], 'axi4_slave_wr_crc_check.sv'),
    ]

    includes = [
        rtl_dict['rtl_amba_includes'],
    ]

    dw_str = TBBase.format_dec(data_width, 3)
    iw_str = TBBase.format_dec(id_width, 2)

    test_name_plus_params = (
        f"test_{dut_name}_{test_type}_dw{dw_str}_iw{iw_str}"
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'AXI_DATA_WIDTH': data_width,
        'AXI_ID_WIDTH': id_width,
        'AXI_USER_WIDTH': user_width,
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
    }

    simulator = os.environ.get('SIM', 'verilator').lower()

    if enable_waves:
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
            testcase="cocotb_test_axi4_slave_wr_crc_check",
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
        print(f"PASS {test_type} dw={data_width} iw={id_width}")
    except Exception as e:
        print(f"FAIL {test_type} dw={data_width} iw={id_width}: {e}")
        raise
