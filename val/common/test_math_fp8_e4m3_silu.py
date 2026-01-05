# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_fp8_e4m3_silu
# Purpose: Test for the FP8 E4M3 silu module
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-01-02

"""
Test for the FP8 E4M3 silu module.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.common.fp_testing import (
    FPSiluTB, FORMATS
)


def get_fp8_e4m3_silu_params():
    """Generate test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [{'test_level': 'simple'}]
    elif reg_level == 'FUNC':
        return [{'test_level': 'basic'}]
    else:
        return [{'test_level': 'simple'}, {'test_level': 'basic'}, {'test_level': 'medium'}, {'test_level': 'full'}]


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def fp8_e4m3_silu_test(dut):
    """Test the FP8 E4M3 silu"""
    tb = FPSiluTB(dut, FORMATS['fp8_e4m3'])
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_fp8_e4m3_silu_params())
def test_math_fp8_e4m3_silu(request, params):
    """PyTest wrapper for FP8 E4M3 silu."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})
    dut_name = "math_fp8_e4m3_silu"
    t_name = params['test_level']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_fp8_e4m3_silu.sv"),
    ]

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    seed = random.randint(0, 100000)
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd", 'VERILATOR_TRACE': '1',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path, 'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
    }
    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=[],
        toplevel=dut_name, module=module, parameters={}, sim_build=sim_build,
        extra_env=extra_env, waves=False, keep_files=True, compile_args=compile_args,
        sim_args=compile_args, plusargs=["--trace"])
