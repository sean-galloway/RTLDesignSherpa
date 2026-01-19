# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_fp16_to_fp8_e4m3
# Purpose: Test for FP16 to FP8_E4M3 conversion
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-01-02

"""
Test for FP16 to FP8_E4M3 format conversion.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.common.fp_testing import (
    FPConversionTB, FORMATS
)


def get_fp16_to_fp8_e4m3_params():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [{'test_level': 'simple'}]
    elif reg_level == 'FUNC':
        return [{'test_level': 'basic'}]
    else:
        return [{'test_level': 'simple'}, {'test_level': 'basic'}, {'test_level': 'medium'}, {'test_level': 'full'}]


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def fp16_to_fp8_e4m3_test(dut):
    tb = FPConversionTB(dut, FORMATS['fp16'], FORMATS['fp8_e4m3'])
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.print_settings()
    await tb.clear_interface()
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_fp16_to_fp8_e4m3_params())
def test_math_fp16_to_fp8_e4m3(request, params):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})
    dut_name = "math_fp16_to_fp8_e4m3"
    t_name = params['test_level']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources = [os.path.join(rtl_dict['rtl_cmn'], "math_fp16_to_fp8_e4m3.sv")]
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
