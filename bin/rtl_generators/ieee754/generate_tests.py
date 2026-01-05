#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: IEEE 754 Test Generator
# Purpose: Generate CocoTB test files for all IEEE 754 floating-point modules
#
# Generated tests:
#   - Arithmetic: Multiplier, Adder, FMA for FP32, FP16, FP8 E4M3, FP8 E5M2
#   - Conversions: All format conversion pairs
#   - Activations: ReLU, Leaky ReLU, Sigmoid, Tanh, GELU, SiLU, Softmax
#   - Comparisons: Comparator, Max, Min, Clamp, Max/Min Tree
#
# Usage:
#   python generate_tests.py [output_directory]
#
# Default output: val/common/

import os
import sys
from datetime import datetime

# Format specifications for arithmetic modules
FORMATS = {
    'fp32': ('FP32', 32, 'math_ieee754_2008_fp32'),
    'fp16': ('FP16', 16, 'math_ieee754_2008_fp16'),
    'fp8_e4m3': ('FP8_E4M3', 8, 'math_fp8_e4m3'),
    'fp8_e5m2': ('FP8_E5M2', 8, 'math_fp8_e5m2'),
}

# For activation/comparison modules that use simpler naming
SIMPLE_FORMATS = {
    'fp32': 'math_fp32',
    'fp16': 'math_fp16',
    'bf16': 'math_bf16',
    'fp8_e4m3': 'math_fp8_e4m3',
    'fp8_e5m2': 'math_fp8_e5m2',
}

# Conversion pairs (src, dst)
CONVERSION_PAIRS = [
    ('fp32', 'fp16'), ('fp32', 'bf16'), ('fp32', 'fp8_e4m3'), ('fp32', 'fp8_e5m2'),
    ('fp16', 'fp32'), ('fp16', 'bf16'), ('fp16', 'fp8_e4m3'), ('fp16', 'fp8_e5m2'),
    ('bf16', 'fp32'), ('bf16', 'fp16'), ('bf16', 'fp8_e4m3'), ('bf16', 'fp8_e5m2'),
    ('fp8_e4m3', 'fp32'), ('fp8_e4m3', 'fp16'), ('fp8_e4m3', 'bf16'), ('fp8_e4m3', 'fp8_e5m2'),
    ('fp8_e5m2', 'fp32'), ('fp8_e5m2', 'fp16'), ('fp8_e5m2', 'bf16'), ('fp8_e5m2', 'fp8_e4m3'),
]

TEST_HEADER = '''# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: {test_name}
# Purpose: {purpose}
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: {date}

"""
{docstring}
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.common.fp_testing import (
    {imports}
)

'''

# Common test body template
TEST_BODY = '''
def get_{test_id}_params():
    """Generate test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [{{'test_level': 'simple'}}]
    elif reg_level == 'FUNC':
        return [{{'test_level': 'basic'}}]
    else:
        return [{{'test_level': 'simple'}}, {{'test_level': 'basic'}}, {{'test_level': 'medium'}}, {{'test_level': 'full'}}]


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def {test_id}_test(dut):
    """Test the {desc}"""
    {tb_init}
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {{seed}}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_{test_id}_params())
def test_{module_name}(request, params):
    """PyTest wrapper for {desc}."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({{'rtl_cmn': 'rtl/common'}})
    dut_name = "{module_name}"
    t_name = params['test_level']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{{dut_name}}_{{t_name}}_{{reg_level}}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{{test_name_plus_params}}_{{worker_id}}"

    verilog_sources = [
{verilog_sources}
    ]

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{{test_name_plus_params}}.log')
    results_path = os.path.join(log_dir, f'results_{{test_name_plus_params}}.xml')

    seed = random.randint(0, 100000)
    extra_env = {{
        'TRACE_FILE': f"{{sim_build}}/dump.vcd", 'VERILATOR_TRACE': '1',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path, 'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
    }}
    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=[],
        toplevel=dut_name, module=module, parameters={{}}, sim_build=sim_build,
        extra_env=extra_env, waves=False, keep_files=True, compile_args=compile_args,
        sim_args=compile_args, plusargs=["--trace"])
'''


def get_arithmetic_deps(fmt_key, op):
    """Get verilog source dependencies for arithmetic modules."""
    deps = [
        '        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_half.sv"),',
        '        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_full.sv"),',
        '        os.path.join(rtl_dict[\'rtl_cmn\'], "math_compressor_4to2.sv"),',
        '        os.path.join(rtl_dict[\'rtl_cmn\'], "math_prefix_cell.sv"),',
        '        os.path.join(rtl_dict[\'rtl_cmn\'], "math_prefix_cell_gray.sv"),',
    ]

    if fmt_key == 'fp32':
        if op in ['multiplier', 'fma']:
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_han_carlson_048.sv"),')
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_multiplier_dadda_4to2_024.sv"),')
        if op == 'fma':
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_han_carlson_072.sv"),')
        if op == 'adder':
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "count_leading_zeros.sv"),')
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_han_carlson_032.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_ieee754_2008_fp32_mantissa_mult.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_ieee754_2008_fp32_exponent_adder.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_ieee754_2008_fp32_{op}.sv"),')
    elif fmt_key == 'fp16':
        if op in ['multiplier', 'fma']:
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_han_carlson_022.sv"),')
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_multiplier_dadda_4to2_011.sv"),')
        if op == 'fma':
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_han_carlson_044.sv"),')
        if op == 'adder':
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "count_leading_zeros.sv"),')
            deps.append('        os.path.join(rtl_dict[\'rtl_cmn\'], "math_adder_han_carlson_016.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_ieee754_2008_fp16_mantissa_mult.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_ieee754_2008_fp16_exponent_adder.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_ieee754_2008_fp16_{op}.sv"),')
    elif fmt_key == 'fp8_e4m3':
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_fp8_e4m3_mantissa_mult.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_fp8_e4m3_exponent_adder.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_fp8_e4m3_{op}.sv"),')
    elif fmt_key == 'fp8_e5m2':
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_fp8_e5m2_mantissa_mult.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_fp8_e5m2_exponent_adder.sv"),')
        deps.append(f'        os.path.join(rtl_dict[\'rtl_cmn\'], "math_fp8_e5m2_{op}.sv"),')

    return '\n'.join(deps)


def generate_arithmetic_test(fmt_key, op, output_dir):
    """Generate arithmetic operation test file."""
    name, bits, prefix = FORMATS[fmt_key]
    module_name = f"{prefix}_{op}"
    test_name = f"test_{module_name}"
    test_id = f"{fmt_key}_{op}"

    tb_class = {'multiplier': 'FPMultiplierTB', 'adder': 'FPAdderTB', 'fma': 'FPFMATB'}[op]

    content = TEST_HEADER.format(
        test_name=test_name,
        purpose=f"Test for the {name} floating-point {op} module",
        date=datetime.now().strftime("%Y-%m-%d"),
        docstring=f"Test for the {name} floating-point {op} module.",
        imports=f"{tb_class}, FORMATS"
    )

    content += TEST_BODY.format(
        test_id=test_id,
        desc=f"{name} {op}",
        tb_init=f"tb = {tb_class}(dut, FORMATS['{fmt_key}'])",
        module_name=module_name,
        verilog_sources=get_arithmetic_deps(fmt_key, op)
    )

    filepath = os.path.join(output_dir, f"{test_name}.py")
    with open(filepath, 'w') as f:
        f.write(content)
    return test_name


def generate_simple_test(fmt_key, op, tb_class, output_dir, extra_args=""):
    """Generate a simple single-module test."""
    prefix = SIMPLE_FORMATS[fmt_key]
    module_name = f"{prefix}_{op}"
    test_name = f"test_{module_name}"
    test_id = f"{fmt_key}_{op}"
    name = fmt_key.upper().replace('_', ' ')

    content = TEST_HEADER.format(
        test_name=test_name,
        purpose=f"Test for the {name} {op} module",
        date=datetime.now().strftime("%Y-%m-%d"),
        docstring=f"Test for the {name} {op} module.",
        imports=f"{tb_class}, FORMATS"
    )

    tb_init = f"tb = {tb_class}(dut, FORMATS['{fmt_key}']{extra_args})"

    content += TEST_BODY.format(
        test_id=test_id,
        desc=f"{name} {op}",
        tb_init=tb_init,
        module_name=module_name,
        verilog_sources=f'        os.path.join(rtl_dict[\'rtl_cmn\'], "{module_name}.sv"),'
    )

    filepath = os.path.join(output_dir, f"{test_name}.py")
    with open(filepath, 'w') as f:
        f.write(content)
    return test_name


def generate_conversion_test(src_fmt, dst_fmt, output_dir):
    """Generate format conversion test."""
    module_name = f"math_{src_fmt}_to_{dst_fmt}"
    test_name = f"test_{module_name}"
    test_id = f"{src_fmt}_to_{dst_fmt}"

    content = TEST_HEADER.format(
        test_name=test_name,
        purpose=f"Test for {src_fmt.upper()} to {dst_fmt.upper()} conversion",
        date=datetime.now().strftime("%Y-%m-%d"),
        docstring=f"Test for {src_fmt.upper()} to {dst_fmt.upper()} format conversion.",
        imports=f"FPConversionTB, FORMATS"
    )

    content += f'''
def get_{test_id}_params():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [{{'test_level': 'simple'}}]
    elif reg_level == 'FUNC':
        return [{{'test_level': 'basic'}}]
    else:
        return [{{'test_level': 'simple'}}, {{'test_level': 'basic'}}, {{'test_level': 'medium'}}, {{'test_level': 'full'}}]


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def {test_id}_test(dut):
    tb = FPConversionTB(dut, FORMATS['{src_fmt}'], FORMATS['{dst_fmt}'])
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.print_settings()
    await tb.clear_interface()
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_{test_id}_params())
def test_{module_name}(request, params):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({{'rtl_cmn': 'rtl/common'}})
    dut_name = "{module_name}"
    t_name = params['test_level']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{{dut_name}}_{{t_name}}_{{reg_level}}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{{test_name_plus_params}}_{{worker_id}}"

    verilog_sources = [os.path.join(rtl_dict['rtl_cmn'], "{module_name}.sv")]
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{{test_name_plus_params}}.log')
    results_path = os.path.join(log_dir, f'results_{{test_name_plus_params}}.xml')

    seed = random.randint(0, 100000)
    extra_env = {{
        'TRACE_FILE': f"{{sim_build}}/dump.vcd", 'VERILATOR_TRACE': '1',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path, 'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
    }}
    compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=[],
        toplevel=dut_name, module=module, parameters={{}}, sim_build=sim_build,
        extra_env=extra_env, waves=False, keep_files=True, compile_args=compile_args,
        sim_args=compile_args, plusargs=["--trace"])
'''

    filepath = os.path.join(output_dir, f"{test_name}.py")
    with open(filepath, 'w') as f:
        f.write(content)
    return test_name


def generate_all_tests(output_dir):
    """Generate all test files."""
    print(f"Generating tests to: {output_dir}")
    os.makedirs(output_dir, exist_ok=True)

    generated = []

    # Arithmetic tests
    print("\n=== Arithmetic Tests ===")
    for fmt_key in FORMATS:
        for op in ['multiplier', 'adder', 'fma']:
            name = generate_arithmetic_test(fmt_key, op, output_dir)
            generated.append(name)
            print(f"  Created: {name}.py")

    # Comparison tests
    print("\n=== Comparison Tests ===")
    for fmt_key in SIMPLE_FORMATS:
        # Comparator
        name = generate_simple_test(fmt_key, 'comparator', 'FPComparatorTB', output_dir)
        generated.append(name)
        print(f"  Created: {name}.py")

        # Max
        name = generate_simple_test(fmt_key, 'max', 'FPMaxMinTB', output_dir, ', is_max=True')
        generated.append(name)
        print(f"  Created: {name}.py")

        # Min
        name = generate_simple_test(fmt_key, 'min', 'FPMaxMinTB', output_dir, ', is_max=False')
        generated.append(name)
        print(f"  Created: {name}.py")

        # Clamp
        name = generate_simple_test(fmt_key, 'clamp', 'FPClampTB', output_dir)
        generated.append(name)
        print(f"  Created: {name}.py")

    # Activation tests
    print("\n=== Activation Tests ===")
    activations = [
        ('relu', 'FPReluTB', ''),
        ('leaky_relu', 'FPLeakyReluTB', ''),
        ('sigmoid', 'FPSigmoidTB', ''),
        ('tanh', 'FPTanhTB', ''),
        ('gelu', 'FPGeluTB', ''),
        ('silu', 'FPSiluTB', ''),
    ]
    for fmt_key in SIMPLE_FORMATS:
        for op, tb_class, extra in activations:
            name = generate_simple_test(fmt_key, op, tb_class, output_dir, extra)
            generated.append(name)
            print(f"  Created: {name}.py")

    # Conversion tests
    print("\n=== Conversion Tests ===")
    for src, dst in CONVERSION_PAIRS:
        name = generate_conversion_test(src, dst, output_dir)
        generated.append(name)
        print(f"  Created: {name}.py")

    print(f"\nGenerated {len(generated)} test files")
    return generated


def main():
    if len(sys.argv) > 1:
        output_dir = sys.argv[1]
    else:
        script_dir = os.path.dirname(os.path.abspath(__file__))
        repo_root = os.path.dirname(os.path.dirname(os.path.dirname(script_dir)))
        output_dir = os.path.join(repo_root, 'val', 'common')

    generate_all_tests(output_dir)


if __name__ == '__main__':
    main()
