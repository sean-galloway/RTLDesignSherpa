# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_bf16_exponent_adder
# Purpose: Test for the BF16 exponent adder module.
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Test for the BF16 exponent adder module.

This module handles exponent addition with bias handling, overflow/underflow
detection, and special case (zero/inf/nan) detection.

BF16 exponent: 8 bits, bias = 127
Result = exp_a + exp_b - 127 + norm_adjust
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class BF16ExponentAdderTB(TBBase):
    """Testbench for BF16 exponent adder.

    Works with the interface:
    - i_exp_a: 8-bit exponent A
    - i_exp_b: 8-bit exponent B
    - i_norm_adjust: 1-bit normalization adjustment
    - ow_exp_out: 8-bit result exponent
    - ow_overflow: 1 if result overflows
    - ow_underflow: 1 if result underflows
    - ow_a_is_zero, ow_b_is_zero: 1 if exponent is 0
    - ow_a_is_inf, ow_b_is_inf: 1 if exponent is 255
    - ow_a_is_nan, ow_b_is_nan: 1 if exponent is 255 (NaN check needs mantissa)
    """

    BIAS = 127

    def __init__(self, dut):
        """Initialize the testbench with design under test."""
        TBBase.__init__(self, dut)
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info("Testing BF16 Exponent Adder")

    def print_settings(self):
        """Print testbench settings."""
        self.log.info("BF16 Exponent Adder Testbench Settings:")
        self.log.info(f"  Test Level: {self.test_level}")
        self.log.info(f"  Seed: {self.seed}")

    def clear_interface(self):
        """Clear the DUT interface."""
        self.dut.i_exp_a.value = 0
        self.dut.i_exp_b.value = 0
        self.dut.i_norm_adjust.value = 0

    async def test_single_exp_add(self, exp_a: int, exp_b: int, norm_adj: int) -> bool:
        """Test a single exponent addition."""
        self.dut.i_exp_a.value = exp_a
        self.dut.i_exp_b.value = exp_b
        self.dut.i_norm_adjust.value = norm_adj

        await self.wait_time(1, 'ns')

        # Get DUT outputs
        exp_out = int(self.dut.ow_exp_out.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        a_is_zero = int(self.dut.ow_a_is_zero.value)
        b_is_zero = int(self.dut.ow_b_is_zero.value)
        a_is_inf = int(self.dut.ow_a_is_inf.value)
        b_is_inf = int(self.dut.ow_b_is_inf.value)
        a_is_nan = int(self.dut.ow_a_is_nan.value)
        b_is_nan = int(self.dut.ow_b_is_nan.value)

        # Calculate expected values
        # Special case flags
        exp_a_is_zero = 1 if exp_a == 0 else 0
        exp_b_is_zero = 1 if exp_b == 0 else 0
        exp_a_is_inf = 1 if exp_a == 255 else 0
        exp_b_is_inf = 1 if exp_b == 255 else 0
        exp_a_is_nan = 1 if exp_a == 255 else 0
        exp_b_is_nan = 1 if exp_b == 255 else 0

        # Calculate raw sum (signed 10-bit to detect over/underflow)
        raw_sum = exp_a + exp_b + norm_adj - self.BIAS

        # Determine overflow/underflow
        either_special = (exp_a == 0) or (exp_b == 0) or (exp_a == 255) or (exp_b == 255)

        # Use signed comparison for underflow
        exp_underflow = 0
        exp_overflow = 0

        if not either_special:
            # Check underflow first (negative or zero result)
            if raw_sum <= 0:
                exp_underflow = 1
            # Check overflow only if not underflow (result > 254)
            elif raw_sum > 254:
                exp_overflow = 1

        # Expected output with saturation
        if exp_overflow:
            exp_exp_out = 255
        elif exp_underflow:
            exp_exp_out = 0
        else:
            exp_exp_out = raw_sum & 0xFF

        self.test_count += 1

        # Check all outputs
        passed = True
        errors = []

        if a_is_zero != exp_a_is_zero:
            passed = False
            errors.append(f"a_is_zero: got {a_is_zero}, expected {exp_a_is_zero}")

        if b_is_zero != exp_b_is_zero:
            passed = False
            errors.append(f"b_is_zero: got {b_is_zero}, expected {exp_b_is_zero}")

        if a_is_inf != exp_a_is_inf:
            passed = False
            errors.append(f"a_is_inf: got {a_is_inf}, expected {exp_a_is_inf}")

        if b_is_inf != exp_b_is_inf:
            passed = False
            errors.append(f"b_is_inf: got {b_is_inf}, expected {exp_b_is_inf}")

        if a_is_nan != exp_a_is_nan:
            passed = False
            errors.append(f"a_is_nan: got {a_is_nan}, expected {exp_a_is_nan}")

        if b_is_nan != exp_b_is_nan:
            passed = False
            errors.append(f"b_is_nan: got {b_is_nan}, expected {exp_b_is_nan}")

        if overflow != exp_overflow:
            passed = False
            errors.append(f"overflow: got {overflow}, expected {exp_overflow}")

        if underflow != exp_underflow:
            passed = False
            errors.append(f"underflow: got {underflow}, expected {exp_underflow}")

        if exp_out != exp_exp_out:
            passed = False
            errors.append(f"exp_out: got {exp_out}, expected {exp_exp_out}")

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            self.log.error(f"FAIL: exp_a={exp_a}, exp_b={exp_b}, norm_adj={norm_adj}")
            self.log.error(f"  raw_sum = {raw_sum}")
            for err in errors:
                self.log.error(f"  {err}")

        return passed

    async def run_comprehensive_tests(self):
        """Run comprehensive test suite based on test level."""
        test_level = self.test_level.lower()

        if test_level == 'simple':
            num_random = 20
        elif test_level == 'basic':
            num_random = 200
        elif test_level == 'medium':
            num_random = 1000
        else:  # full
            num_random = 5000

        # Special case tests - zeros
        self.log.info("Testing zero exponent cases...")
        zero_cases = [
            (0, 0, 0),      # Both zero
            (0, 127, 0),    # A is zero
            (127, 0, 0),    # B is zero
            (0, 255, 0),    # Zero x Inf
            (255, 0, 0),    # Inf x Zero
        ]
        for exp_a, exp_b, norm in zero_cases:
            passed = await self.test_single_exp_add(exp_a, exp_b, norm)
            if not passed:
                assert False, f"Zero case failed: exp_a={exp_a}, exp_b={exp_b}"

        # Special case tests - infinities
        self.log.info("Testing infinity exponent cases...")
        inf_cases = [
            (255, 255, 0),  # Inf x Inf
            (255, 127, 0),  # Inf x normal
            (127, 255, 0),  # normal x Inf
            (255, 1, 0),    # Inf x tiny
        ]
        for exp_a, exp_b, norm in inf_cases:
            passed = await self.test_single_exp_add(exp_a, exp_b, norm)
            if not passed:
                assert False, f"Inf case failed: exp_a={exp_a}, exp_b={exp_b}"

        self.log.info(f"Special cases: {self.pass_count}/{self.test_count} passed")

        # Normal multiplication cases - exp_a + exp_b - 127
        self.log.info("Testing normal exponent cases...")
        normal_cases = [
            (127, 127, 0),  # 1.0 x 1.0: 127 + 127 - 127 = 127
            (127, 127, 1),  # 1.0 x 1.0 + norm: 127 + 127 - 127 + 1 = 128
            (128, 128, 0),  # 2.0 x 2.0: 128 + 128 - 127 = 129
            (126, 126, 0),  # 0.5 x 0.5: 126 + 126 - 127 = 125
            (100, 100, 0),  # Small x Small: 100 + 100 - 127 = 73
            (150, 150, 0),  # Larger x Larger: 150 + 150 - 127 = 173
        ]
        for exp_a, exp_b, norm in normal_cases:
            passed = await self.test_single_exp_add(exp_a, exp_b, norm)
            if not passed:
                assert False, f"Normal case failed: exp_a={exp_a}, exp_b={exp_b}"

        # Overflow cases - result > 254
        self.log.info("Testing overflow cases...")
        overflow_cases = [
            (200, 200, 0),  # 200 + 200 - 127 = 273 > 254 -> overflow
            (254, 128, 0),  # 254 + 128 - 127 = 255 -> overflow (255 reserved for inf)
            (200, 182, 0),  # 200 + 182 - 127 = 255 -> overflow
            (250, 140, 0),  # 250 + 140 - 127 = 263 -> overflow
        ]
        for exp_a, exp_b, norm in overflow_cases:
            passed = await self.test_single_exp_add(exp_a, exp_b, norm)
            if not passed:
                assert False, f"Overflow case failed: exp_a={exp_a}, exp_b={exp_b}"

        # Underflow cases - result <= 0
        self.log.info("Testing underflow cases...")
        underflow_cases = [
            (1, 1, 0),      # 1 + 1 - 127 = -125 -> underflow
            (10, 10, 0),    # 10 + 10 - 127 = -107 -> underflow
            (50, 50, 0),    # 50 + 50 - 127 = -27 -> underflow
            (63, 64, 0),    # 63 + 64 - 127 = 0 -> underflow (0 is also underflow)
            (60, 60, 0),    # 60 + 60 - 127 = -7 -> underflow
        ]
        for exp_a, exp_b, norm in underflow_cases:
            passed = await self.test_single_exp_add(exp_a, exp_b, norm)
            if not passed:
                assert False, f"Underflow case failed: exp_a={exp_a}, exp_b={exp_b}"

        # Boundary cases - near overflow/underflow edge
        self.log.info("Testing boundary cases...")
        boundary_cases = [
            (127, 127, 0),   # 127 + 127 - 127 = 127 (no overflow)
            (127, 128, 0),   # 127 + 128 - 127 = 128 (no overflow)
            (190, 191, 0),   # 190 + 191 - 127 = 254 (right at boundary, no overflow)
            (190, 192, 0),   # 190 + 192 - 127 = 255 (overflow!)
            (64, 63, 0),     # 64 + 63 - 127 = 0 (underflow)
            (64, 64, 0),     # 64 + 64 - 127 = 1 (just above underflow)
            (65, 63, 0),     # 65 + 63 - 127 = 1 (just above underflow)
        ]
        for exp_a, exp_b, norm in boundary_cases:
            passed = await self.test_single_exp_add(exp_a, exp_b, norm)
            if not passed:
                assert False, f"Boundary case failed: exp_a={exp_a}, exp_b={exp_b}"

        # Norm adjust tests
        self.log.info("Testing normalization adjustment cases...")
        norm_cases = [
            (127, 127, 1),   # 127 + 127 - 127 + 1 = 128
            (190, 191, 1),   # 190 + 191 - 127 + 1 = 255 (overflow due to +1)
            (64, 64, 1),     # 64 + 64 - 127 + 1 = 2 (just above underflow)
            (63, 64, 1),     # 63 + 64 - 127 + 1 = 1 (saves from underflow)
        ]
        for exp_a, exp_b, norm in norm_cases:
            passed = await self.test_single_exp_add(exp_a, exp_b, norm)
            if not passed:
                assert False, f"Norm adjust case failed: exp_a={exp_a}, exp_b={exp_b}, norm={norm}"

        self.log.info(f"Structured tests: {self.pass_count}/{self.test_count} passed")

        # Random tests
        self.log.info(f"Running {num_random} random tests...")
        for i in range(num_random):
            exp_a = random.randint(0, 255)
            exp_b = random.randint(0, 255)
            norm_adj = random.randint(0, 1)

            passed = await self.test_single_exp_add(exp_a, exp_b, norm_adj)
            if not passed:
                assert False, f"Random test {i} failed"

            if i % max(1, num_random // 10) == 0:
                self.log.info(f"Progress: {i}/{num_random}")

        self.log.info(f"Final: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        assert self.fail_count == 0, f"Test failures: {self.fail_count}"


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def bf16_exponent_adder_test(dut):
    """Test the BF16 exponent adder"""
    tb = BF16ExponentAdderTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')

    tb.print_settings()
    tb.clear_interface()
    await tb.wait_time(1, 'ns')

    await tb.run_comprehensive_tests()


def get_test_params():
    """Generate test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [{'test_level': 'simple'}]
    elif reg_level == 'FUNC':
        return [{'test_level': 'basic'}]
    else:  # FULL
        return [{'test_level': 'medium'}]


@pytest.mark.parametrize("params", get_test_params())
def test_math_bf16_exponent_adder(request, params):
    """PyTest function to run the cocotb test for BF16 exponent adder."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_bf16_exponent_adder"
    toplevel = dut_name
    t_level = params['test_level']

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_level}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # BF16 exponent adder - standalone module
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_exponent_adder.sv"),
    ]

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    seed = random.randint(0, 100000)

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
