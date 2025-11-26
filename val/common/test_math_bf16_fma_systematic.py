# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_bf16_fma_systematic
# Purpose: Systematic edge-case testing for BF16 FMA around power-of-2 boundaries.
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Systematic Edge-Case Test for BF16 FMA.

This test systematically explores all combinations of power-of-2 boundary values
for the BF16 FMA. By testing at exponent boundaries (2^n - 1, 2^n, 2^n + 1),
we catch edge cases in:
- Exponent calculation and bias handling
- Mantissa normalization
- Overflow/underflow detection
- Rounding at boundaries

The test uses itertools.product to exhaustively cover all combinations,
making it easy to identify pass/fail patterns around specific boundaries.
"""
import os
import random
import struct
import itertools
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class BF16FMASystematicTB(TBBase):
    """Systematic testbench for BF16 FMA edge cases."""

    def __init__(self, dut):
        """Initialize the testbench."""
        TBBase.__init__(self, dut)
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.failures = []

    @staticmethod
    def float_to_bf16(f: float) -> int:
        """Convert Python float to BF16 bit representation."""
        if f != f:  # NaN
            return 0x7FC0
        fp32_bytes = struct.pack('>f', f)
        fp32_bits = struct.unpack('>I', fp32_bytes)[0]
        return (fp32_bits >> 16) & 0xFFFF

    @staticmethod
    def bf16_to_float(bf16: int) -> float:
        """Convert BF16 bit representation to Python float."""
        fp32_bits = (bf16 & 0xFFFF) << 16
        fp32_bytes = struct.pack('>I', fp32_bits)
        return struct.unpack('>f', fp32_bytes)[0]

    @staticmethod
    def float_to_fp32(f: float) -> int:
        """Convert Python float to FP32 bit representation."""
        fp32_bytes = struct.pack('>f', f)
        return struct.unpack('>I', fp32_bytes)[0]

    @staticmethod
    def fp32_to_float(fp32: int) -> float:
        """Convert FP32 bit representation to Python float."""
        fp32_bytes = struct.pack('>I', fp32 & 0xFFFFFFFF)
        return struct.unpack('>f', fp32_bytes)[0]

    def _compute_expected_fma(self, a_bf16: int, b_bf16: int, c_fp32: int):
        """Compute expected FMA result using Python floats."""
        a_float = self.bf16_to_float(a_bf16)
        b_float = self.bf16_to_float(b_bf16)
        c_float = self.fp32_to_float(c_fp32)

        # Check for special values
        a_exp = (a_bf16 >> 7) & 0xFF
        b_exp = (b_bf16 >> 7) & 0xFF
        a_mant = a_bf16 & 0x7F
        b_mant = b_bf16 & 0x7F

        c_exp = (c_fp32 >> 23) & 0xFF
        c_mant = c_fp32 & 0x7FFFFF

        a_is_zero = (a_bf16 & 0x7FFF) == 0 or (a_exp == 0)
        b_is_zero = (b_bf16 & 0x7FFF) == 0 or (b_exp == 0)
        a_is_inf = a_exp == 0xFF and a_mant == 0
        b_is_inf = b_exp == 0xFF and b_mant == 0
        a_is_nan = a_exp == 0xFF and a_mant != 0
        b_is_nan = b_exp == 0xFF and b_mant != 0

        c_is_zero = (c_fp32 & 0x7FFFFFFF) == 0 or (c_exp == 0)
        c_is_inf = c_exp == 0xFF and c_mant == 0
        c_is_nan = c_exp == 0xFF and c_mant != 0

        sign_a = (a_bf16 >> 15) & 1
        sign_b = (b_bf16 >> 15) & 1
        sign_c = (c_fp32 >> 31) & 1
        prod_sign = sign_a ^ sign_b

        # Invalid operations
        invalid_mul = (a_is_zero and b_is_inf) or (b_is_zero and a_is_inf)
        prod_is_inf = a_is_inf or b_is_inf
        invalid_add = prod_is_inf and c_is_inf and (prod_sign != sign_c)
        invalid = invalid_mul or invalid_add
        any_nan = a_is_nan or b_is_nan or c_is_nan

        if any_nan or invalid:
            return 0x7FC00000, False, False, invalid

        if prod_is_inf and not c_is_inf:
            return (prod_sign << 31) | 0x7F800000, False, False, False

        if c_is_inf:
            return c_fp32, False, False, False

        if a_is_zero or b_is_zero:
            if c_is_zero:
                return (prod_sign & sign_c) << 31, False, False, False
            return c_fp32, False, False, False

        if c_is_zero:
            result_float = a_float * b_float
        else:
            result_float = (a_float * b_float) + c_float

        # Check overflow/underflow
        abs_result = abs(result_float)
        if abs_result > 3.4e38:
            sign = 1 if result_float < 0 else 0
            return (sign << 31) | 0x7F800000, True, False, False

        if abs_result < 1.17e-38 and abs_result > 0:
            sign = 1 if result_float < 0 else 0
            return sign << 31, False, True, False

        if result_float == 0:
            return 0, False, False, False

        return self.float_to_fp32(result_float), False, False, False

    async def test_single_fma(self, a_bf16: int, b_bf16: int, c_fp32: int,
                               a_name: str, b_name: str, c_name: str) -> bool:
        """Test a single FMA operation with named values."""
        self.dut.i_a.value = a_bf16
        self.dut.i_b.value = b_bf16
        self.dut.i_c.value = c_fp32

        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        invalid = int(self.dut.ow_invalid.value)

        exp_result, exp_overflow, exp_underflow, exp_invalid = \
            self._compute_expected_fma(a_bf16, b_bf16, c_fp32)

        self.test_count += 1

        # NaN check
        result_is_nan = (result & 0x7F800000) == 0x7F800000 and (result & 0x007FFFFF) != 0
        exp_is_nan = (exp_result & 0x7F800000) == 0x7F800000 and (exp_result & 0x007FFFFF) != 0

        if result_is_nan and exp_is_nan:
            passed = True
        elif result == exp_result:
            passed = True
        else:
            # Allow 1 ULP difference
            diff = abs(int(result) - int(exp_result))
            passed = diff <= 1

        # Check flags
        if overflow != exp_overflow or underflow != exp_underflow or invalid != exp_invalid:
            passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            a_float = self.bf16_to_float(a_bf16)
            b_float = self.bf16_to_float(b_bf16)
            c_float = self.fp32_to_float(c_fp32)
            exp_float = self.fp32_to_float(exp_result)
            act_float = self.fp32_to_float(result)

            failure_info = {
                'a_name': a_name, 'b_name': b_name, 'c_name': c_name,
                'a_bf16': a_bf16, 'b_bf16': b_bf16, 'c_fp32': c_fp32,
                'a_float': a_float, 'b_float': b_float, 'c_float': c_float,
                'exp_result': exp_result, 'act_result': result,
                'exp_float': exp_float, 'act_float': act_float,
                'exp_flags': (exp_overflow, exp_underflow, exp_invalid),
                'act_flags': (overflow, underflow, invalid),
            }
            self.failures.append(failure_info)

        return passed

    def generate_bf16_power2_values(self):
        """Generate BF16 values around powers of 2.

        Returns list of (name, bf16_value) tuples.
        """
        values = []

        # Zero
        values.append(("0", 0x0000))

        # One and nearby
        values.append(("1", 0x3F80))

        # Powers of 2 from 2^-4 to 2^4
        for exp_offset in range(-4, 5):
            # BF16 exponent = 127 + exp_offset
            bf16_exp = 127 + exp_offset
            if bf16_exp < 1 or bf16_exp > 254:
                continue

            base = bf16_exp << 7  # Mantissa = 0 means 1.0 * 2^(exp-127)
            power = 2 ** exp_offset

            # Exact power of 2
            values.append((f"2^{exp_offset}", base))

            # Power of 2 - 1 ULP (mantissa = 0x7F, exponent - 1)
            if bf16_exp > 1:
                minus_ulp = ((bf16_exp - 1) << 7) | 0x7F
                values.append((f"2^{exp_offset}-ulp", minus_ulp))

            # Power of 2 + 1 ULP (mantissa = 0x01)
            plus_ulp = base | 0x01
            values.append((f"2^{exp_offset}+ulp", plus_ulp))

        # Add some negative versions
        neg_values = []
        for name, val in values:
            if val != 0:
                neg_values.append((f"-{name}", val | 0x8000))
        values.extend(neg_values)

        return values

    def generate_fp32_power2_values(self):
        """Generate FP32 values around powers of 2.

        Returns list of (name, fp32_value) tuples.
        """
        values = []

        # Zero
        values.append(("0", 0x00000000))

        # One
        values.append(("1", 0x3F800000))

        # Powers of 2 from 2^-4 to 2^4
        for exp_offset in range(-4, 5):
            fp32_exp = 127 + exp_offset
            if fp32_exp < 1 or fp32_exp > 254:
                continue

            base = fp32_exp << 23

            # Exact power of 2
            values.append((f"2^{exp_offset}", base))

            # Power of 2 - 1 ULP
            if fp32_exp > 1:
                minus_ulp = ((fp32_exp - 1) << 23) | 0x7FFFFF
                values.append((f"2^{exp_offset}-ulp", minus_ulp))

            # Power of 2 + 1 ULP
            plus_ulp = base | 0x01
            values.append((f"2^{exp_offset}+ulp", plus_ulp))

        # Add some negative versions
        neg_values = []
        for name, val in values:
            if val != 0:
                neg_values.append((f"-{name}", val | 0x80000000))
        values.extend(neg_values)

        return values

    async def run_systematic_tests(self):
        """Run systematic power-of-2 boundary tests."""
        self.log.info("=" * 60)
        self.log.info("BF16 FMA Systematic Power-of-2 Boundary Test")
        self.log.info("=" * 60)

        bf16_values = self.generate_bf16_power2_values()
        fp32_values = self.generate_fp32_power2_values()

        self.log.info(f"BF16 test values: {len(bf16_values)}")
        self.log.info(f"FP32 test values: {len(fp32_values)}")

        # For BF16 a and b, use a subset to keep test manageable
        # Full test would be len(bf16)^2 * len(fp32) combinations
        # Use smaller lists for a and b
        bf16_core = [(n, v) for n, v in bf16_values if 'ulp' not in n]
        self.log.info(f"BF16 core values (no ULP variants): {len(bf16_core)}")

        total_combinations = len(bf16_core) * len(bf16_core) * len(fp32_values)
        self.log.info(f"Total combinations to test: {total_combinations}")
        self.log.info("-" * 60)

        # Test all combinations
        progress_interval = max(1, total_combinations // 20)
        test_num = 0

        for (a_name, a_val), (b_name, b_val) in itertools.product(bf16_core, bf16_core):
            for c_name, c_val in fp32_values:
                await self.test_single_fma(a_val, b_val, c_val, a_name, b_name, c_name)
                test_num += 1
                if test_num % progress_interval == 0:
                    self.log.info(f"Progress: {test_num}/{total_combinations} "
                                 f"({100*test_num//total_combinations}%) - "
                                 f"Pass: {self.pass_count}, Fail: {self.fail_count}")

        self.log.info("=" * 60)
        self.log.info("Test Summary")
        self.log.info("=" * 60)
        self.log.info(f"Total tests: {self.test_count}")
        self.log.info(f"Passed: {self.pass_count}")
        self.log.info(f"Failed: {self.fail_count}")
        self.log.info(f"Pass rate: {100*self.pass_count/max(1,self.test_count):.2f}%")

        if self.failures:
            self.log.info("-" * 60)
            self.log.info("Failure Analysis")
            self.log.info("-" * 60)

            # Group failures by pattern
            failure_patterns = {}
            for f in self.failures:
                pattern = f"{f['a_name']} * {f['b_name']} + {f['c_name']}"
                if pattern not in failure_patterns:
                    failure_patterns[pattern] = []
                failure_patterns[pattern].append(f)

            self.log.info(f"Unique failure patterns: {len(failure_patterns)}")

            # Show first 20 failure patterns
            for i, (pattern, failures) in enumerate(list(failure_patterns.items())[:20]):
                f = failures[0]
                self.log.error(f"Pattern {i+1}: {pattern}")
                self.log.error(f"  a=0x{f['a_bf16']:04X} ({f['a_float']}), "
                              f"b=0x{f['b_bf16']:04X} ({f['b_float']}), "
                              f"c=0x{f['c_fp32']:08X} ({f['c_float']})")
                self.log.error(f"  Expected: 0x{f['exp_result']:08X} ({f['exp_float']})")
                self.log.error(f"  Actual:   0x{f['act_result']:08X} ({f['act_float']})")
                self.log.error(f"  Flags exp: ovf={f['exp_flags'][0]}, udf={f['exp_flags'][1]}, inv={f['exp_flags'][2]}")
                self.log.error(f"  Flags act: ovf={f['act_flags'][0]}, udf={f['act_flags'][1]}, inv={f['act_flags'][2]}")

            if len(failure_patterns) > 20:
                self.log.error(f"... and {len(failure_patterns) - 20} more patterns")

        return self.fail_count == 0


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def bf16_fma_systematic_test(dut):
    """Systematic power-of-2 boundary test for BF16 FMA."""
    tb = BF16FMASystematicTB(dut)

    await tb.wait_time(1, 'ns')

    passed = await tb.run_systematic_tests()

    assert passed, f"Systematic test failed with {tb.fail_count} failures"


def get_test_params():
    """Generate test parameters."""
    return [{'test_level': 'systematic'}]


@pytest.mark.parametrize("params", get_test_params())
def test_math_bf16_fma_systematic(request, params):
    """PyTest wrapper for systematic BF16 FMA test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_bf16_fma"
    toplevel = dut_name

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_systematic_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_compressor_4to2.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell_gray.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "count_leading_zeros.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_han_carlson_016.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_han_carlson_048.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_multiplier_dadda_4to2_008.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_fma.sv"),
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
    plusargs = ["--trace"]

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
        print(f"To view waveforms: {cmd_filename}")
        raise
