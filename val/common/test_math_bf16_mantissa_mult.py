# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_bf16_mantissa_mult
# Purpose: Test for the BF16 mantissa multiplier module.
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Test for the BF16 mantissa multiplier module.

This multiplier handles 7-bit mantissa inputs with implied 1 handling,
producing a 16-bit product with normalization detection and rounding bits.
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class BF16MantissaMultTB(TBBase):
    """Testbench for BF16 mantissa multiplier.

    Works with the interface:
    - i_mant_a: 7-bit mantissa A
    - i_mant_b: 7-bit mantissa B
    - i_a_is_normal: 1 if A is normalized (has implied 1)
    - i_b_is_normal: 1 if B is normalized (has implied 1)
    - ow_product: 16-bit raw product
    - ow_needs_norm: 1 if product needs normalization (shift right)
    - ow_mant_out: 7-bit extracted mantissa
    - ow_round_bit: rounding bit for RNE
    - ow_sticky_bit: sticky bit for RNE
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test."""
        TBBase.__init__(self, dut)
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info("Testing BF16 Mantissa Multiplier")

    def print_settings(self):
        """Print testbench settings."""
        self.log.info("BF16 Mantissa Multiplier Testbench Settings:")
        self.log.info(f"  Test Level: {self.test_level}")
        self.log.info(f"  Seed: {self.seed}")

    def clear_interface(self):
        """Clear the DUT interface."""
        self.dut.i_mant_a.value = 0
        self.dut.i_mant_b.value = 0
        self.dut.i_a_is_normal.value = 0
        self.dut.i_b_is_normal.value = 0

    async def test_single_mult(self, mant_a: int, mant_b: int,
                                a_normal: int, b_normal: int) -> bool:
        """Test a single mantissa multiplication."""
        self.dut.i_mant_a.value = mant_a
        self.dut.i_mant_b.value = mant_b
        self.dut.i_a_is_normal.value = a_normal
        self.dut.i_b_is_normal.value = b_normal

        await self.wait_time(1, 'ns')

        # Get DUT outputs
        product = int(self.dut.ow_product.value)
        needs_norm = int(self.dut.ow_needs_norm.value)
        mant_out = int(self.dut.ow_mant_out.value)
        round_bit = int(self.dut.ow_round_bit.value)
        sticky_bit = int(self.dut.ow_sticky_bit.value)

        # Calculate expected values
        # Extend mantissa with implied 1 for normalized numbers
        ext_a = (a_normal << 7) | mant_a
        ext_b = (b_normal << 7) | mant_b
        exp_product = ext_a * ext_b

        # Normalization detection
        exp_needs_norm = 1 if (exp_product & 0x8000) else 0

        # Expected mantissa extraction
        if exp_needs_norm:
            exp_mant_out = (exp_product >> 8) & 0x7F
        else:
            exp_mant_out = (exp_product >> 7) & 0x7F

        # Expected rounding bits
        if exp_needs_norm:
            # G=[7], R=[6], S=|[5:0]
            exp_round = (exp_product >> 6) & 1
            guard = (exp_product >> 7) & 1
            sticky_raw = (exp_product & 0x3F) != 0
            exp_sticky = 1 if (guard or sticky_raw) else 0
        else:
            # G=[6], R=[5], S=|[4:0]
            exp_round = (exp_product >> 5) & 1
            guard = (exp_product >> 6) & 1
            sticky_raw = (exp_product & 0x1F) != 0
            exp_sticky = 1 if (guard or sticky_raw) else 0

        self.test_count += 1

        # Check all outputs
        passed = True
        errors = []

        if product != exp_product:
            passed = False
            errors.append(f"product: got 0x{product:04X}, expected 0x{exp_product:04X}")

        if needs_norm != exp_needs_norm:
            passed = False
            errors.append(f"needs_norm: got {needs_norm}, expected {exp_needs_norm}")

        if mant_out != exp_mant_out:
            passed = False
            errors.append(f"mant_out: got 0x{mant_out:02X}, expected 0x{exp_mant_out:02X}")

        if round_bit != exp_round:
            passed = False
            errors.append(f"round_bit: got {round_bit}, expected {exp_round}")

        if sticky_bit != exp_sticky:
            passed = False
            errors.append(f"sticky_bit: got {sticky_bit}, expected {exp_sticky}")

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            self.log.error(f"FAIL: mant_a=0x{mant_a:02X}, mant_b=0x{mant_b:02X}, "
                          f"a_norm={a_normal}, b_norm={b_normal}")
            self.log.error(f"  ext_a=0x{ext_a:02X}, ext_b=0x{ext_b:02X}")
            for err in errors:
                self.log.error(f"  {err}")

        return passed

    async def run_comprehensive_tests(self):
        """Run comprehensive test suite based on test level."""
        test_level = self.test_level.lower()

        if test_level == 'simple':
            num_random = 20
        elif test_level == 'basic':
            num_random = 100
        elif test_level == 'medium':
            num_random = 500
        else:  # full
            num_random = 2000

        # Edge cases - normalized x normalized
        self.log.info("Testing edge cases (normalized x normalized)...")
        norm_edge_cases = [
            (0x00, 0x00),  # 1.0000000 * 1.0000000
            (0x00, 0x7F),  # 1.0000000 * 1.1111111
            (0x7F, 0x00),  # 1.1111111 * 1.0000000
            (0x7F, 0x7F),  # 1.1111111 * 1.1111111 (max)
            (0x40, 0x40),  # 1.1000000 * 1.1000000
            (0x55, 0x2A),  # Alternating bits
            (0x2A, 0x55),
        ]

        for mant_a, mant_b in norm_edge_cases:
            passed = await self.test_single_mult(mant_a, mant_b, 1, 1)
            if not passed:
                assert False, f"Edge case failed: mant_a=0x{mant_a:02X}, mant_b=0x{mant_b:02X}"

        self.log.info(f"Edge cases (norm x norm): {self.pass_count}/{self.test_count} passed")

        # Denormal cases - one or both operands are subnormal
        self.log.info("Testing denormal cases...")
        denorm_cases = [
            (0x00, 0x00, 0, 0),  # 0.0000000 * 0.0000000 = 0
            (0x7F, 0x7F, 0, 0),  # 0.1111111 * 0.1111111
            (0x00, 0x7F, 1, 0),  # 1.0000000 * 0.1111111
            (0x7F, 0x00, 0, 1),  # 0.1111111 * 1.0000000
            (0x40, 0x40, 0, 1),  # 0.1000000 * 1.1000000
            (0x40, 0x40, 1, 0),  # 1.1000000 * 0.1000000
        ]

        for mant_a, mant_b, a_norm, b_norm in denorm_cases:
            passed = await self.test_single_mult(mant_a, mant_b, a_norm, b_norm)
            if not passed:
                assert False, f"Denormal case failed"

        self.log.info(f"Denormal cases: {self.pass_count}/{self.test_count} passed")

        # Specific product range tests (to verify normalization)
        self.log.info("Testing normalization boundary cases...")
        # 1.0 * 1.0 = 1.0 (no norm needed, product = 0x4000)
        passed = await self.test_single_mult(0x00, 0x00, 1, 1)
        if not passed:
            assert False, "1.0 * 1.0 failed"

        # ~1.0 * ~2.0 = ~2.0 (needs norm, product >= 0x8000)
        # 1.0 * 1.999 = 1.999 (no norm)
        # 1.5 * 1.5 = 2.25 (needs norm)
        passed = await self.test_single_mult(0x40, 0x40, 1, 1)  # 1.5 * 1.5
        if not passed:
            assert False, "1.5 * 1.5 failed"

        self.log.info(f"Normalization cases: {self.pass_count}/{self.test_count} passed")

        # Random tests with all combinations of normal flags
        self.log.info(f"Running {num_random} random tests...")
        for i in range(num_random):
            mant_a = random.randint(0, 0x7F)
            mant_b = random.randint(0, 0x7F)
            a_norm = random.randint(0, 1)
            b_norm = random.randint(0, 1)

            passed = await self.test_single_mult(mant_a, mant_b, a_norm, b_norm)
            if not passed:
                assert False, f"Random test {i} failed"

            if i % max(1, num_random // 10) == 0:
                self.log.info(f"Progress: {i}/{num_random}")

        self.log.info(f"Final: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        assert self.fail_count == 0, f"Test failures: {self.fail_count}"


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def bf16_mantissa_mult_test(dut):
    """Test the BF16 mantissa multiplier"""
    tb = BF16MantissaMultTB(dut)

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
def test_math_bf16_mantissa_mult(request, params):
    """PyTest function to run the cocotb test for BF16 mantissa multiplier."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_bf16_mantissa_mult"
    toplevel = dut_name
    t_level = params['test_level']

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_level}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # BF16 mantissa multiplier dependencies
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_compressor_4to2.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell_gray.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_han_carlson_016.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_multiplier_dadda_4to2_008.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_mantissa_mult.sv"),
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
