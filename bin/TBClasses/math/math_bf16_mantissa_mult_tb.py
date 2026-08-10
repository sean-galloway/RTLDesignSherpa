# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: BF16MantissaMultTB
# Purpose: Testbench for math_bf16_mantissa_mult
# Subsystem: framework
#
# Extracted from val/math/test_math_bf16_mantissa_mult.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from TBClasses.shared.tbbase import TBBase


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
        self.test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
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
            # TRUE sticky since MATH-001: the fold (guard|sticky) made RNE
            # ties-at-even round up in the consumer.
            exp_sticky = 1 if sticky_raw else 0
        else:
            # G=[6], R=[5], S=|[4:0]
            exp_round = (exp_product >> 5) & 1
            guard = (exp_product >> 6) & 1
            sticky_raw = (exp_product & 0x1F) != 0
            exp_sticky = 1 if sticky_raw else 0

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

        # Exhaustive or random tests based on test level
        if test_level in ['full', 'exhaustive']:
            # FULL: Exhaustive 128x128x4 = 65536 tests for complete coverage
            self.log.info("Running exhaustive tests (128 x 128 x 4 = 65536 cases)...")
            for mant_a in range(0x80):  # 7-bit mantissa: 0-127
                for mant_b in range(0x80):
                    for norm_combo in [(0, 0), (0, 1), (1, 0), (1, 1)]:
                        a_norm, b_norm = norm_combo
                        passed = await self.test_single_mult(mant_a, mant_b, a_norm, b_norm)
                        if not passed:
                            assert False, f"Exhaustive test failed: mant_a=0x{mant_a:02X}, mant_b=0x{mant_b:02X}"
                if mant_a % 16 == 0:
                    self.log.info(f"Exhaustive progress: {mant_a}/128")
        else:
            # Random tests with configured count
            if test_level == 'gate':
                num_random = 20
            else:  # func
                num_random = 100

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
