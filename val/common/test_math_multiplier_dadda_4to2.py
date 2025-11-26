# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_multiplier_dadda_4to2
# Purpose: Test for the Dadda 4:2 multiplier module (8-bit).
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Test for the Dadda 4:2 multiplier module.

This multiplier is used in the BF16 mantissa multiplication (8x8).
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class DaddaMultiplierTB(TBBase):
    """Testbench for Dadda 4:2 multiplier.

    Works with the interface:
    - i_multiplier: N-bit input
    - i_multiplicand: N-bit input
    - ow_product: 2N-bit output
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test."""
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '8'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.product_mask = (2**(2*self.N)) - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"Testing Dadda 4:2 Multiplier with N={self.N}")

    def print_settings(self):
        """Print testbench settings."""
        self.log.info(f"Dadda 4:2 Multiplier Testbench Settings:")
        self.log.info(f"  Width (N): {self.N}")
        self.log.info(f"  Test Level: {self.test_level}")
        self.log.info(f"  Seed: {self.seed}")

    def clear_interface(self):
        """Clear the DUT interface."""
        self.dut.i_multiplier.value = 0
        self.dut.i_multiplicand.value = 0

    async def test_single_mult(self, a: int, b: int) -> bool:
        """Test a single multiplication operation."""
        self.dut.i_multiplier.value = a
        self.dut.i_multiplicand.value = b

        await self.wait_time(1, 'ns')

        product = int(self.dut.ow_product.value)
        expected = (a * b) & self.product_mask

        self.test_count += 1

        if product == expected:
            self.pass_count += 1
            return True
        else:
            self.fail_count += 1
            self.log.error(f"FAIL: a=0x{a:02X}, b=0x{b:02X}")
            self.log.error(f"  Expected: product=0x{expected:04X}")
            self.log.error(f"  Actual:   product=0x{product:04X}")
            return False

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
            num_random = 1000

        # Edge case tests
        self.log.info("Testing edge cases...")
        edge_cases = [
            (0, 0),
            (0, 1),
            (1, 0),
            (1, 1),
            (self.mask, 0),
            (0, self.mask),
            (self.mask, 1),
            (1, self.mask),
            (self.mask, self.mask),
            (0x80, 0x80),  # 1.0 * 1.0 for BF16 mantissa
            (0xFF, 0xFF),  # Max * Max
            (0x55, 0xAA),  # Alternating bits
            (0xAA, 0x55),
        ]

        for a, b in edge_cases:
            passed = await self.test_single_mult(a, b)
            if not passed:
                assert False, f"Edge case failed: a=0x{a:02X}, b=0x{b:02X}"

        self.log.info(f"Edge cases: {self.pass_count}/{self.test_count} passed")

        # Exhaustive test for small multipliers (if test level allows)
        if test_level in ['medium', 'full'] and self.N <= 8:
            self.log.info(f"Running exhaustive test ({self.max_val}x{self.max_val} = {self.max_val**2} cases)...")
            for a in range(self.max_val):
                for b in range(self.max_val):
                    passed = await self.test_single_mult(a, b)
                    if not passed:
                        assert False, f"Exhaustive test failed: a=0x{a:02X}, b=0x{b:02X}"
                if a % max(1, self.max_val // 10) == 0:
                    self.log.info(f"Exhaustive progress: {a}/{self.max_val}")
        else:
            # Random tests
            self.log.info(f"Running {num_random} random tests...")
            for i in range(num_random):
                a = random.randint(0, self.mask)
                b = random.randint(0, self.mask)
                passed = await self.test_single_mult(a, b)
                if not passed:
                    assert False, f"Random test {i} failed"

                if i % max(1, num_random // 10) == 0:
                    self.log.info(f"Progress: {i}/{num_random}")

        self.log.info(f"Final: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        assert self.fail_count == 0, f"Test failures: {self.fail_count}"


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def dadda_multiplier_test(dut):
    """Test the Dadda 4:2 multiplier"""
    tb = DaddaMultiplierTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')

    tb.print_settings()
    tb.clear_interface()
    await tb.wait_time(1, 'ns')

    await tb.run_comprehensive_tests()


def get_multiplier_params():
    """Generate multiplier parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'width': 8, 'test_level': 'simple'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'width': 8, 'test_level': 'basic'},
        ]
    else:  # FULL
        return [
            {'width': 8, 'test_level': 'medium'},
        ]


@pytest.mark.parametrize("params", get_multiplier_params())
def test_math_multiplier_dadda_4to2(request, params):
    """PyTest function to run the cocotb test for Dadda multiplier."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    width = params['width']
    dut_name = f"math_multiplier_dadda_4to2_{width:03d}"
    toplevel = dut_name
    t_level = params['test_level']

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_level}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Dadda multiplier dependencies
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_compressor_4to2.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell_gray.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_han_carlson_016.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
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
        'PARAM_N': str(width),
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
            parameters={'N': width},
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
