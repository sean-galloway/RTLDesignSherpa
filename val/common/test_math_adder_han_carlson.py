# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_adder_han_carlson
# Purpose: Test for the Han-Carlson prefix adder modules (16-bit and 48-bit).
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Test for the Han-Carlson prefix adder modules.

These adders are used in the BF16 FMA:
- 16-bit: Final CPA for BF16 mantissa result
- 48-bit: Wide adder for FMA accumulation
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from conftest import get_coverage_compile_args


class HanCarlsonAdderTB(TBBase):
    """Testbench for Han-Carlson prefix adder.

    Works with the interface:
    - i_a, i_b: N-bit inputs
    - i_cin: Carry input
    - ow_sum: N-bit sum output
    - ow_cout: Carry output
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test."""
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '16'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"Testing Han-Carlson Adder with N={self.N}")

    def print_settings(self):
        """Print testbench settings."""
        self.log.info(f"Han-Carlson Adder Testbench Settings:")
        self.log.info(f"  Width (N): {self.N}")
        self.log.info(f"  Test Level: {self.test_level}")
        self.log.info(f"  Seed: {self.seed}")

    def clear_interface(self):
        """Clear the DUT interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_cin.value = 0

    async def test_single_add(self, a: int, b: int, cin: int) -> bool:
        """Test a single addition operation."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        self.dut.i_cin.value = cin

        await self.wait_time(1, 'ns')

        ow_sum = int(self.dut.ow_sum.value)
        ow_cout = int(self.dut.ow_cout.value)

        # Calculate expected
        full_sum = a + b + cin
        expected_sum = full_sum & self.mask
        expected_cout = 1 if full_sum >= self.max_val else 0

        self.test_count += 1

        if ow_sum == expected_sum and ow_cout == expected_cout:
            self.pass_count += 1
            return True
        else:
            self.fail_count += 1
            self.log.error(f"FAIL: a=0x{a:X}, b=0x{b:X}, cin={cin}")
            self.log.error(f"  Expected: sum=0x{expected_sum:X}, cout={expected_cout}")
            self.log.error(f"  Actual:   sum=0x{ow_sum:X}, cout={ow_cout}")
            return False

    async def run_comprehensive_tests(self):
        """Run comprehensive test suite based on test level."""
        test_level = self.test_level.lower()

        if test_level == 'simple':
            num_random = 10
        elif test_level == 'basic':
            num_random = 100
        elif test_level == 'medium':
            num_random = 500
        else:  # full
            num_random = 1000

        # Edge case tests
        self.log.info("Testing edge cases...")
        edge_cases = [
            (0, 0, 0),
            (0, 0, 1),
            (self.mask, 0, 0),
            (self.mask, 0, 1),
            (0, self.mask, 0),
            (0, self.mask, 1),
            (self.mask, self.mask, 0),
            (self.mask, self.mask, 1),
            (self.mask // 2, self.mask // 2, 0),
            (self.mask // 2, self.mask // 2 + 1, 0),
        ]

        for a, b, cin in edge_cases:
            passed = await self.test_single_add(a, b, cin)
            if not passed:
                assert False, f"Edge case failed: a=0x{a:X}, b=0x{b:X}, cin={cin}"

        self.log.info(f"Edge cases: {self.pass_count}/{self.test_count} passed")

        # Random tests
        self.log.info(f"Running {num_random} random tests...")
        for i in range(num_random):
            a = random.randint(0, self.mask)
            b = random.randint(0, self.mask)
            cin = random.randint(0, 1)
            passed = await self.test_single_add(a, b, cin)
            if not passed:
                assert False, f"Random test {i} failed"

            if i % max(1, num_random // 10) == 0:
                self.log.info(f"Progress: {i}/{num_random}")

        self.log.info(f"Final: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        assert self.fail_count == 0, f"Test failures: {self.fail_count}"


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def han_carlson_adder_test(dut):
    """Test the Han-Carlson prefix adder"""
    tb = HanCarlsonAdderTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')

    tb.print_settings()
    tb.clear_interface()
    await tb.wait_time(1, 'ns')

    await tb.run_comprehensive_tests()


def get_adder_params():
    """Generate adder parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'width': 16, 'test_level': 'simple'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'width': 16, 'test_level': 'basic'},
            {'width': 48, 'test_level': 'basic'},
        ]
    else:  # FULL
        return [
            {'width': 16, 'test_level': 'medium'},
            {'width': 48, 'test_level': 'medium'},
        ]


@pytest.mark.parametrize("params", get_adder_params())
def test_math_adder_han_carlson(request, params):
    """PyTest function to run the cocotb test for Han-Carlson adder."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    width = params['width']
    dut_name = f"math_adder_han_carlson_{width:03d}"
    toplevel = dut_name
    t_level = params['test_level']

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_level}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Han-Carlson adder dependencies
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell_gray.sv"),
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

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

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
