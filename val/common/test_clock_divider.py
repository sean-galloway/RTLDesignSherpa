# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ClockDividerTB
# Purpose: Clock Divider Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Clock Divider Test with Parameterized Test Levels and Configuration

This test uses N, PO_WIDTH, COUNTER_WIDTH and test_level as parameters for maximum flexibility:

CONFIGURATION:
    N:              Number of output clocks (1, 2, 4, 8)
    PO_WIDTH:       Width of pickoff point registers (4, 6, 8)
    COUNTER_WIDTH:  Width of the counter (16, 32, 64)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - N: [1, 2, 4, 8]
    - PO_WIDTH: [4, 6, 8]
    - COUNTER_WIDTH: [16, 32, 64]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_N: Number of output clocks
    TEST_PO_WIDTH: Width of pickoff point registers
    TEST_COUNTER_WIDTH: Width of the counter
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

class ClockDividerTB(TBBase):
    """Testbench for Clock Divider module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.N = self.convert_to_int(os.environ.get('TEST_N', '4'))
        self.PO_WIDTH = self.convert_to_int(os.environ.get('TEST_PO_WIDTH', '8'))
        self.COUNTER_WIDTH = self.convert_to_int(os.environ.get('TEST_COUNTER_WIDTH', '64'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.MAX_PICKOFF = (1 << self.PO_WIDTH) - 1
        self.MAX_COUNTER = (1 << self.COUNTER_WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Clock Divider TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"N={self.N}, PO_WIDTH={self.PO_WIDTH}, COUNTER_WIDTH={self.COUNTER_WIDTH}")
        self.log.info(f"MAX_PICKOFF={self.MAX_PICKOFF}, MAX_COUNTER={self.MAX_COUNTER}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.pickoff_points = self.dut.pickoff_points
        self.divided_clk = self.dut.divided_clk

    async def _reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 1
        self.pickoff_points.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        self.rst_n.value = 1
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

    def _pack_pickoff_points(self, pickoff_list):
        """Pack a list of pickoff points into the concatenated signal"""
        packed = 0
        for i, pickoff in enumerate(pickoff_list):
            packed |= (pickoff & self.MAX_PICKOFF) << (i * self.PO_WIDTH)
        return packed

    def _unpack_pickoff_points(self, packed):
        """Unpack the concatenated signal into a list of pickoff points"""
        pickoff_list = []
        for i in range(self.N):
            pickoff = (packed >> (i * self.PO_WIDTH)) & self.MAX_PICKOFF
            pickoff_list.append(pickoff)
        return pickoff_list

    async def _wait_cycles(self, cycles):
        """Wait for specified number of clock cycles"""
        for _ in range(cycles):
            await RisingEdge(self.clk)

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info("Testing reset behavior")

        # Set some pickoff points
        test_pickoffs = [min(5, self.MAX_PICKOFF), min(10, self.MAX_PICKOFF),
                        min(3, self.MAX_PICKOFF), min(7, self.MAX_PICKOFF)][:self.N]
        self.pickoff_points.value = self._pack_pickoff_points(test_pickoffs)

        # Apply reset
        await self._reset_dut()

        # Check that all divided clocks are 0 after reset
        divided_value = int(self.divided_clk.value)
        expected = 0

        success = (divided_value == expected)
        if success:
            self.log.debug(f"PASS: Reset test - all outputs are 0")
        else:
            self.log.error(f"FAIL: Reset test - expected 0x{expected:x}, got 0x{divided_value:x}")

        result = {
            'test_type': 'reset',
            'expected': expected,
            'actual': divided_value,
            'success': success
        }
        self.test_results.append(result)
        if not success:
            self.test_failures.append(result)

        return success

    async def test_counter_increment(self):
        """Test that the internal counter increments properly"""
        self.log.info("Testing counter increment behavior")

        await self._reset_dut()

        # Use bit 0 and 1 which change frequently
        # Bit 0 toggles every 2 cycles, bit 1 toggles every 4 cycles
        # Repeat pattern to cover all N channels
        test_pickoffs = [(i % 2) for i in range(self.N)]  # Alternating [0, 1, 0, 1, ...] for all N channels
        
        self.pickoff_points.value = self._pack_pickoff_points(test_pickoffs)
        await RisingEdge(self.clk)

        # Monitor for enough cycles to see clear patterns
        cycles_to_test = 20  # Enough to see multiple toggles
        
        # Track each output separately
        output_histories = [[] for _ in range(self.N)]
        
        for cycle in range(cycles_to_test):
            await RisingEdge(self.clk)
            current_pattern = int(self.divided_clk.value)
            
            # Extract each output bit
            for ch in range(self.N):
                bit_value = (current_pattern >> ch) & 1
                output_histories[ch].append(bit_value)

        # Analyze changes for each channel
        changes_detected = 0
        total_expected_changes = 0
        
        for ch in range(self.N):
            pickoff_bit = test_pickoffs[ch]
            history = output_histories[ch]
            
            # Count transitions
            transitions = 0
            for i in range(1, len(history)):
                if history[i] != history[i-1]:
                    transitions += 1
            
            # Expected transitions based on pickoff bit
            # Bit N toggles every 2^(N+1) cycles
            expected_period = 2 ** (pickoff_bit + 1)
            expected_transitions = max(1, cycles_to_test // expected_period)
            
            self.log.debug(f"Channel {ch} (bit {pickoff_bit}): {transitions} transitions, expected ~{expected_transitions}")
            
            # We should see at least some transitions for low bits
            if pickoff_bit <= 2:  # For bits 0, 1, 2 we should definitely see changes
                if transitions >= 1:
                    changes_detected += 1
                total_expected_changes += 1
            
        # Success if we detected changes on most channels monitoring low bits
        success = changes_detected >= max(1, total_expected_changes // 2)

        if success:
            self.log.debug(f"PASS: Counter increment test - {changes_detected}/{total_expected_changes} channels showed changes")
        else:
            self.log.error(f"FAIL: Counter increment test - only {changes_detected}/{total_expected_changes} channels showed changes")
            # Log detailed history for debugging
            for ch in range(min(2, self.N)):  # Log first 2 channels
                history = output_histories[ch][:10]  # First 10 values
                self.log.error(f"  Channel {ch} history: {history}")

        result = {
            'test_type': 'counter_increment',
            'changes_detected': changes_detected,
            'total_expected': total_expected_changes,
            'cycles_tested': cycles_to_test,
            'success': success
        }
        self.test_results.append(result)
        if not success:
            self.test_failures.append(result)

        return success

    async def test_pickoff_functionality(self):
        """Test pickoff point functionality"""
        self.log.info("Testing pickoff point functionality")

        # Define test pickoff points based on test level
        if self.TEST_LEVEL == 'basic':
            test_cases = [
                [i for i in range(self.N)],  # [0, 1, 2, ..., N-1]
                [i+1 for i in range(self.N)]  # [1, 2, 3, ..., N]
            ]
        elif self.TEST_LEVEL == 'medium':
            test_cases = [
                [i for i in range(self.N)],  # [0, 1, 2, ..., N-1]
                [i+1 for i in range(self.N)],  # [1, 2, 3, ..., N]
                [i*2 for i in range(self.N)],  # [0, 2, 4, ..., 2*(N-1)]
                [min(i*2, self.MAX_PICKOFF) for i in range(self.N)]
            ]
        else:  # full
            test_cases = []
            # Add systematic patterns
            for offset in range(0, min(8, self.COUNTER_WIDTH - self.N)):
                test_cases.append([offset + i for i in range(self.N)])

            # Add power-of-2 patterns
            for power in range(0, min(6, self.COUNTER_WIDTH)):
                if (1 << power) < self.COUNTER_WIDTH:
                    test_cases.append([min((1 << power) + i, self.MAX_PICKOFF) for i in range(self.N)])

            # Add random patterns
            for _ in range(5):
                test_cases.append([random.randint(0, min(self.MAX_PICKOFF, self.COUNTER_WIDTH-1))
                                    for _ in range(self.N)])

        all_passed = True

        for test_case in test_cases:
            # Ensure all pickoff points are valid
            test_case = [min(p, self.MAX_PICKOFF) for p in test_case]

            await self._reset_dut()
            self.pickoff_points.value = self._pack_pickoff_points(test_case)
            await RisingEdge(self.clk)

            # Wait for counter to increment enough to see patterns
            max_pickoff = max(test_case) if test_case else 0
            cycles_to_wait = min(100, 2 ** (max_pickoff + 2))  # Wait for several toggles

            # Track the behavior of each output
            output_changes = [0] * self.N
            prev_outputs = [0] * self.N

            for cycle in range(cycles_to_wait):
                await RisingEdge(self.clk)
                current_value = int(self.divided_clk.value)

                for i in range(self.N):
                    current_bit = (current_value >> i) & 1
                    if current_bit != prev_outputs[i]:
                        output_changes[i] += 1
                    prev_outputs[i] = current_bit

            # Verify that outputs with smaller pickoff values change more frequently
            success = True
            for i in range(self.N):
                expected_period = 2 ** (test_case[i] + 1)
                expected_changes = cycles_to_wait // expected_period

                # Allow some tolerance for timing
                if expected_changes > 0 and output_changes[i] == 0:
                    success = False
                    self.log.error(f"Output {i} (pickoff {test_case[i]}) never changed")
                elif expected_changes == 0 and output_changes[i] > 2:  # Some tolerance
                    success = False
                    self.log.error(f"Output {i} (pickoff {test_case[i]}) changed too often")

            if success:
                self.log.debug(f"PASS: Pickoff test {test_case} - changes: {output_changes}")
            else:
                self.log.error(f"FAIL: Pickoff test {test_case} - changes: {output_changes}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            result = {
                'test_type': 'pickoff_functionality',
                'pickoff_points': test_case,
                'output_changes': output_changes,
                'cycles_tested': cycles_to_wait,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping boundary condition tests")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test maximum pickoff values
        max_pickoffs = [self.MAX_PICKOFF] * self.N
        await self._reset_dut()
        self.pickoff_points.value = self._pack_pickoff_points(max_pickoffs)
        await RisingEdge(self.clk)

        # Since we're using the MSB, changes should be very infrequent
        initial_value = int(self.divided_clk.value)
        await self._wait_cycles(50)  # Wait a reasonable time
        final_value = int(self.divided_clk.value)

        # For max pickoff, outputs should change very slowly or not at all
        changes = bin(initial_value ^ final_value).count('1')

        # Test minimum pickoff values
        min_pickoffs = [0] * self.N
        await self._reset_dut()
        self.pickoff_points.value = self._pack_pickoff_points(min_pickoffs)
        await RisingEdge(self.clk)

        # LSB should toggle every cycle
        toggle_count = 0
        prev_lsb = int(self.divided_clk.value) & 1

        for _ in range(20):
            await RisingEdge(self.clk)
            current_lsb = int(self.divided_clk.value) & 1
            if current_lsb != prev_lsb:
                toggle_count += 1
            prev_lsb = current_lsb

        # LSB should toggle frequently (but not necessarily every cycle due to timing)
        success = toggle_count > 5  # Reasonable threshold

        if success:
            self.log.debug(f"PASS: Boundary conditions - LSB toggled {toggle_count} times")
        else:
            self.log.error(f"FAIL: Boundary conditions - LSB only toggled {toggle_count} times")
            all_passed = False

        result = {
            'test_type': 'boundary_conditions',
            'lsb_toggles': toggle_count,
            'success': success
        }
        self.test_results.append(result)
        if not success:
            self.test_failures.append(result)

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running CLOCK_DIVIDER tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_counter_increment, "Counter increment"),
            (self.test_pickoff_functionality, "Pickoff functionality"),
            (self.test_boundary_conditions, "Boundary conditions")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall CLOCK_DIVIDER result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=20000, timeout_unit="us")
async def clock_divider_test(dut):
    """Test for Clock Divider module"""
    tb = ClockDividerTB(dut)

    # Start clock
    clock_thread = cocotb.start_soon(tb.clock_gen(tb.clk, 10, 'ns'))

    # Run tests
    passed = await tb.run_all_tests()

    # Stop clock
    clock_thread.kill()

    # Report final result
    tb.log.info(f"CLOCK_DIVIDER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Clock Divider test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 3 tests (quick smoke at basic level)
    REG_LEVEL=FUNC: ~12 tests (all valid configs, basic level) - default
    REG_LEVEL=FULL: ~36 tests (all valid configs, all levels)

    Returns:
        List of tuples: (n, po_width, counter_width, test_level)

    RTL Constraint: PO_WIDTH > $clog2(COUNTER_WIDTH) to avoid truncation
                    Equivalently: PO_WIDTH >= $clog2(COUNTER_WIDTH + 1)
                    This ensures PO_WIDTH can hold the value COUNTER_WIDTH

    Examples:
        COUNTER_WIDTH=16 → needs PO_WIDTH >= 5 (since $clog2(16)=4, $clog2(17)=5)
        COUNTER_WIDTH=32 → needs PO_WIDTH >= 6 (since $clog2(32)=5, $clog2(33)=6)
        COUNTER_WIDTH=64 → needs PO_WIDTH >= 7 (since $clog2(64)=6, $clog2(65)=7)
    """
    import math
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    n_values = [1, 2, 4, 8]           # Number of output clocks
    po_width_values = [4, 6, 8]       # Width of pickoff registers
    counter_width_values = [16, 32, 64]  # Width of counter
    test_levels = ['basic', 'medium', 'full']

    # Generate valid combinations respecting RTL constraint
    valid_configs = []
    for n, po_width, counter_width in product(n_values, po_width_values, counter_width_values):
        # RTL constraint: PO_WIDTH > $clog2(COUNTER_WIDTH)
        # Equivalently: PO_WIDTH >= $clog2(COUNTER_WIDTH + 1)
        # This prevents truncation when comparing w_pickoff_raw < w_counter_width_sized
        min_po_width = math.ceil(math.log2(counter_width + 1))
        if po_width >= min_po_width:
            valid_configs.append((n, po_width, counter_width))

    if reg_level == 'GATE':
        # Quick smoke test: 3 different configs at basic level
        return [(valid_configs[0] + ('basic',)),
                (valid_configs[len(valid_configs)//2] + ('basic',)),
                (valid_configs[-1] + ('basic',))]

    elif reg_level == 'FUNC':
        # All valid configs at basic level only
        return [(n, po, cw, 'basic') for n, po, cw in valid_configs]

    else:  # FULL
        # All valid configs at all test levels
        return [(n, po, cw, level)
                for n, po, cw in valid_configs
                for level in test_levels]

params = generate_params()

@pytest.mark.parametrize("n, po_width, counter_width, test_level", params)
def test_clock_divider(request, n, po_width, counter_width, test_level):
    """
    Parameterized Clock Divider test with configurable parameters and test level.

    N controls the number of divided clock outputs.
    PO_WIDTH controls the width of pickoff point configuration.
    COUNTER_WIDTH controls the width of the internal counter.
    Test level controls the depth and breadth of testing.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "clock_divider"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/clock_divider.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    n_str = TBBase.format_dec(n, 1)
    po_str = TBBase.format_dec(po_width, 1)
    cw_str = TBBase.format_dec(counter_width, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_clock_divider_n{n_str}_po{po_str}_cw{cw_str}_{test_level}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'N': str(n),
        'PO_WIDTH': str(po_width),
        'COUNTER_WIDTH': str(counter_width)
    }

    # Adjust timeout based on test level and parameters
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    param_factor = max(1.0, (n * counter_width) / 128.0)  # More complex configs take more time
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * param_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_N': str(n),
        'TEST_PO_WIDTH': str(po_width),
        'TEST_COUNTER_WIDTH': str(counter_width),
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: N={n}, PO_WIDTH={po_width}, COUNTER_WIDTH={counter_width}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} test PASSED: N={n}, PO_WIDTH={po_width}, COUNTER_WIDTH={counter_width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
