# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DebounceTB
# Purpose: Debounce Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Debounce Test with Parameterized Test Levels and Configuration

This test uses num_buttons, debounce_delay, pressed_state and test_level as parameters:

CONFIGURATION:
    num_buttons:     Number of button inputs (1, 2, 4, 8)
    debounce_delay:  Debounce delay in tick cycles (2, 4, 8)
    pressed_state:   State when button is pressed (0=NC, 1=NO)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_NUM_BUTTONS: Number of button inputs
    TEST_DEBOUNCE_DELAY: Debounce delay in cycles
    TEST_PRESSED_STATE: Pressed state (0 or 1)
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from conftest import get_coverage_compile_args

class DebounceTB(TBBase):
    """Testbench for Debounce module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.NUM_BUTTONS = self.convert_to_int(os.environ.get('TEST_NUM_BUTTONS', '4'))
        self.DEBOUNCE_DELAY = self.convert_to_int(os.environ.get('TEST_DEBOUNCE_DELAY', '4'))
        self.PRESSED_STATE = self.convert_to_int(os.environ.get('TEST_PRESSED_STATE', '1'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Debounce TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}{self.get_time_ns_str()}")
        self.log.info(f"NUM_BUTTONS={self.NUM_BUTTONS}, DEBOUNCE_DELAY={self.DEBOUNCE_DELAY}{self.get_time_ns_str()}")
        self.log.info(f"PRESSED_STATE={self.PRESSED_STATE}{self.get_time_ns_str()}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

    def get_time_ns_str(self):
        """Get current simulation time as formatted string"""
        try:
            import cocotb
            current_time = cocotb.utils.get_sim_time(units='ns')
            return f" @ {current_time}ns"
        except:
            return ""

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.long_tick = self.dut.long_tick
        self.button_in = self.dut.button_in
        self.button_out = self.dut.button_out

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.long_tick.value = 0
        self.button_in.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1

        # Set initial button state based on PRESSED_STATE
        if self.PRESSED_STATE == 1:  # Normal Open
            self.button_in.value = 0  # Released state = 0
        else:  # Normal Closed
            self.button_in.value = (1 << self.NUM_BUTTONS) - 1  # Released state = all 1s

        await RisingEdge(self.clk)

    async def send_long_tick(self):
        """Send a long_tick pulse"""
        self.long_tick.value = 1
        await RisingEdge(self.clk)
        self.long_tick.value = 0
        await RisingEdge(self.clk)

    def get_button_output(self):
        """Get the debounced button output"""
        try:
            return int(self.button_out.value)
        except:
            return 0

    async def test_basic_debouncing(self):
        """Test basic debouncing functionality"""
        self.log.info(f"Testing basic debouncing{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test each button individually based on test level
        if self.TEST_LEVEL == 'basic':
            test_buttons = [0] if self.NUM_BUTTONS > 0 else []
        elif self.TEST_LEVEL == 'medium':
            test_buttons = list(range(min(2, self.NUM_BUTTONS)))
        else:  # full
            test_buttons = list(range(self.NUM_BUTTONS))

        for button_idx in test_buttons:
            self.log.debug(f"Testing button {button_idx}{self.get_time_ns_str()}")

            # Establish stable released state first
            if self.PRESSED_STATE == 1:  # Normal Open
                release_value = 0
            else:  # Normal Closed
                release_value = (1 << self.NUM_BUTTONS) - 1  # All buttons released = all 1s

            self.button_in.value = release_value

            # Send enough ticks to establish stable released state
            for tick in range(self.DEBOUNCE_DELAY + 2):
                await self.send_long_tick()

            # Check initial state - should be 0 (no buttons pressed)
            initial_output = self.get_button_output()
            if initial_output != 0:
                self.log.error(f"Initial state not clear: output=0x{initial_output:x}, expected=0x0{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Test button press
            button_mask = 1 << button_idx if button_idx < self.NUM_BUTTONS else 0

            if self.PRESSED_STATE == 1:  # Normal Open
                press_value = button_mask  # Press = set bit
            else:  # Normal Closed
                press_value = release_value & ~button_mask  # Press = clear bit

            # Apply button press
            self.button_in.value = press_value

            # Send enough ticks for debouncing
            for tick in range(self.DEBOUNCE_DELAY + 1):
                await self.send_long_tick()

            # Check output - should show button pressed
            output_after_press = self.get_button_output()
            expected_press_output = button_mask  # Always expect 1 for pressed button

            if (output_after_press & button_mask) != expected_press_output:
                self.log.error(f"Button {button_idx} press: output=0x{output_after_press:x}, expected bit {button_idx} set{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Test button release
            self.button_in.value = release_value

            # Send enough ticks for debouncing
            for tick in range(self.DEBOUNCE_DELAY + 1):
                await self.send_long_tick()

            # Check output - should show button released (that bit should be 0)
            output_after_release = self.get_button_output()
            if (output_after_release & button_mask) != 0:
                self.log.error(f"Button {button_idx} release: output=0x{output_after_release:x}, expected bit {button_idx} clear{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            self.log.debug(f"Button {button_idx} test passed: press=0x{output_after_press:x}, release=0x{output_after_release:x}{self.get_time_ns_str()}")

            # Store result
            result = {
                'test_type': 'basic_debouncing',
                'button_idx': button_idx,
                'success': True
            }
            self.test_results.append(result)

        return all_passed

    async def test_bouncing_signals(self):
        """Test rejection of bouncing signals"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping bouncing signal tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing bouncing signal rejection{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test button 0 with bouncing
        button_mask = 1 if self.NUM_BUTTONS > 0 else 0

        # Establish proper initial state based on button type
        if self.PRESSED_STATE == 1:  # Normal Open
            initial_state = 0          # Released = 0
            bounce_press = button_mask # Pressed = 1
        else:  # Normal Closed
            initial_state = (1 << self.NUM_BUTTONS) - 1  # Released = all 1s
            bounce_press = initial_state & ~button_mask   # Pressed = clear bit

        # Start with stable released state
        self.button_in.value = initial_state
        for tick in range(self.DEBOUNCE_DELAY + 2):
            await self.send_long_tick()

        # Record initial stable output (should be all buttons released = 0)
        initial_output = self.get_button_output()

        # Create bouncing pattern: press, release, press, release, then stable press
        bounce_pattern = [bounce_press, initial_state, bounce_press, initial_state, bounce_press]

        for i, pattern in enumerate(bounce_pattern):
            self.button_in.value = pattern
            await self.send_long_tick()

            output = self.get_button_output()

            # During bouncing (first 4 steps), output should remain stable
            if i < len(bounce_pattern) - 1:  # During bouncing
                # The output should not show the button as fully pressed yet
                # Allow some intermediate states but not the final stable pressed state
                if i < self.DEBOUNCE_DELAY:
                    # During initial bouncing, output should be close to initial state
                    if output == button_mask:  # Full stable press detected too early
                        self.log.error(f"Button registered as pressed too early during bouncing at step {i}: 0x{output:x}{self.get_time_ns_str()}")
                        all_passed = False
                        break
                else:
                    # Later in bouncing, allow some change but not full stability
                    pass  # Some change is acceptable as shift register transitions

        # After stable signal, continue for full debounce delay
        for tick in range(self.DEBOUNCE_DELAY):
            await self.send_long_tick()

        # Now output should show stable pressed state
        final_output = self.get_button_output()
        if (final_output & button_mask) == 0:
            self.log.error(f"Button not detected as pressed after stable signal: 0x{final_output:x}{self.get_time_ns_str()}")
            all_passed = False
        else:
            self.log.debug(f"Bouncing test passed: initial=0x{initial_output:x}, final=0x{final_output:x}{self.get_time_ns_str()}")

        # Store result
        result = {
            'test_type': 'bouncing_signals',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_multiple_buttons(self):
        """Test multiple buttons simultaneously"""
        if self.TEST_LEVEL == 'basic' or self.NUM_BUTTONS == 1:
            self.log.info(f"Skipping multiple button tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing multiple buttons{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test all buttons pressed simultaneously
        all_buttons_mask = (1 << self.NUM_BUTTONS) - 1

        if self.PRESSED_STATE == 1:  # Normal Open
            press_input = all_buttons_mask  # All buttons = 1 when pressed
            release_input = 0               # All buttons = 0 when released
        else:  # Normal Closed
            press_input = 0                 # All buttons = 0 when pressed (inverted)
            release_input = all_buttons_mask # All buttons = 1 when released (inverted)

        # Press all buttons
        self.button_in.value = press_input

        # Send enough ticks for debouncing
        for tick in range(self.DEBOUNCE_DELAY + 1):
            await self.send_long_tick()

        # Check output - all buttons should show as pressed
        output = self.get_button_output()
        expected = all_buttons_mask  # Always expect all bits set when all buttons pressed

        if output != expected:
            self.log.error(f"All buttons press: output=0x{output:x}, expected=0x{expected:x}{self.get_time_ns_str()}")
            all_passed = False

        # Test releasing all buttons
        self.button_in.value = release_input

        for tick in range(self.DEBOUNCE_DELAY + 1):
            await self.send_long_tick()

        output = self.get_button_output()
        if output != 0:
            self.log.error(f"All buttons released: output=0x{output:x}, expected=0x0{self.get_time_ns_str()}")
            all_passed = False

        # Test individual button combinations if in full mode
        if self.TEST_LEVEL == 'full':
            test_patterns = []
            for i in range(min(8, 2**self.NUM_BUTTONS)):
                test_patterns.append(i)

            for pattern in test_patterns:
                # Convert pattern to appropriate input based on PRESSED_STATE
                if self.PRESSED_STATE == 1:
                    input_pattern = pattern
                else:
                    input_pattern = pattern ^ all_buttons_mask  # Invert for NC buttons

                self.button_in.value = input_pattern

                for tick in range(self.DEBOUNCE_DELAY + 1):
                    await self.send_long_tick()

                output = self.get_button_output()
                expected = pattern  # Always expect the pattern in output regardless of polarity

                if output != expected:
                    self.log.error(f"Pattern 0x{pattern:x}: output=0x{output:x}, expected=0x{expected:x}{self.get_time_ns_str()}")
                    all_passed = False
                    break

        # Store result
        result = {
            'test_type': 'multiple_buttons',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_pressed_state_polarity(self):
        """Test pressed state polarity"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping pressed state polarity tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing pressed state polarity{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test button 0
        button_mask = 1 if self.NUM_BUTTONS > 0 else 0

        # Test the polarity - what the module considers "pressed"
        # Based on PRESSED_STATE parameter
        if self.PRESSED_STATE == 1:  # Normal Open (NO) - 1 when pressed
            press_input = button_mask    # Input 1 to press
            release_input = 0            # Input 0 to release
        else:  # Normal Closed (NC) - 0 when pressed
            press_input = 0              # Input 0 to press (inverted logic)
            release_input = button_mask  # Input 1 to release (inverted logic)

        # Test press
        self.button_in.value = press_input
        for tick in range(self.DEBOUNCE_DELAY + 1):
            await self.send_long_tick()

        output = self.get_button_output()
        if (output & button_mask) == 0:
            self.log.error(f"Press not detected with PRESSED_STATE={self.PRESSED_STATE}: input=0x{press_input:x}, output=0x{output:x}{self.get_time_ns_str()}")
            all_passed = False

        # Test release
        self.button_in.value = release_input
        for tick in range(self.DEBOUNCE_DELAY + 1):
            await self.send_long_tick()

        output = self.get_button_output()
        if (output & button_mask) != 0:
            self.log.error(f"Release not detected with PRESSED_STATE={self.PRESSED_STATE}: input=0x{release_input:x}, output=0x{output:x}{self.get_time_ns_str()}")
            all_passed = False

        self.log.debug(f"Polarity test passed: PRESSED_STATE={self.PRESSED_STATE}, press_input=0x{press_input:x}, release_input=0x{release_input:x}{self.get_time_ns_str()}")

        # Store result
        result = {
            'test_type': 'pressed_state_polarity',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info(f"Testing reset behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Press some buttons
        button_value = (1 << min(2, self.NUM_BUTTONS)) - 1
        self.button_in.value = button_value

        # Send enough ticks to debounce
        for tick in range(self.DEBOUNCE_DELAY + 1):
            await self.send_long_tick()

        # Verify output is set
        output = self.get_button_output()
        expected = button_value if self.PRESSED_STATE else 0
        if output != expected:
            self.log.warning(f"Pre-reset output unexpected: 0x{output:x}{self.get_time_ns_str()}")

        # Apply reset
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        # Check output is cleared
        output = self.get_button_output()
        if output != 0:
            self.log.error(f"Reset did not clear output: 0x{output:x}{self.get_time_ns_str()}")
            all_passed = False

        # Release reset
        self.rst_n.value = 1
        await RisingEdge(self.clk)

        # Output should still be clear
        output = self.get_button_output()
        if output != 0:
            self.log.error(f"Output not clear after reset release: 0x{output:x}{self.get_time_ns_str()}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'reset_behavior',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running DEBOUNCE tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_debouncing, "Basic debouncing"),
            (self.test_bouncing_signals, "Bouncing signal rejection"),
            (self.test_multiple_buttons, "Multiple buttons"),
            (self.test_pressed_state_polarity, "Pressed state polarity"),
            (self.test_reset_behavior, "Reset behavior")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}{self.get_time_ns_str()}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED{self.get_time_ns_str()}")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED{self.get_time_ns_str()}")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}{self.get_time_ns_str()}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")
        self.log.info(f"TEST RESULTS SUMMARY{self.get_time_ns_str()}")
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}{self.get_time_ns_str()}")
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall DEBOUNCE result: {overall_status}{self.get_time_ns_str()}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}{self.get_time_ns_str()}")
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")

        return all_passed

@cocotb.test(timeout_time=10000, timeout_unit="us")
async def debounce_test(dut):
    """Test for Debounce module"""
    tb = DebounceTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"DEBOUNCE test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Debounce test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.
    """
    num_buttons_list = [1, 2, 4]     # Different button counts
    debounce_delays = [2, 4, 8]      # Different debounce delays
    pressed_states = [0, 1]          # NC and NO buttons
    test_levels = ['full']           # Test levels

    valid_params = []
    for num_buttons, debounce_delay, pressed_state, test_level in product(
        num_buttons_list, debounce_delays, pressed_states, test_levels):
        valid_params.append((num_buttons, debounce_delay, pressed_state, test_level))

    # For debugging, uncomment one of these:
    # return [(4, 4, 1, 'basic')]  # Single test
    # return [(2, 4, 1, 'medium')]  # Just specific configurations

    return valid_params

params = generate_params()

@pytest.mark.parametrize("num_buttons, debounce_delay, pressed_state, test_level", params)
def test_debounce(request, num_buttons, debounce_delay, pressed_state, test_level):
    """
    Parameterized Debounce test with configurable parameters and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "debounce"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/debounce.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    n_str = TBBase.format_dec(num_buttons, 1)
    d_str = TBBase.format_dec(debounce_delay, 1)
    p_str = "no" if pressed_state else "nc"
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_debounce_n{n_str}_d{d_str}_{p_str}_{test_level}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
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
        'N': str(num_buttons),
        'DEBOUNCE_DELAY': str(debounce_delay),
        'PRESSED_STATE': str(pressed_state)
    }

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1))

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
        'TEST_NUM_BUTTONS': str(num_buttons),
        'TEST_DEBOUNCE_DELAY': str(debounce_delay),
        'TEST_PRESSED_STATE': str(pressed_state),
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

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: {num_buttons} buttons, delay={debounce_delay}, {p_str}")
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
        print(f"✓ {test_level.upper()} test PASSED: {num_buttons} buttons, {p_str}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
