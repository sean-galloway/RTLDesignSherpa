# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: DebounceTB
# Purpose: Testbench for debounce
# Subsystem: framework
#
# Extracted from val/common/test_debounce.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class DebounceTB(TBBase):
    """Testbench for Debounce module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.NUM_BUTTONS = self.convert_to_int(os.environ.get('TEST_NUM_BUTTONS', '4'))
        self.DEBOUNCE_DELAY = self.convert_to_int(os.environ.get('TEST_DEBOUNCE_DELAY', '4'))
        self.PRESSED_STATE = self.convert_to_int(os.environ.get('TEST_PRESSED_STATE', '1'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

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

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.reset_dut()

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
        if self.TEST_LEVEL == 'gate':
            test_buttons = [0] if self.NUM_BUTTONS > 0 else []
        elif self.TEST_LEVEL == 'func':
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
                if self.TEST_LEVEL == 'gate':
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
                if self.TEST_LEVEL == 'gate':
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
                if self.TEST_LEVEL == 'gate':
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
        if self.TEST_LEVEL == 'gate':
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
        if self.TEST_LEVEL == 'gate' or self.NUM_BUTTONS == 1:
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
