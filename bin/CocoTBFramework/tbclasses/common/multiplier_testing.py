"""Multiplier Testing Module

This module provides a robust testbench for various multiplier implementations.
It contains a base class that can be extended for different multiplier architectures.
"""
import os
import random
import contextlib
import itertools
from typing import List, Tuple, Dict, Any, Optional, Union

from cocotb.triggers import Timer
from cocotb.utils import get_sim_time
from CocoTBFramework.tbclasses.tbbase import TBBase

class MultiplierTB(TBBase):
    """Base Testbench for various multiplier implementations

    This class provides common functionality for testing various
    multiplier architectures and configurations.
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '8'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        
        # Initialize the random generator
        random.seed(self.seed)
        
        # Track test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0
        
        # Get DUT type
        self.dut_type = os.environ.get('DUT', 'unknown')
        self.log.info(f"Testing {self.dut_type} with N={self.N}")

    async def main_loop(self, count: int = 256) -> None:
        """Main test loop for multipliers.
        
        Tests various combinations of inputs up to max_val or randomly samples
        if max_val is larger than count.
        
        Args:
            count: Number of test vectors to generate if random sampling
        """
        self.log.info("Starting Main Test")
        
        # Determine if we need to test all possible values or random sampling
        if self.max_val * self.max_val < count:
            self.log.info(f"Testing all {self.max_val} possible values")
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            self.log.info(f"Random sampling with {count} test vectors")
            a_list = [random.randint(0, self.mask) for _ in range(count)]
            b_list = [random.randint(0, self.mask) for _ in range(count)]

        total_tests = len(a_list) * len(b_list)
        self.log.info(f"Will run {min(total_tests, count)} total test cases")
        
        test_idx = 0
        for a, b in itertools.product(a_list, b_list):
            # Stop when we've reached the desired count
            if test_idx >= count:
                break
                
            # Log progress periodically
            if test_idx % max(1, count // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{count} tests completed")
                
            msg = f'Testing {a=} {b=}'
            self.log.debug(msg)
            
            # Apply the inputs to DUT
            try:
                self.dut.i_multiplier.value = a
                self.dut.i_multiplicand.value = b
            except AttributeError as e:
                self.log.warning(f"Error setting inputs: {e}")
                continue
                
            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')
            
            # Read outputs
            try:
                ow_product = int(self.dut.ow_product.value)
            except AttributeError as e:
                self.log.warning(f"Error reading outputs: {e}")
                continue
            
            # Calculate expected values
            expected_product = (a * b) & (2**(2*self.N) - 1)
            
            # Verify results
            if ow_product != expected_product:
                self.log.error(f"Test failed at {test_idx+1}/{count}:")
                self.log.error(f"  Input: multiplier={a}, multiplicand={b}")
                self.log.error(f"  Expected: product={expected_product} (0x{expected_product:X})")
                self.log.error(f"  Actual: product={ow_product} (0x{ow_product:X})")
                
                # For comprehensive analysis, also print binary representation 
                # of both expected and actual results for easier debugging
                self.log.error(f"  Binary comparison:")
                self.log.error(f"    multiplier   = {bin(a)[2:].zfill(self.N)}")
                self.log.error(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
                self.log.error(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
                self.log.error(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")
                
                if a > 0 and b > 0:
                    # Analyze bit by bit for partial products debug
                    self.log.error("  Analyzing partial products:")
                    for i in range(self.N):
                        for j in range(self.N):
                            bit_pos = i + j
                            partial_product = ((a >> i) & 1) & ((b >> j) & 1)
                            expected_bit = (expected_product >> bit_pos) & 1
                            actual_bit = (ow_product >> bit_pos) & 1
                            if expected_bit != actual_bit:
                                self.log.error(f"    Bit position {bit_pos}: Expected {expected_bit}, Got {actual_bit}")
                                self.log.error(f"      Partial product a[{i}] & b[{j}] = {partial_product}")
                
                self.fail_count += 1
                assert False, f"Multiplier test failed: Input: multiplier={a}, multiplicand={b}\nExpected: product={expected_product}\nGot: product={ow_product}"
            else:
                self.pass_count += 1
                
            self.test_count += 1
            test_idx += 1
            
        # Print test summary
        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def corner_cases_test(self) -> None:
        """Test with corner cases specific to multipliers.
        
        Includes cases like zeros, ones, powers of 2, max values, etc.
        """
        self.log.info("Starting Corner Cases Test")
        
        # Define corner cases
        corner_cases = [
            0,                  # Zero
            1,                  # One
            self.mask,          # All ones (max value)
            self.mask // 2,     # 01111...
            self.mask // 2 + 1, # 10000...
            0xA,                # 1010
            0x5,                # 0101
        ]
        
        # Add some powers of 2
        for i in range(1, self.N):
            corner_cases.append(1 << i)  # 2^i
            
        # Add some values with single bit set
        for i in range(self.N):
            corner_cases.append(1 << i)  # Bit at position i set
            
        # Remove duplicates and ensure values fit in N bits
        corner_cases = list(set([case & self.mask for case in corner_cases]))
        
        total_tests = len(corner_cases) * len(corner_cases)
        self.log.info(f"Will run {total_tests} corner case tests")
        
        for a in corner_cases:
            for b in corner_cases:
                # Apply the inputs to DUT
                self.dut.i_multiplier.value = a
                self.dut.i_multiplicand.value = b
                
                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')
                
                # Read outputs
                ow_product = int(self.dut.ow_product.value)
                
                # Calculate expected values
                expected_product = (a * b) & (2**(2*self.N) - 1)
                
                # Verify results
                if ow_product != expected_product:
                    self.log.error(f"Corner case test failed:")
                    self.log.error(f"  Input: multiplier={a} (0x{a:X}), multiplicand={b} (0x{b:X})")
                    self.log.error(f"  Expected: product={expected_product} (0x{expected_product:X})")
                    self.log.error(f"  Actual: product={ow_product} (0x{ow_product:X})")
                    
                    # Print binary representation for easier debugging
                    self.log.error(f"  Binary comparison:")
                    self.log.error(f"    multiplier   = {bin(a)[2:].zfill(self.N)}")
                    self.log.error(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
                    self.log.error(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
                    self.log.error(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")
                    
                    self.fail_count += 1
                    assert False, f"Corner case test failed: Input: multiplier={a}, multiplicand={b}\nExpected: product={expected_product}\nGot: product={ow_product}"
                else:
                    self.pass_count += 1
                    
                self.test_count += 1
        
        # Print test summary
        self.log.info(f"Corner Cases Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def walking_ones_test(self) -> None:
        """Walking ones test pattern.
        
        Tests the multiplier with a sequential pattern where a single bit
        is set to 1 and walks through all bit positions.
        """
        self.log.info("Starting Walking Ones Test")
        
        # Test with walking ones pattern in multiplier
        for pos_a in range(self.N):
            a = 1 << pos_a  # Set only the bit at position 'pos_a' to 1
            
            # Test against walking ones in multiplicand
            for pos_b in range(self.N):
                b = 1 << pos_b  # Set only the bit at position 'pos_b' to 1
                
                # Apply the inputs to DUT
                self.dut.i_multiplier.value = a
                self.dut.i_multiplicand.value = b
                
                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')
                
                # Calculate expected values - for walking ones, should be a single bit set
                expected_product = 1 << (pos_a + pos_b)
                
                # Read outputs
                ow_product = int(self.dut.ow_product.value)
                
                # Verify results
                if ow_product != expected_product:
                    self.log.error(f"Walking ones test failed:")
                    self.log.error(f"  Input: multiplier=0b{bin(a)[2:].zfill(self.N)}, multiplicand=0b{bin(b)[2:].zfill(self.N)}")
                    self.log.error(f"  Expected: product=0b{bin(expected_product)[2:].zfill(2*self.N)}")
                    self.log.error(f"  Actual: product=0b{bin(ow_product)[2:].zfill(2*self.N)}")
                    self.fail_count += 1
                    assert False, f"Walking ones test failed at bit positions multiplier[{pos_a}] * multiplicand[{pos_b}]"
                else:
                    self.pass_count += 1
                
                self.test_count += 1
        
        # Print test summary
        self.log.info(f"Walking Ones Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def alternating_pattern_test(self) -> None:
        """Test with alternating bit patterns (0101... and 1010...).
        
        This tests for issues with adjacent bits affecting each other.
        """
        self.log.info("Starting Alternating Pattern Test")
        
        # Create alternating patterns
        pattern1 = 0  # Will be 0101...
        pattern2 = 0  # Will be 1010...
        
        for i in range(self.N):
            if i % 2 == 0:  # Even bit positions
                pattern1 |= (1 << i)
            else:  # Odd bit positions
                pattern2 |= (1 << i)
        
        # Test combinations of these patterns
        for a, b in itertools.product([pattern1, pattern2], [pattern1, pattern2]):
            # Apply the inputs to DUT
            self.dut.i_multiplier.value = a
            self.dut.i_multiplicand.value = b
            
            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')
            
            # Calculate expected values
            expected_product = (a * b) & (2**(2*self.N) - 1)
            
            # Read outputs
            ow_product = int(self.dut.ow_product.value)
            
            # Verify results
            if ow_product != expected_product:
                self.log.error(f"Alternating pattern test failed:")
                self.log.error(f"  Input: multiplier=0b{bin(a)[2:].zfill(self.N)}, multiplicand=0b{bin(b)[2:].zfill(self.N)}")
                self.log.error(f"  Expected: product=0b{bin(expected_product)[2:].zfill(2*self.N)}")
                self.log.error(f"  Actual: product=0b{bin(ow_product)[2:].zfill(2*self.N)}")
                self.fail_count += 1
                assert False, f"Alternating pattern test failed"
            else:
                self.pass_count += 1
            
            self.test_count += 1
        
        # Print test summary
        self.log.info(f"Alternating Pattern Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def special_patterns_test(self) -> None:
        """Test multiplier with special patterns specific to multiplier architectures.
        
        Includes tests for booth encoding, carry propagation, etc.
        """
        self.log.info("Starting Special Patterns Test")
        
        # Special cases for Booth algorithm
        booth_special = [
            (0x2, 0x2),     # 2*2, simple multiplication
            (0x3, 0x3),     # 3*3, testing +1 -1 sequence
            (0x7, 0x7),     # 7*7, testing multiple +1 patterns
            (0x5, 0x5),     # 5*5, testing +1 0 -1 sequence
            (0xA, 0xA),     # 10*10, testing -1 +1 sequence
            (0x55, 0xAA),   # Alternating 01/10 patterns
            (0x33, 0xCC),   # Alternating 00/11 patterns
        ]
        
        # Limit patterns to N bits
        booth_special = [(a & self.mask, b & self.mask) for a, b in booth_special]
        
        # Test each special case
        for a, b in booth_special:
            # Apply the inputs to DUT
            self.dut.i_multiplier.value = a
            self.dut.i_multiplicand.value = b
            
            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')
            
            # Calculate expected values
            expected_product = (a * b) & (2**(2*self.N) - 1)
            
            # Read outputs
            ow_product = int(self.dut.ow_product.value)
            
            # Verify results
            if ow_product != expected_product:
                self.log.error(f"Special pattern test failed:")
                self.log.error(f"  Input: multiplier=0x{a:X}, multiplicand=0x{b:X}")
                self.log.error(f"  Expected: product=0x{expected_product:X}")
                self.log.error(f"  Actual: product=0x{ow_product:X}")
                self.log.error(f"  Binary comparison:")
                self.log.error(f"    multiplier   = {bin(a)[2:].zfill(self.N)}")
                self.log.error(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
                self.log.error(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
                self.log.error(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")
                self.fail_count += 1
                assert False, f"Special pattern test failed: multiplier=0x{a:X}, multiplicand=0x{b:X}"
            else:
                self.pass_count += 1
            
            self.test_count += 1
        
        # Print test summary
        self.log.info(f"Special Patterns Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def clear_interface(self) -> None:
        """Clear the DUT interface by setting all inputs to 0."""
        self.log.debug('Clearing DUT interface')
        with contextlib.suppress(AttributeError):
            self.dut.i_multiplier.value = 0
            self.dut.i_multiplicand.value = 0

    def print_settings(self) -> None:
        """Print the current testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('Multiplier Testbench Settings:')
        self.log.info(f'    DUT:   {self.dut_type}')
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    Mask:  0x{self.mask:X}')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run a comprehensive suite of tests based on test_level.
        
        This combines multiple test patterns to thoroughly test the multiplier.
        """
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        
        # Clear the interface
        await self.clear_interface()
        
        # Determine test count based on level
        if self.test_level == 'basic':
            count = min(64, 2**self.N)
        elif self.test_level == 'medium':
            count = min(128, 2**self.N)
        else:  # 'full' or anything else
            count = min(256, 2**self.N)
        
        # Always run the main loop for standard tests
        await self.main_loop(count)
        
        # For all levels, include corner cases
        await self.corner_cases_test()
        
        # For medium and full test levels, add walking ones test
        if self.test_level in ['medium', 'full']:
            await self.walking_ones_test()
            
        # For full test level, add alternating pattern and special patterns tests
        if self.test_level == 'full':
            await self.alternating_pattern_test()
            await self.special_patterns_test()
            
        # Print final test summary
        self.log.info(f"Comprehensive Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
