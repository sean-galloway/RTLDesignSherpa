# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RealisticAxiSplitTB
# Purpose: Realistic AXI Split Combinational Logic Test Suite - NO WRAPAROUND
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Realistic AXI Split Combinational Logic Test Suite - NO WRAPAROUND

REALISTIC ASSUMPTIONS:
- No address wraparound ever occurs (transactions never wrap 0xFFFFFFFF -> 0x00000000)
- Focus on comprehensive testing of real-world boundary crossing scenarios
- Robust testing across different data widths and boundary sizes
- Enhanced coverage of legitimate edge cases

COMPREHENSIVE TEST COVERAGE:
1. Boundary crossing with various data widths (32-bit to 512-bit)
2. Multiple boundary sizes (256B to 4KB)
3. Complex multi-boundary crossing scenarios
4. Edge cases near boundaries (but not wraparound)
5. FSM sequence validation for realistic splitting
"""

import os
import random
from itertools import product

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class RealisticAxiSplitTB(TBBase):
    """
    Realistic testbench for AXI Split Combinational Logic - No wraparound cases
    """

    def __init__(self, dut):
        """Initialize the realistic testbench"""
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.TEST_MODE = os.environ.get('TEST_MODE', 'sequence')
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))

        # Validate test mode
        assert self.TEST_MODE in ['basic', 'sequence'], f"Invalid TEST_MODE: {self.TEST_MODE}"

        # Initialize random generator
        random.seed(self.SEED)

        # Clock for assertions
        self.aclk = getattr(self.dut, 'aclk', None)
        self.aresetn = getattr(self.dut, 'aresetn', None)

        # Combinational logic signals
        self.current_addr = self.dut.current_addr
        self.current_len = self.dut.current_len
        self.ax_size = self.dut.ax_size
        self.alignment_mask = self.dut.alignment_mask
        self.is_idle_state = self.dut.is_idle_state
        self.transaction_valid = self.dut.transaction_valid

        # Output signals
        self.split_required = self.dut.split_required
        self.split_len = self.dut.split_len
        self.next_boundary_addr = self.dut.next_boundary_addr
        self.remaining_len_after_split = self.dut.remaining_len_after_split
        self.new_split_needed = self.dut.new_split_needed

        # Test configuration
        self.test_results = []
        self.errors = []
        self.test_count = 0

        # Calculate data width parameters
        self.BYTES_PER_BEAT = self.DW // 8
        self.EXPECTED_AX_SIZE = self.BYTES_PER_BEAT.bit_length() - 1
        self.ADDR_ALIGN_MASK = self.BYTES_PER_BEAT - 1

        # Test masks as specified
        self.TEST_MASKS = [0x0FF, 0x1FF, 0x3FF, 0x7FF, 0xFFF]

        # REALISTIC: Address space limits - avoid wraparound entirely
        self.MAX_ADDR = (1 << self.AW) - 1
        self.SAFE_ADDR_LIMIT = self.MAX_ADDR // 2  # Use lower half of address space
        self.ADDR_MASK = (1 << self.AW) - 1

        # Configuration for comprehensive realistic testing
        self.MAX_POSITIONS_BACK = 32 if self.TEST_LEVEL == 'full' else 16
        self.MAX_BEATS_BEFORE = 32 if self.TEST_LEVEL == 'full' else 16
        self.MAX_BEATS_AFTER = 32 if self.TEST_LEVEL == 'full' else 16

        # Log configuration
        self.log.info("=== REALISTIC AXI SPLIT TEST SUITE - NO WRAPAROUND ===")
        self.log.info(f"TEST_MODE={self.TEST_MODE}")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"AW={self.AW}, DW={self.DW}")
        self.log.info(f"SAFE_ADDR_LIMIT=0x{self.SAFE_ADDR_LIMIT:08X} (no wraparound)")
        self.log.info(f"BYTES_PER_BEAT={self.BYTES_PER_BEAT}, EXPECTED_AX_SIZE={self.EXPECTED_AX_SIZE}")
        self.log.info(f"TEST_MASKS={[hex(m) for m in self.TEST_MASKS]}")
        self.log.info("🚫 WRAPAROUND TESTING DISABLED (realistic assumption)")

    async def setup_clock_and_reset(self):
        """Setup clock and reset"""
        if self.aclk is not None:
            await self.start_clock('aclk', 10, 'ns')
            if self.aresetn is not None:
                self.aresetn.value = 0
                await self.wait_clocks('aclk', 5)
                self.aresetn.value = 1
                await self.wait_clocks('aclk', 2)
                self.log.info("Clock and reset setup complete")

    def align_address_to_data_width(self, addr: int) -> int:
        """Align address to data width boundary"""
        return addr & ~self.ADDR_ALIGN_MASK

    def is_address_safe(self, addr: int, length: int) -> bool:
        """Check if address + transaction length is safe (no wraparound)"""
        aligned_addr = self.align_address_to_data_width(addr)
        total_bytes = (length + 1) * self.BYTES_PER_BEAT
        end_addr = aligned_addr + total_bytes - 1

        # Ensure transaction doesn't wrap around or get too close to limit
        return (end_addr >= aligned_addr and  # No wraparound
                end_addr < self.SAFE_ADDR_LIMIT)  # Stay in safe region

    def generate_safe_random_address(self, max_transaction_bytes: int = 4096) -> int:
        """Generate a random address that's guaranteed safe"""
        # Generate in lower portion of address space with safety margin
        max_safe_start = self.SAFE_ADDR_LIMIT - max_transaction_bytes
        raw_addr = random.randint(0, max_safe_start)
        return self.align_address_to_data_width(raw_addr)

    async def apply_combi_inputs(self, current_addr, current_len, ax_size, alignment_mask,
                                is_idle_state, transaction_valid):
        """Apply inputs to combinational logic and wait for settling"""
        # Align address but don't mask (no wraparound expected)
        aligned_addr = self.align_address_to_data_width(current_addr)

        # Verify this is a safe address (no wraparound)
        if not self.is_address_safe(aligned_addr, current_len):
            self.log.warning(f"Unsafe address detected: 0x{aligned_addr:08X}, len={current_len}")
            return None

        self.current_addr.value = aligned_addr
        self.current_len.value = current_len
        self.ax_size.value = ax_size
        self.alignment_mask.value = alignment_mask
        self.is_idle_state.value = is_idle_state
        self.transaction_valid.value = transaction_valid

        # Wait for combinational logic
        await Timer(1, units='ns')
        if self.aclk is not None:
            await RisingEdge(self.aclk)
            await Timer(1, units='ns')

        return aligned_addr

    def read_combi_outputs(self):
        """Read outputs from combinational logic"""
        return {
            'split_required': bool(self.split_required.value),
            'split_len': int(self.split_len.value),
            'next_boundary_addr': int(self.next_boundary_addr.value),
            'remaining_len_after_split': int(self.remaining_len_after_split.value),
            'new_split_needed': bool(self.new_split_needed.value)
        }

    def calculate_expected_outputs(self, current_addr, current_len, ax_size, alignment_mask,
                                    is_idle_state, transaction_valid):
        """
        SIMPLIFIED reference model - no wraparound handling needed
        """
        # Align address
        current_addr = self.align_address_to_data_width(current_addr)

        # Basic parameters
        boundary_size = alignment_mask + 1
        bytes_per_beat = 1 << ax_size
        total_bytes = (current_len + 1) * bytes_per_beat

        # Calculate transaction end address (no wraparound)
        transaction_end_addr = current_addr + total_bytes - 1

        # Next boundary calculation (no wraparound)
        next_boundary_addr = (current_addr | alignment_mask) + 1

        # SIMPLIFIED: Boundary crossing detection (no wraparound cases)
        crosses_boundary = (transaction_end_addr >= next_boundary_addr)

        # Calculate bytes and beats to boundary (no wraparound)
        bytes_to_boundary = next_boundary_addr - current_addr
        beats_to_boundary = bytes_to_boundary >> ax_size

        # Split decision
        has_beats_before_boundary = beats_to_boundary > 0
        split_required = crosses_boundary and has_beats_before_boundary

        # Split length calculation
        if split_required:
            split_len = beats_to_boundary - 1  # AXI len encoding: beats - 1
        else:
            split_len = current_len

        # Remaining length calculation
        if split_required:
            split_beats = beats_to_boundary
            original_beats = current_len + 1
            remaining_beats = original_beats - split_beats
            remaining_len_after_split = remaining_beats - 1 if remaining_beats > 0 else 0
        else:
            remaining_len_after_split = 0

        # Control signal
        new_split_needed = split_required and is_idle_state and transaction_valid

        return {
            'split_required': split_required,
            'split_len': split_len,
            'next_boundary_addr': next_boundary_addr,
            'remaining_len_after_split': remaining_len_after_split,
            'new_split_needed': new_split_needed,
            # Debug info
            'beats_to_boundary': beats_to_boundary,
            'crosses_boundary': crosses_boundary,
            'total_beats': current_len + 1,
            'transaction_end_addr': transaction_end_addr
        }

    async def test_realistic_edge_cases(self):
        """
        Test realistic edge cases that can actually occur in systems
        """
        self.log.info("🔬 Testing realistic edge case collection")

        edge_cases = [
            # Edge cases for different data widths at various boundaries
            ("DW32 near boundary", "auto", 3, 2, 0x0FF),
            ("DW64 near boundary", "auto", 7, 3, 0x0FF),
            ("DW128 multi-boundary", "auto", 15, 4, 0x0FF),
            ("DW512 large transaction", "auto", 7, 6, 0x0FF),

            # Different boundary sizes
            ("Small boundary crossing", "auto", 3, "auto", 0x07F),
            ("Medium boundary crossing", "auto", 15, "auto", 0x1FF),
            ("Large boundary crossing", "auto", 31, "auto", 0xFFF),

            # Stress cases with multiple boundaries
            ("Multi-boundary DW512", "auto", 31, 6, 0x0FF),
            ("Multi-boundary DW128", "auto", 63, 4, 0x1FF),

            # Edge of safe address space (but not wraparound)
            ("High address region", self.SAFE_ADDR_LIMIT - 0x10000, 15, "auto", 0x0FF),
        ]

        all_passed = True

        for desc, base_addr, length, size, mask in edge_cases:
            # Auto-select appropriate size for current DW
            if size == "auto":
                size = self.EXPECTED_AX_SIZE

            # Skip cases that don't make sense for current DW
            bytes_per_beat = 1 << size
            if bytes_per_beat != self.BYTES_PER_BEAT:
                continue  # Skip mismatched size cases

            # Auto-generate safe address if needed
            if base_addr == "auto":
                boundary_size = mask + 1
                # Position transaction to cross boundaries
                beats_before_boundary = 4
                target_boundary = random.randint(1, 100) * boundary_size
                base_addr = target_boundary - (beats_before_boundary * self.BYTES_PER_BEAT)

            # Ensure address is safe
            aligned_addr = self.align_address_to_data_width(base_addr)
            if not self.is_address_safe(aligned_addr, length):
                self.log.debug(f"Skipping unsafe case: {desc}")
                continue

            self.log.info(f"\n🔍 REALISTIC EDGE CASE: {desc}")
            self.log.info(f"  Addr: 0x{aligned_addr:08X}, Len: {length}, Size: {size}, Mask: 0x{mask:03X}")

            test_desc = f"REALISTIC EDGE: {desc}"
            passed = await self.test_case(test_desc, aligned_addr, length, size, mask)

            if not passed:
                all_passed = False
                self.log.error(f"💥 REALISTIC EDGE CASE FAILED: {desc}")

        return all_passed

    async def test_case(self, test_desc, addr, length, ax_size, mask):
        """Test a single case"""
        self.test_count += 1

        if self.TEST_MODE == 'sequence':
            return await self.test_fsm_sequence_case(test_desc, addr, length, ax_size, mask)
        else:
            return await self.test_basic_case(test_desc, addr, length, ax_size, mask)

    async def test_basic_case(self, test_desc, addr, length, ax_size, mask):
        """Test individual combinational logic case"""
        actual_addr = await self.apply_combi_inputs(
            addr, length, ax_size, mask, True, True
        )

        if actual_addr is None:
            self.log.warning(f"Skipped unsafe test case: {test_desc}")
            return True  # Skip unsafe cases

        actual = self.read_combi_outputs()
        expected = self.calculate_expected_outputs(
            addr, length, ax_size, mask, True, True
        )

        inputs = (addr, length, ax_size, mask, True, True)
        return self.verify_and_log_result(test_desc, inputs, expected, actual_addr, actual)

    def verify_and_log_result(self, test_desc, inputs, expected, actual_addr, actual):
        """Verify outputs and log results"""
        addr, length, size, mask, idle, valid = inputs

        errors = []

        # Check each output
        for signal in ['split_required', 'split_len', 'next_boundary_addr', 'remaining_len_after_split', 'new_split_needed']:
            exp_val = expected[signal]
            act_val = actual[signal]
            if exp_val != act_val:
                errors.append(f"{signal}: expected {exp_val}, got {act_val}")

        # Additional validation for splits
        if actual['split_required']:
            if actual['split_len'] >= length:
                errors.append(f"split_len ({actual['split_len']}) should be < original length ({length})")

            # Check length conservation
            split_beats = actual['split_len'] + 1
            remaining_beats = actual['remaining_len_after_split'] + 1 if actual['remaining_len_after_split'] >= 0 else 0
            original_beats = length + 1

            if split_beats + remaining_beats != original_beats:
                errors.append(f"Length conservation: split_beats({split_beats}) + remaining_beats({remaining_beats}) != original_beats({original_beats})")

        # Log result with focus on realistic scenarios
        passed = len(errors) == 0
        time_str = self.get_time_ns_str()

        # Log significant cases and all failures
        should_log = (not passed or
                        "REALISTIC EDGE" in test_desc or
                        "Multi-boundary" in test_desc or
                        self.test_count % 25 == 0 or
                        self.TEST_LEVEL == 'basic')

        if should_log:
            self.log.info("─" * 80)
            self.log.info(f"Test #{self.test_count}: {test_desc}{time_str}")
            self.log.info("─" * 80)

            # Enhanced input display
            boundary_size = mask + 1
            bytes_per_beat = 1 << size
            total_bytes = (length + 1) * bytes_per_beat

            self.log.info("📥 INPUTS:")
            self.log.info(f"   Address: 0x{actual_addr:08X}, Length: {length} ({length + 1} beats)")
            self.log.info(f"   Boundary: 0x{mask:03X} ({boundary_size} bytes), Total bytes: {total_bytes}")

            # Enhanced boundary analysis
            if expected.get('transaction_end_addr') is not None:
                end_addr = expected['transaction_end_addr']
                self.log.info(f"   Transaction end: 0x{end_addr:08X}")
                self.log.info(f"   Next boundary: 0x{expected['next_boundary_addr']:08X}")
                self.log.info(f"   Crosses boundary: {expected['crosses_boundary']}")

            # Format expected vs actual
            self.log.info("📤 EXPECTED vs ACTUAL:")
            for signal in ['split_required', 'split_len', 'remaining_len_after_split', 'new_split_needed']:
                exp_val = expected[signal]
                act_val = actual[signal]
                status = "✅" if exp_val == act_val else "❌"
                self.log.info(f"   {signal:25} | {str(exp_val):>8} | {str(act_val):>8} | {status}")

            # Special formatting for addresses
            exp_addr = expected['next_boundary_addr']
            act_addr = actual['next_boundary_addr']
            addr_status = "✅" if exp_addr == act_addr else "❌"
            self.log.info(f"   {'next_boundary_addr':25} | 0x{exp_addr:06X} | 0x{act_addr:06X} | {addr_status}")

            if not passed:
                self.log.error("❌ ERRORS FOUND:")
                for i, error in enumerate(errors, 1):
                    self.log.error(f"   {i}. {error}")
                self.errors.extend([f"Test {self.test_count}{time_str}: {err}" for err in errors])
            else:
                self.log.info("✅ PASSED")

            self.log.info("")

        return passed

    async def test_no_split_cases(self, mask, boundary_base_addr):
        """Test no-split cases in realistic scenarios"""
        self.log.info(f"Testing no-split cases for mask 0x{mask:03X}")

        boundary_size = mask + 1
        all_passed = True

        for beats_back in range(1, min(self.MAX_POSITIONS_BACK + 1, boundary_size // self.BYTES_PER_BEAT)):
            # Calculate address that's safely within boundary
            next_boundary = boundary_base_addr + boundary_size
            addr = next_boundary - (beats_back * self.BYTES_PER_BEAT)
            addr = self.align_address_to_data_width(addr)

            # Ensure it's safe
            if not self.is_address_safe(addr, 0):
                continue

            # Test 1-beat transaction
            length = 0
            test_desc = f"No split: {beats_back} beats before boundary, 1-beat transaction"

            passed = await self.test_case(test_desc, addr, length, self.EXPECTED_AX_SIZE, mask)
            if not passed:
                all_passed = False

        return all_passed

    async def test_split_combinations(self, mask, boundary_base_addr):
        """Test split combinations in realistic scenarios"""
        self.log.info(f"Testing split combinations for mask 0x{mask:03X}")

        boundary_size = mask + 1
        all_passed = True

        beats_before_list = [1, 2, 4, 8] if self.TEST_LEVEL != 'full' else [1, 2, 3, 4, 5, 8, 12, 16]
        beats_after_list = [1, 2, 4, 8] if self.TEST_LEVEL != 'full' else [1, 2, 3, 4, 5, 8, 12, 16]

        next_boundary = boundary_base_addr + boundary_size

        for beats_before in beats_before_list:
            if beats_before * self.BYTES_PER_BEAT >= boundary_size:
                continue

            for beats_after in beats_after_list:
                # Calculate address
                addr = next_boundary - (beats_before * self.BYTES_PER_BEAT)
                addr = self.align_address_to_data_width(addr)

                # Calculate total length
                total_beats = beats_before + beats_after
                length = total_beats - 1

                if length > 64:  # Keep reasonable
                    continue

                # Ensure it's safe
                if not self.is_address_safe(addr, length):
                    continue

                test_desc = f"Split: {beats_before} before + {beats_after} after boundary"

                passed = await self.test_case(test_desc, addr, length, self.EXPECTED_AX_SIZE, mask)
                if not passed:
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        return all_passed

        return all_passed

    async def test_multiple_splits(self, mask, boundary_base_addr):
        """Test multiple splits for larger data widths - realistic scenarios only"""
        boundary_size = mask + 1

        if self.DW < 64:
            self.log.info(f"Skipping multiple splits test for DW={self.DW}")
            return True

        self.log.info(f"Testing multiple splits for DW={self.DW}, mask=0x{mask:03X}")

        # Calculate realistic scenarios that create multiple splits
        test_cases = []

        if self.DW >= 512 and boundary_size <= 1024:  # 512DW with small boundaries
            boundaries_to_cross = 3  # Reduced from 4 for safety
            total_bytes_needed = boundaries_to_cross * boundary_size + (4 * self.BYTES_PER_BEAT)
            total_beats_needed = total_bytes_needed // self.BYTES_PER_BEAT

            if total_beats_needed <= 64:  # Keep reasonable
                test_cases.extend([
                    (1, total_beats_needed - 1, f"512DW: cross {boundaries_to_cross} boundaries"),
                    (2, total_beats_needed - 1, f"512DW: 2 beats before, cross {boundaries_to_cross} boundaries"),
                ])

        elif self.DW >= 128:  # For 128DW and above
            boundaries_to_cross = 2
            total_bytes_needed = boundaries_to_cross * boundary_size + (8 * self.BYTES_PER_BEAT)
            total_beats_needed = total_bytes_needed // self.BYTES_PER_BEAT

            if total_beats_needed <= 64:
                test_cases.extend([
                    (1, total_beats_needed - 1, f"{self.DW}DW: cross {boundaries_to_cross} boundaries"),
                    (4, total_beats_needed - 1, f"{self.DW}DW: 4 beats before, cross {boundaries_to_cross} boundaries"),
                ])

        if not test_cases:
            self.log.info(f"No suitable multiple split cases for DW={self.DW}, mask=0x{mask:03X}")
            return True

        all_passed = True

        for beats_before, length, description in test_cases:
            if beats_before * self.BYTES_PER_BEAT >= boundary_size:
                continue

            addr = boundary_base_addr + boundary_size - (beats_before * self.BYTES_PER_BEAT)
            addr = self.align_address_to_data_width(addr)

            # Ensure it's safe
            if not self.is_address_safe(addr, length):
                self.log.debug(f"Skipping unsafe multiple split case: {description}")
                continue

            test_desc = f"Multiple splits: {description}"

            passed = await self.test_case(test_desc, addr, length, self.EXPECTED_AX_SIZE, mask)
            if not passed:
                all_passed = False

        return all_passed

    # Include complete FSM sequence testing (same as before but with safety checks)
    async def execute_fsm_splitting_sequence(self, original_addr, original_len, ax_size, alignment_mask):
        """Execute FSM sequence with safety checks"""
        # Ensure starting address is safe
        if not self.is_address_safe(original_addr, original_len):
            self.log.warning(f"Skipping unsafe FSM sequence: addr=0x{original_addr:08X}, len={original_len}")
            return None

        sequence_log = []
        split_transactions = []

        current_addr = original_addr
        current_len = original_len
        is_idle_state = True
        transaction_valid = True
        step = 0

        self.log.debug(f"Starting FSM sequence for addr=0x{original_addr:08X}, len={original_len}")

        while step < 20:  # Safety limit
            step += 1

            # Apply inputs with safety check
            actual_addr = await self.apply_combi_inputs(
                current_addr, current_len, ax_size, alignment_mask,
                is_idle_state, transaction_valid
            )

            if actual_addr is None:
                self.log.warning(f"FSM sequence hit unsafe address at step {step}")
                break

            outputs = self.read_combi_outputs()

            # Log this step
            state_name = "IDLE" if is_idle_state else "SPLITTING"
            step_info = {
                'step': step,
                'state': state_name,
                'inputs': {'addr': actual_addr, 'len': current_len, 'is_idle': is_idle_state},
                'outputs': outputs.copy()
            }
            sequence_log.append(step_info)

            # Record split transaction
            actual_len = outputs['split_len'] if outputs['split_required'] else current_len
            split_transactions.append({
                'step': step,
                'addr': actual_addr,
                'len': actual_len,
                'beats': actual_len + 1
            })

            # FSM state transition logic
            if is_idle_state:
                if outputs['new_split_needed']:
                    is_idle_state = False
                    current_addr = outputs['next_boundary_addr']
                    current_len = outputs['remaining_len_after_split']
                else:
                    break
            else:
                if outputs['split_required']:
                    current_addr = outputs['next_boundary_addr']
                    current_len = outputs['remaining_len_after_split']
                else:
                    break

        return {
            'sequence_log': sequence_log,
            'split_transactions': split_transactions,
            'total_steps': step
        }

    async def test_fsm_sequence_case(self, test_desc, original_addr, original_len, ax_size, alignment_mask):
        """Test FSM sequence case with safety checks"""
        sequence_result = await self.execute_fsm_splitting_sequence(
            original_addr, original_len, ax_size, alignment_mask
        )

        if sequence_result is None:
            return True  # Skip unsafe cases

        # Use simplified reference model for expected results
        expected_splits = self.calculate_expected_split_sequence(
            original_addr, original_len, ax_size, alignment_mask
        )

        # Verify results (same validation logic as before)
        errors = []

        actual_split_count = len(sequence_result['split_transactions'])
        expected_split_count = len(expected_splits['transactions'])

        if actual_split_count != expected_split_count:
            errors.append(f"Split count mismatch: expected {expected_split_count}, got {actual_split_count}")

        # Check each split transaction
        for i, (actual_txn, expected_txn) in enumerate(zip(sequence_result['split_transactions'], expected_splits['transactions'])):
            if actual_txn['addr'] != expected_txn['addr']:
                errors.append(f"Txn {i+1} addr mismatch: expected 0x{expected_txn['addr']:08X}, got 0x{actual_txn['addr']:08X}")
            if actual_txn['len'] != expected_txn['len']:
                errors.append(f"Txn {i+1} len mismatch: expected {expected_txn['len']}, got {actual_txn['len']}")

        # Check total beat conservation
        actual_total_beats = sum(txn['beats'] for txn in sequence_result['split_transactions'])
        expected_total_beats = original_len + 1

        if actual_total_beats != expected_total_beats:
            errors.append(f"Beat conservation: expected {expected_total_beats} total beats, got {actual_total_beats}")

        passed = len(errors) == 0

        if not passed:
            self.errors.extend([f"Test {self.test_count}: {err}" for err in errors])

        return passed

    def calculate_expected_split_sequence(self, addr, length, size, mask):
        """Calculate expected split sequence - simplified for no wraparound"""
        transactions = []
        current_addr = self.align_address_to_data_width(addr)
        remaining_len = length

        while remaining_len >= 0:
            boundary_size = mask + 1
            next_boundary = (current_addr | mask) + 1

            # No wraparound calculations needed
            bytes_to_boundary = next_boundary - current_addr
            beats_to_boundary = bytes_to_boundary >> size

            # Calculate if this crosses boundary
            bytes_per_beat = 1 << size
            transaction_bytes = (remaining_len + 1) * bytes_per_beat
            transaction_end = current_addr + transaction_bytes - 1

            crosses_boundary = (transaction_end >= next_boundary)

            if crosses_boundary and beats_to_boundary > 0:
                # Split required
                split_len = beats_to_boundary - 1
                transactions.append({
                    'addr': current_addr,
                    'len': split_len,
                    'beats': beats_to_boundary
                })

                remaining_beats = (remaining_len + 1) - beats_to_boundary
                remaining_len = remaining_beats - 1 if remaining_beats > 0 else -1
                current_addr = next_boundary
            else:
                # Final transaction
                transactions.append({
                    'addr': current_addr,
                    'len': remaining_len,
                    'beats': remaining_len + 1
                })
                break

        return {'transactions': transactions, 'total_splits': len(transactions)}

    async def test_mask_systematic(self, mask):
        """Test one mask systematically - realistic scenarios only"""
        self.log.info("="*60)
        self.log.info(f"SYSTEMATIC TEST FOR MASK 0x{mask:03X} - REALISTIC SCENARIOS{self.get_time_ns_str()}")
        self.log.info("="*60)

        boundary_size = mask + 1
        all_passed = True

        # Use safe boundary bases within our safe address region
        test_boundaries = [
            0x00010000,
            0x00100000,
            0x01000000,
            self.SAFE_ADDR_LIMIT // 4,  # Ensure plenty of room
        ]

        for i, boundary_base in enumerate(test_boundaries):
            if boundary_base + (boundary_size * 10) >= self.SAFE_ADDR_LIMIT:
                continue  # Skip if not enough room

            self.log.info(f"Testing at safe boundary base 0x{boundary_base:08X}")

            # 1. No split cases
            no_split_passed = await self.test_no_split_cases(mask, boundary_base)
            if not no_split_passed:
                all_passed = False

            # 2. Split combinations
            split_passed = await self.test_split_combinations(mask, boundary_base)
            if not split_passed:
                all_passed = False

            # 3. Multiple splits
            if self.DW >= 64:
                multi_split_passed = await self.test_multiple_splits(mask, boundary_base)
                if not multi_split_passed:
                    all_passed = False

            if self.TEST_LEVEL == 'basic' and not all_passed:
                break

        return all_passed

    async def run_realistic_test_suite(self):
        """Run the realistic test suite"""
        mode_desc = "FSM SEQUENCE" if self.TEST_MODE == 'sequence' else "BASIC"
        self.log.info(f"STARTING REALISTIC AXI SPLIT TEST SUITE - {mode_desc} MODE")
        self.log.info(f"Configuration: DW={self.DW}, AW={self.AW}, Level={self.TEST_LEVEL}")

        # Setup
        await self.setup_clock_and_reset()

        overall_passed = True

        # Phase 1: Realistic edge cases
        self.log.info("🔥 PHASE 1: Realistic Edge Cases")
        edge_cases_passed = await self.test_realistic_edge_cases()
        if not edge_cases_passed:
            overall_passed = False
            if self.TEST_LEVEL == 'basic':
                self.print_final_summary()
                return overall_passed

        # Phase 2: Systematic mask testing
        self.log.info("🔍 PHASE 2: Systematic Mask Testing")
        for i, mask in enumerate(self.TEST_MASKS):
            self.log.info(f"\n🎯 Starting {mode_desc} tests for mask 0x{mask:03X} ({i+1}/{len(self.TEST_MASKS)})")

            mask_passed = await self.test_mask_systematic(mask)
            if not mask_passed:
                self.log.error(f"❌ MASK 0x{mask:03X} tests failed")
                overall_passed = False
                if self.TEST_LEVEL == 'basic':
                    break
            else:
                self.log.info(f"✅ MASK 0x{mask:03X} tests passed")

        # Print summary
        self.print_final_summary()
        return overall_passed

    def print_final_summary(self):
        """Print final test summary"""
        total_tests = self.test_count
        total_errors = len(self.errors)

        self.log.info("="*80)
        self.log.info(f"REALISTIC AXI SPLIT TEST RESULTS - NO WRAPAROUND")
        self.log.info("="*80)
        self.log.info(f"Configuration: DW={self.DW}, AW={self.AW}, Level={self.TEST_LEVEL}")
        self.log.info(f"Safe Address Limit: 0x{self.SAFE_ADDR_LIMIT:08X}")
        self.log.info(f"Total Tests: {total_tests}")
        self.log.info(f"Total Errors: {total_errors}")

        if total_errors == 0:
            self.log.info("🎉 ALL REALISTIC TESTS PASSED! 🎉")
            self.log.info("✅ RTL correctly handles realistic boundary crossing scenarios")
        else:
            self.log.error(f"❌ {total_errors} ERRORS FOUND in realistic scenarios")
            for i, error in enumerate(self.errors[:5], 1):
                self.log.error(f"  {i}: {error}")
            if len(self.errors) > 5:
                self.log.error(f"  ... and {len(self.errors) - 5} more errors")


@cocotb.test(timeout_time=120000, timeout_unit="us")
async def realistic_axi_split_test(dut):
    """Run the realistic test suite"""
    tb = RealisticAxiSplitTB(dut)
    passed = await tb.run_realistic_test_suite()
    assert passed, f"Realistic test failed with {len(tb.errors)} errors"


def generate_realistic_test_params():
    """Generate test parameters for realistic testing"""
    aw = [32]  # Focus on 32-bit for realistic scenarios
    dw = [32, 64, 128, 512]  # Full data width range
    test_levels = ['basic', 'full']
    test_modes = ['basic', 'sequence']

    return [
        {
            'AW': combo[0],
            'DW': combo[1],
            'test_level': combo[2],
            'test_mode': combo[3]
        }
        for combo in product(aw, dw, test_levels, test_modes)
    ]


@pytest.mark.parametrize("params", generate_realistic_test_params())
def test_axi_split_realistic(request, params):
    """Run realistic test with pytest"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared': 'rtl/amba/shared'
    })

    dut_name = "axi_split_combi"
    toplevel = dut_name
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_shared'], "axi_split_combi.sv")
    ]

    # Create test identifier following pattern: test_<module>_<params>
    t_aw = params['AW']
    t_dw = params['DW']
    t_level = params['test_level']
    t_mode = params['test_mode']
    # Format: test_axi_split_combi_aw032_dw064_basic_realistic
    aw_str = f"{t_aw:03d}"
    dw_str = f"{t_dw:03d}"
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_{t_level}_{t_mode}"

    # Setup paths
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'AW': str(params['AW']),
        'DW': str(params['DW'])
    }

    # Environment
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': params['test_level'],
        'TEST_MODE': params['test_mode'],
        'TEST_AW': str(params['AW']),
        'TEST_DW': str(params['DW']),
    }

    # Realistic timeout
    timeout_multiplier = 8.0 if params['test_level'] == 'full' else 4.0
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_multiplier)

    # Compilation arguments
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace", "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-WIDTHEXPAND"
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create view command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        print(f"Realistic test failed: {str(e)}")
        print(f"Logs at: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Run realistic test with pytest"""

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared': 'rtl/amba/shared'
    })

    dut_name = "axi_split_combi"
    toplevel = dut_name
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_shared'], "axi_split_combi.sv")
    ]

    # Create test identifier following pattern: test_<module>_<params>
    t_aw = params['AW']
    t_dw = params['DW']
    t_level = params['test_level']
    t_mode = params['test_mode']
    # Format: test_axi_split_combi_aw032_dw064_basic_realistic
    aw_str = f"{t_aw:03d}"
    dw_str = f"{t_dw:03d}"
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_{t_level}_{t_mode}"

    # Setup paths
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'AW': str(params['AW']),
        'DW': str(params['DW'])
    }

    # Environment
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': params['test_level'],
        'TEST_MODE': params['test_mode'],
        'TEST_AW': str(params['AW']),
        'TEST_DW': str(params['DW']),
    }

    # Realistic timeout
    timeout_multiplier = 8.0 if params['test_level'] == 'full' else 4.0
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_multiplier)

    # Compilation arguments
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace", "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-WIDTHEXPAND"
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create view command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        print(f"Realistic test failed: {str(e)}")
        print(f"Logs at: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise
