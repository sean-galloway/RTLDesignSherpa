# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterPriorityEncoderTB
# Purpose: Testbench for arbiter_priority_encoder module
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Testbench for arbiter_priority_encoder module

The arbiter_priority_encoder implements optimized priority encoding for arbitration.
It provides specialized unrolled implementations for common power-of-2 client counts
(4, 8, 16, 32) and a generic loop-based version for other sizes.

Key Features Tested:
- Priority ordering (client 0 = highest priority)
- Masked vs unmasked request handling
- All client count variants (4, 8, 16, 32, and generic sizes like 5, 12)
- No-request handling (winner_valid = 0)
- All-request scenarios
- Single-request scenarios

Author: RTL Design Sherpa Project
"""

import cocotb
from cocotb.triggers import Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
import os


class ArbiterPriorityEncoderTB(TBBase):
    """Testbench for arbiter_priority_encoder module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get parameters from environment
        self.CLIENTS = self.convert_to_int(os.environ.get('PARAM_CLIENTS', '4'))

        self.log.info(f"ArbiterPriorityEncoderTB initialized: CLIENTS={self.CLIENTS}")

    async def setup_clocks_and_reset(self):
        """Setup - no clock needed for combinational logic"""
        # Priority encoder is purely combinational, no clock/reset
        await Timer(1, units='ns')  # Small delay for initialization

    async def assert_reset(self):
        """No reset for combinational logic"""
        pass

    async def deassert_reset(self):
        """No reset for combinational logic"""
        pass

    def set_inputs(self, requests_masked, requests_unmasked, any_masked):
        """Set input signals"""
        self.dut.requests_masked.value = requests_masked
        self.dut.requests_unmasked.value = requests_unmasked
        self.dut.any_masked_requests.value = any_masked

    async def get_outputs(self):
        """Get output signals after combinational delay"""
        await Timer(1, units='ns')  # Combinational propagation delay
        winner = int(self.dut.winner.value)
        winner_valid = int(self.dut.winner_valid.value)
        return winner, winner_valid

    async def test_priority_order(self):
        """Test that lower index clients have higher priority"""
        self.log.info("=== Test: Priority Order ===")

        # Test with multiple requesters - lowest index should win
        test_cases = [
            # (requests_unmasked, expected_winner, description)
            (0b0001, 0, "Single request - client 0"),
            (0b0010, 1, "Single request - client 1"),
            (0b0011, 0, "Clients 0,1 - client 0 wins (higher priority)"),
            (0b1111, 0, "All clients - client 0 wins"),
            (0b1110, 1, "Clients 1,2,3 - client 1 wins"),
            (0b1100, 2, "Clients 2,3 - client 2 wins"),
            (0b1000, 3, "Client 3 only"),
        ]

        # Extend test cases for larger client counts
        if self.CLIENTS >= 8:
            test_cases.extend([
                (0b10000000, 7, "Client 7 only"),
                (0b11111111, 0, "All 8 clients - client 0 wins"),
                (0b11110000, 4, "Clients 4-7 - client 4 wins"),
            ])

        if self.CLIENTS >= 16:
            test_cases.extend([
                (0b1000000000000000, 15, "Client 15 only"),
                (0b1111111111111111, 0, "All 16 clients - client 0 wins"),
            ])

        all_passed = True
        for requests, expected_winner, desc in test_cases:
            if requests >= (1 << self.CLIENTS):
                continue  # Skip if exceeds client count

            # Use unmasked requests (any_masked = 0)
            self.set_inputs(0, requests, 0)
            winner, winner_valid = await self.get_outputs()

            if winner_valid != 1:
                self.log.error(f"  FAIL: {desc} - winner_valid should be 1, got {winner_valid}")
                all_passed = False
            elif winner != expected_winner:
                self.log.error(f"  FAIL: {desc} - expected winner {expected_winner}, got {winner}")
                all_passed = False
            else:
                self.log.debug(f"  PASS: {desc}")

        if all_passed:
            self.log.info("✓ Priority order test passed")

        return all_passed

    async def test_masked_vs_unmasked(self):
        """Test masked requests have priority over unmasked"""
        self.log.info("=== Test: Masked vs Unmasked Priority ===")

        all_passed = True

        # When any_masked=1, use masked requests
        self.set_inputs(requests_masked=0b0010, requests_unmasked=0b0001, any_masked=1)
        winner, winner_valid = await self.get_outputs()

        if winner != 1:
            self.log.error(f"  FAIL: Masked requests - expected winner 1, got {winner}")
            all_passed = False
        elif winner_valid != 1:
            self.log.error(f"  FAIL: Masked requests - winner_valid should be 1")
            all_passed = False
        else:
            self.log.debug(f"  PASS: Masked requests used (winner=1)")

        # When any_masked=0, use unmasked requests
        self.set_inputs(requests_masked=0b0010, requests_unmasked=0b0001, any_masked=0)
        winner, winner_valid = await self.get_outputs()

        if winner != 0:
            self.log.error(f"  FAIL: Unmasked requests - expected winner 0, got {winner}")
            all_passed = False
        elif winner_valid != 1:
            self.log.error(f"  FAIL: Unmasked requests - winner_valid should be 1")
            all_passed = False
        else:
            self.log.debug(f"  PASS: Unmasked requests used (winner=0)")

        if all_passed:
            self.log.info("✓ Masked vs unmasked test passed")

        return all_passed

    async def test_no_requests(self):
        """Test behavior when no requests"""
        self.log.info("=== Test: No Requests ===")

        # No requests on either masked or unmasked
        self.set_inputs(0, 0, 0)
        winner, winner_valid = await self.get_outputs()

        if winner_valid != 0:
            self.log.error(f"  FAIL: No requests - winner_valid should be 0, got {winner_valid}")
            return False

        self.log.debug(f"  PASS: No requests - winner_valid = 0")
        self.log.info("✓ No requests test passed")
        return True

    async def test_all_clients(self):
        """Test all individual clients"""
        self.log.info("=== Test: All Individual Clients ===")

        all_passed = True
        for client in range(self.CLIENTS):
            requests = 1 << client
            self.set_inputs(0, requests, 0)
            winner, winner_valid = await self.get_outputs()

            if winner != client:
                self.log.error(f"  FAIL: Client {client} - expected winner {client}, got {winner}")
                all_passed = False
            elif winner_valid != 1:
                self.log.error(f"  FAIL: Client {client} - winner_valid should be 1")
                all_passed = False
            else:
                self.log.debug(f"  PASS: Client {client} → winner {winner}")

        if all_passed:
            self.log.info(f"✓ All {self.CLIENTS} clients test passed")

        return all_passed

    async def test_all_combinations(self):
        """Test all possible request combinations (feasible for small client counts)"""
        if self.CLIENTS > 8:
            self.log.info("=== Test: All Combinations (skipped for CLIENTS > 8) ===")
            return True

        self.log.info(f"=== Test: All {2**self.CLIENTS} Request Combinations ===")

        all_passed = True
        for requests in range(1 << self.CLIENTS):
            self.set_inputs(0, requests, 0)
            winner, winner_valid = await self.get_outputs()

            if requests == 0:
                # No requests - should be invalid
                if winner_valid != 0:
                    self.log.error(f"  FAIL: requests=0x{requests:X} - winner_valid should be 0")
                    all_passed = False
            else:
                # Find expected winner (lowest set bit)
                expected_winner = None
                for i in range(self.CLIENTS):
                    if requests & (1 << i):
                        expected_winner = i
                        break

                if winner != expected_winner:
                    self.log.error(f"  FAIL: requests=0x{requests:X} - expected {expected_winner}, got {winner}")
                    all_passed = False
                elif winner_valid != 1:
                    self.log.error(f"  FAIL: requests=0x{requests:X} - winner_valid should be 1")
                    all_passed = False

        if all_passed:
            self.log.info(f"✓ All {2**self.CLIENTS} combinations passed")

        return all_passed

    async def run_all_tests(self):
        """Run all test scenarios"""
        results = []

        # Test 1: Priority order
        passed = await self.test_priority_order()
        results.append(("Priority Order", passed))

        # Test 2: Masked vs unmasked
        passed = await self.test_masked_vs_unmasked()
        results.append(("Masked vs Unmasked", passed))

        # Test 3: No requests
        passed = await self.test_no_requests()
        results.append(("No Requests", passed))

        # Test 4: All individual clients
        passed = await self.test_all_clients()
        results.append(("All Individual Clients", passed))

        # Test 5: All combinations (for small client counts)
        passed = await self.test_all_combinations()
        results.append(("All Combinations", passed))

        # Summary
        self.log.info("=" * 60)
        self.log.info("Test Summary:")
        for name, passed in results:
            status = "✓ PASSED" if passed else "✗ FAILED"
            self.log.info(f"  {name}: {status}")
        self.log.info("=" * 60)

        return all(result[1] for result in results)
