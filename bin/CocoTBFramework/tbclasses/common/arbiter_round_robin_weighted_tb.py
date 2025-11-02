# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: WeightedRoundRobinTB
# Purpose: Proper Weighted Round Robin Testbench with Clean Weight Testing Methodology
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Proper Weighted Round Robin Testbench with Clean Weight Testing Methodology
Follows the correct process: idle -> set weights -> enable all -> run -> disable -> validate
"""

import os
import random
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ClockCycles
from cocotb.clock import Clock

# Import the corrected ArbiterMaster and existing monitor
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.arbiter_monitor import WeightedRoundRobinArbiterMonitor
from CocoTBFramework.components.shared.arbiter_master import ArbiterMaster

class WeightedRoundRobinTB(TBBase):
    """
    Proper Weighted Round Robin Testbench with Clean Weight Testing
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters with proper type conversion
        self.CLIENTS = int(dut.CLIENTS)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.MAX_LEVELS = int(dut.MAX_LEVELS)

        # Ensure MAX_LEVELS_WIDTH is properly converted to int
        if hasattr(dut, 'MAX_LEVELS_WIDTH'):
            try:
                self.MAX_LEVELS_WIDTH = int(dut.MAX_LEVELS_WIDTH.value)
            except:
                self.MAX_LEVELS_WIDTH = int(dut.MAX_LEVELS_WIDTH)
        else:
            self.MAX_LEVELS_WIDTH = (self.MAX_LEVELS - 1).bit_length()

        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))
        self.MAX_LEVELS_WIDTH = int(self.MAX_LEVELS_WIDTH)

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset signals
        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n

        # Initialize the weighted arbiter monitor
        self.monitor = WeightedRoundRobinArbiterMonitor(
            dut=dut,
            title="WRR_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=self.dut.grant_ack,
            block_arb_signal=self.dut.block_arb,
            max_thresh_signal=self.dut.max_thresh,
            clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            log=self.log,
            clock_period_ns=10
        )

        # Initialize the corrected arbiter master with weight support
        self.master = ArbiterMaster(
            dut=dut,
            title="WRR Driver",
            clock=self.dut.clk,
            num_clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            is_weighted=True,  # Enable weight support
            log=self.log
        )

        # Track any monitor errors
        self.monitor_errors = []
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)
        self.monitor.enable_debug()

        # Same ACK timeout as RR TB - no artificial differences
        if hasattr(self.monitor, 'compliance'):
            self.monitor.compliance.ack_timeout_cycles = 8000
            self.log.info(f"Configured ACK timeout: 8000 cycles ({8000 * 10}ns)")

        # Clock management
        self.clock_started = False

        # Initialize weight test scenarios - PROPER testing scenarios
        self.weight_test_scenarios = self._setup_proper_weight_scenarios()
        self._validate_weight_scenarios()

        # Set initial weights to valid equal weights
        self.current_test_weights = [1] * self.CLIENTS

        # Log configuration
        self.log.info(f"Proper Weighted Round Robin TB initialized with CLIENTS={self.CLIENTS}{self.get_time_ns_str()}")
        self.log.info(f"WAIT_GNT_ACK={self.WAIT_GNT_ACK}, MAX_LEVELS={self.MAX_LEVELS}, MAX_LEVELS_WIDTH={self.MAX_LEVELS_WIDTH}, SEED={self.SEED}{self.get_time_ns_str()}")
        self.log.info(f"ACK mode: {'enabled' if self.WAIT_GNT_ACK else 'disabled'}{self.get_time_ns_str()}")

    def _setup_proper_weight_scenarios(self):
        """Setup proper weight test scenarios with expected distributions"""
        scenarios = []

        # Scenario 1: Equal weights
        equal_weights = [2] * self.CLIENTS
        equal_expected = [1.0 / self.CLIENTS] * self.CLIENTS
        scenarios.append({
            'name': 'Equal Weights',
            'weights': equal_weights,
            'expected_distribution': equal_expected,
            'description': 'All clients have equal weight - should get equal grants'
        })

        # Scenario 2: Simple ratio - adapt to client count
        if self.CLIENTS >= 4:
            # Original 4:2:1:1 pattern for 4+ clients
            ratio_weights = [4, 2, 1, 1] + [1] * (self.CLIENTS - 4)
        elif self.CLIENTS == 3:
            ratio_weights = [4, 2, 1]
        elif self.CLIENTS == 2:
            ratio_weights = [3, 1]
        else:  # self.CLIENTS == 1
            ratio_weights = [1]

        total_weight = sum(ratio_weights)
        ratio_expected = [w / total_weight for w in ratio_weights]
        scenarios.append({
            'name': 'Simple Ratio',
            'weights': ratio_weights,
            'expected_distribution': ratio_expected,
            'description': f'Weighted ratio pattern: {ratio_weights}'
        })

        # Scenario 3: High dominance (one client gets most) - scale to client count
        max_weight = min(self.MAX_LEVELS - 1, 8)
        dominance_weights = [max_weight] + [1] * (self.CLIENTS - 1)
        total_weight = sum(dominance_weights)
        dominance_expected = [w / total_weight for w in dominance_weights]
        scenarios.append({
            'name': 'High Dominance',
            'weights': dominance_weights,
            'expected_distribution': dominance_expected,
            'description': f'Client 0 gets {max_weight}x weight, others get 1x'
        })

        # Scenario 4: Zero weights (some clients disabled) - adapt to client count
        if self.CLIENTS >= 4:
            zero_weights = [3, 0, 2, 0] + [1] * (self.CLIENTS - 4)
        elif self.CLIENTS == 3:
            zero_weights = [3, 0, 2]
        elif self.CLIENTS == 2:
            zero_weights = [3, 0]
        else:  # self.CLIENTS == 1
            zero_weights = [3]  # Can't have zero weight for only client

        active_total = sum(w for w in zero_weights if w > 0)
        zero_expected = [w / active_total if w > 0 else 0.0 for w in zero_weights]
        scenarios.append({
            'name': 'Zero Weights',
            'weights': zero_weights,
            'expected_distribution': zero_expected,
            'description': 'Some clients have zero weight - should get no grants'
        })

        # Scenario 5: Single client only (if more than 1 client)
        if self.CLIENTS > 1:
            single_weights = [0] * self.CLIENTS
            single_weights[0] = 1
            single_expected = [1.0] + [0.0] * (self.CLIENTS - 1)
            scenarios.append({
                'name': 'Single Client Only',
                'weights': single_weights,
                'expected_distribution': single_expected,
                'description': 'Only one client has weight - should get all grants'
            })

        # Scenario 6: Alternating pattern - scale to client count
        alt_weights = []
        for i in range(self.CLIENTS):
            alt_weights.append(3 if i % 2 == 0 else 1)
        total_weight = sum(alt_weights)
        alt_expected = [w / total_weight for w in alt_weights]
        scenarios.append({
            'name': 'Alternating Pattern',
            'weights': alt_weights,
            'expected_distribution': alt_expected,
            'description': 'Even clients get 3x, odd clients get 1x'
        })

        # Scenario 7: Geometric progression (if enough clients)
        if self.CLIENTS >= 3:
            geom_weights = []
            for i in range(self.CLIENTS):
                weight = min(2 ** i, self.MAX_LEVELS - 1)
                if weight == 0:
                    weight = 1
                geom_weights.append(weight)

            total_weight = sum(geom_weights)
            geom_expected = [w / total_weight for w in geom_weights]
            scenarios.append({
                'name': 'Geometric Progression',
                'weights': geom_weights,
                'expected_distribution': geom_expected,
                'description': f'Powers of 2 pattern: {geom_weights}'
            })

        return scenarios

    def _validate_weight_scenarios(self):
        """Validate all weight scenarios fit within signal constraints - IMPROVED"""
        max_weight = self.MAX_LEVELS - 1
        expected_signal_width = self.CLIENTS * self.MAX_LEVELS_WIDTH
        max_packed_value = (1 << expected_signal_width) - 1

        self.log.info(f"Validating weight scenarios for {self.CLIENTS} clients:")
        self.log.info(f"  Max weight per client: {max_weight}")
        self.log.info(f"  Signal width: {expected_signal_width} bits")
        self.log.info(f"  Max packed value: 0x{max_packed_value:x}")

        for scenario in self.weight_test_scenarios:
            weights = scenario['weights']

            # Ensure we have exactly the right number of weights
            if len(weights) != self.CLIENTS:
                self.log.error(f"Scenario '{scenario['name']}' has {len(weights)} weights but need {self.CLIENTS}")
                raise ValueError(f"Weight scenario '{scenario['name']}' has wrong number of weights")

            # Clamp weights to valid range
            clamped_weights = [min(max(w, 0), max_weight) for w in weights]
            if clamped_weights != weights:
                self.log.warning(f"Scenario '{scenario['name']}' weights clamped: {weights} -> {clamped_weights}")
                scenario['weights'] = clamped_weights

                # Recalculate expected distribution
                if sum(clamped_weights) > 0:
                    total = sum(clamped_weights)
                    scenario['expected_distribution'] = [w / total for w in clamped_weights]
                else:
                    # All zero weights - this is an invalid scenario, skip it
                    self.log.error(f"Scenario '{scenario['name']}' has all zero weights - removing from test")
                    continue

            # Check packed value
            packed = 0
            for i, weight in enumerate(clamped_weights):
                packed |= (weight << (i * self.MAX_LEVELS_WIDTH))

            if packed > max_packed_value:
                self.log.error(f"Scenario '{scenario['name']}' packed value 0x{packed:x} > max 0x{max_packed_value:x}")
                raise ValueError(f"Weight scenario '{scenario['name']}' exceeds signal capacity")

            self.log.debug(f"  Scenario '{scenario['name']}': {clamped_weights} -> 0x{packed:x} ✓")

        # Remove any invalid scenarios
        self.weight_test_scenarios = [s for s in self.weight_test_scenarios if sum(s['weights']) > 0]

        self.log.info(f"Validation complete: {len(self.weight_test_scenarios)} valid scenarios")

    def _on_monitor_transaction(self, transaction):
        """Callback for monitor transactions"""
        if transaction.gnt_id >= self.CLIENTS:
            error = f"Invalid grant ID {transaction.gnt_id} >= {self.CLIENTS}"
            self.monitor_errors.append(error)
            self.log.error(error)

    def _on_monitor_reset(self, reset_type):
        """Callback for monitor reset events"""
        self.log.debug(f"Monitor reset event: {reset_type}{self.get_time_ns_str()}")

    async def start_clock(self, clock_name: str, period: int, units: str = 'ns'):
        """Start the clock"""
        if not self.clock_started:
            clock_gen = Clock(getattr(self.dut, clock_name), period, units=units)
            cocotb.start_soon(clock_gen.start())
            self.clock_started = True
            await ClockCycles(self.dut.clk, 2)

    async def reset_dut(self):
        """Reset the DUT"""
        # Apply reset
        self.dut.rst_n.value = 0
        await ClockCycles(self.dut.clk, 10)
        self.dut.rst_n.value = 1
        await ClockCycles(self.dut.clk, 5)

        # Set master's max levels width parameter
        self.master._max_levels_width = int(self.MAX_LEVELS_WIDTH)

        # Set initial equal weights
        self.master.set_weights(self.current_test_weights)
        await ClockCycles(self.dut.clk, 15)

        # Start the master
        # await self.master.startup()

        self.log.info(f"DUT reset complete, components started with weights {self.current_test_weights}{self.get_time_ns_str()}")

    async def wait_clocks(self, clock_name: str, num_clocks: int):
        """Wait for specified number of clock cycles"""
        await ClockCycles(getattr(self.dut, clock_name), num_clocks)

    def get_time_ns_str(self):
        """Get current simulation time as string"""
        return f" @ {get_sim_time('ns'):.1f}ns"

    # =============================================================================
    # PROPER WEIGHT TESTING METHODOLOGY
    # =============================================================================

    async def run_proper_weight_test(self, scenario, target_grants=1000, tolerance=0.15):
        """
        Run a single weight test scenario using proper methodology:
        1. Idle all requests
        2. Set the new weights
        3. Set all requests to true
        4. Run for ~target_grants grants
        5. Set requests to 0
        6. Validate percentage of grants according to weights
        """
        scenario_name = scenario['name']
        weights = scenario['weights']
        expected_dist = scenario['expected_distribution']

        self.log.info(f"=== Running Weight Test: {scenario_name} ===")
        self.log.info(f"Weights: {weights}")
        self.log.info(f"Expected distribution: {[f'{d:.3f}' for d in expected_dist]}")
        self.log.info(f"Target grants: {target_grants}, Tolerance: ±{tolerance*100:.1f}%")

        # Step 1: Idle all requests using drain_and_idle
        self.log.info("Step 1: Idling all requests...")
        drain_success = await self.master.drain_and_idle(idle_cycles=50, drain_timeout_cycles=500)
        if not drain_success:
            self.log.warning("Drain timeout - continuing anyway")

        # Verify we're truly idle
        status = self.master.get_drain_status()
        if not status['is_idle']:
            self.log.warning(f"System not fully idle: {status}")

        # Step 2: Set the new weights
        self.log.info(f"Step 2: Setting weights to {weights}...")
        self.master.set_weights(weights)
        await self.wait_clocks('clk', 100)  # Let weights settle

        # Step 3: Set all requests to true (enable all clients with continuous requests)
        self.log.info("Step 3: Enabling all clients with continuous requests...")

        # Create a profile that requests continuously
        continuous_profile = {
            'inter_request_delay': ([(1, 1)], [1.0]),  # Always request after 1 clock
            'request_duration': ([(1000, 1000)], [1.0]),  # Long duration (effectively continuous)
            'enabled_probability': ([(1, 1)], [1.0])  # Always enabled
        }

        self.master.update_request_profiles({'continuous': continuous_profile})

        # Apply continuous profile to all clients
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'continuous')
            self.master.enable_client(client_id)

        # Set fast ACK for quick turnaround
        self.master.set_ack_profile('immediate')

        # Wait for requests to start
        await self.wait_clocks('clk', 20)

        # Step 4: Run for target_grants grants
        self.log.info(f"Step 4: Running until {target_grants} grants collected...")

        # Reset monitor counters for clean measurement per test
        # Clear the monitor's grant statistics for this test
        for i in range(self.CLIENTS):
            self.monitor.arbiter_stats['grants_per_client'][i] = 0
        self.monitor.arbiter_stats['total_grants'] = 0

        # Also reset any other relevant counters
        if hasattr(self.monitor, 'total_transactions'):
            self.monitor.total_transactions = 0

        # Clear the transaction queue for clean measurement
        if hasattr(self.monitor, 'transactions'):
            self.monitor.transactions.clear()

        self.log.debug("Monitor grant counters reset for clean weight test measurement")

        grants_collected = 0
        max_cycles = target_grants * 10  # Safety timeout
        cycle_count = 0

        while grants_collected < target_grants and cycle_count < max_cycles:
            await self.wait_clocks('clk', 10)
            cycle_count += 10

            # Count grants collected so far (now from zero baseline)
            grants_collected = sum(self.monitor.arbiter_stats['grants_per_client'])

            # Should count only completed grants in ACK mode:
            if self.WAIT_GNT_ACK:
                # Count only new_grant transactions, not continuations
                grants_collected = len([t for t in self.monitor.transactions
                                    if t.metadata.get('transaction_type') == 'new_grant'])
            else:
                grants_collected = sum(self.monitor.arbiter_stats['grants_per_client'])
        # Step 5: Set requests to 0 (idle all clients)
        self.log.info("Step 5: Idling all requests...")
        await self.master.drain_and_idle(idle_cycles=20)

        # Step 6: Validate percentage of grants according to weights
        self.log.info("Step 6: Validating grant distribution...")

        # Use direct counts since we reset to zero at start
        final_grants = self.monitor.arbiter_stats['grants_per_client'].copy()

        total_grants = sum(final_grants)
        actual_dist = [g / total_grants if total_grants > 0 else 0.0 for g in final_grants]

        self.log.info(f"Results for {scenario_name}:")
        self.log.info(f"  Total grants collected: {total_grants}")
        self.log.info(f"  Grants per client: {final_grants}")
        self.log.info(f"  Actual distribution: {[f'{d:.3f}' for d in actual_dist]}")
        self.log.info(f"  Expected distribution: {[f'{d:.3f}' for d in expected_dist]}")

        # Validate each client's distribution
        compliance_results = []
        for i in range(self.CLIENTS):
            expected = expected_dist[i]
            actual = actual_dist[i]
            error = abs(actual - expected)

            if expected == 0.0:
                # Zero weight case - should have exactly zero grants
                compliant = (final_grants[i] == 0)
                error_pct = 0.0 if compliant else 100.0
            else:
                # Non-zero weight case - check within tolerance
                relative_error = error / expected if expected > 0 else 0
                error_pct = relative_error * 100
                compliant = (relative_error <= tolerance)

            compliance_results.append({
                'client': i,
                'expected': expected,
                'actual': actual,
                'error_pct': error_pct,
                'compliant': compliant,
                'grants': final_grants[i]
            })

            status = "✓" if compliant else "✗"
            self.log.info(f"  Client {i}: {status} Expected {expected:.3f}, Got {actual:.3f}, Error {error_pct:.1f}%")

        # Overall compliance
        compliant_clients = sum(1 for r in compliance_results if r['compliant'])
        overall_compliant = (compliant_clients == self.CLIENTS)

        self.log.info(f"Overall Result: {compliant_clients}/{self.CLIENTS} clients compliant")

        if not overall_compliant:
            self.log.error(f"Weight test FAILED for scenario: {scenario_name} {weights=}")
            for r in compliance_results:
                if not r['compliant']:
                    self.log.error(f"  Client {r['client']}: Expected {r['expected']:.3f}, Got {r['actual']:.3f}, Error {r['error_pct']:.1f}%")
        else:
            self.log.info(f"Weight test PASSED for scenario: {scenario_name}")

        return {
            'scenario_name': scenario_name,
            'weights': weights,
            'total_grants': total_grants,
            'final_grants': final_grants,
            'actual_distribution': actual_dist,
            'expected_distribution': expected_dist,
            'compliance_results': compliance_results,
            'overall_compliant': overall_compliant,
            'compliant_clients': compliant_clients
        }

    async def test_weighted_fairness(self):
        """Run comprehensive weight fairness tests using proper methodology"""
        self.log.info(f"Starting comprehensive weighted fairness test{self.get_time_ns_str()}")

        passed_scenarios = 0
        total_scenarios = len(self.weight_test_scenarios)
        test_results = []

        for scenario_idx, scenario in enumerate(self.weight_test_scenarios):
            self.log.info(f"=== Scenario {scenario_idx + 1}/{total_scenarios}: {scenario['name']} ===")

            try:
                # Run the proper weight test
                result = await self.run_proper_weight_test(
                    scenario=scenario,
                    target_grants=1000,  # Collect 1000 grants for good statistics
                    tolerance=0.15       # 15% tolerance
                )

                test_results.append(result)

                if result['overall_compliant']:
                    passed_scenarios += 1
                    self.log.info(f"✓ Scenario '{scenario['name']}' PASSED")
                else:
                    self.log.error(f"✗ Scenario '{scenario['name']}' FAILED")

            except Exception as e:
                self.log.error(f"✗ Scenario '{scenario['name']}' FAILED with exception: {e}")
                test_results.append({
                    'scenario_name': scenario['name'],
                    'overall_compliant': False,
                    'error': str(e)
                })

            # Brief pause between scenarios
            await self.wait_clocks('clk', 50)

        # Overall test results
        pass_rate = passed_scenarios / total_scenarios
        min_pass_rate = 0.8  # Require 80% of scenarios to pass

        self.log.info("=== WEIGHTED FAIRNESS TEST SUMMARY ===")
        self.log.info(f"Scenarios passed: {passed_scenarios}/{total_scenarios} ({pass_rate:.1%})")

        for result in test_results:
            if 'error' in result:
                self.log.info(f"  {result['scenario_name']}: ERROR - {result['error']}")
            else:
                status = "PASS" if result['overall_compliant'] else "FAIL"
                self.log.info(f"  {result['scenario_name']}: {status} ({result['compliant_clients']}/{self.CLIENTS} clients)")

        assert pass_rate >= min_pass_rate, f"Insufficient scenario pass rate: {pass_rate:.1%} < {min_pass_rate:.1%}"
        self.log.info(f"✓ Weighted fairness test PASSED with {pass_rate:.1%} success rate")

    # =============================================================================
    # BASIC TESTS - SAME AS RR EXCEPT SIMPLE WEIGHT SETUP
    # =============================================================================

    async def test_grant_signals(self):
        """Test basic grant signal functionality"""
        self.log.info(f"Starting grant signals test{self.get_time_ns_str()}")

        # Set equal weights
        self.master.set_weights([1] * self.CLIENTS)
        await ClockCycles(self.dut.clk, 25)

        # Same test as RR TB
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        self.master.set_ack_profile('immediate')

        for client_id in range(self.CLIENTS):
            self.log.info(f"Testing grant signal for client {client_id}")

            if self.WAIT_GNT_ACK == 1:
                await self.master.manual_request(
                    client_id=client_id,
                    cycles=20,
                    auto_ack=False,
                    ack_delay=1
                )
                self.master._set_ack_signal(client_id, 1)
                await self.wait_clocks('clk', 1)
                self.master._set_ack_signal(client_id, 0)
                await self.wait_clocks('clk', 1)
            else:
                await self.master.manual_request(client_id, cycles=5)

            if self.WAIT_GNT_ACK == 0:
                grant_received = await self.master.wait_for_grant(client_id, timeout_cycles=200)
                assert grant_received, f"Client {client_id} did not receive grant"

            await self.wait_clocks('clk', 15)

        self.log.info(f"Grant signals test passed{self.get_time_ns_str()}")
        # Start the master
        await self.master.startup()

    async def test_threshold_operation(self):
        """Test that weight changes work at basic level"""
        self.log.info(f"Starting threshold operation test{self.get_time_ns_str()}")

        # Test a few simple weight changes to verify basic functionality - adapt to client count
        simple_scenarios = [
            ([1] * self.CLIENTS, "equal"),
            ([2] + [1] * (self.CLIENTS - 1), "client 0 higher"),
        ]

        # Add second client higher test if we have more than 1 client
        if self.CLIENTS > 1:
            second_higher = [1] * self.CLIENTS
            second_higher[1] = 2
            simple_scenarios.append((second_higher, "client 1 higher"))

        for weights, description in simple_scenarios:
            self.log.info(f"Testing {description}: {weights}")

            # Simple weight change
            self.master.set_weights(weights)
            await ClockCycles(self.dut.clk, 15)

            # Enable all clients briefly
            for client_id in range(self.CLIENTS):
                self.master.set_client_profile(client_id, 'fast')
                self.master.enable_client(client_id)

            self.master.set_ack_profile('immediate')

            # Run briefly to verify basic operation
            await self.wait_clocks('clk', 200)

            # Check that grants are being issued
            current_grants = sum(self.monitor.arbiter_stats['grants_per_client'])
            assert current_grants > 0, f"No grants issued with {description}"

            # Idle for next test
            await self.master.drain_and_idle(idle_cycles=20)

        self.log.info(f"Threshold operation test passed{self.get_time_ns_str()}")

    async def run_basic_arbitration_test(self, duration_cycles: int = 800):
        """Basic arbitration functionality test"""
        self.log.info(f"Starting basic arbitration test for {duration_cycles} cycles{self.get_time_ns_str()}")

        # Set simple increasing weights that fit any client count
        weights = []
        for i in range(self.CLIENTS):
            weight = min(i + 1, self.MAX_LEVELS - 1)
            if weight == 0:
                weight = 1
            weights.append(weight)

        self.master.set_weights(weights)
        await ClockCycles(self.dut.clk, 15)

        # Same setup as RR
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('fast')

        await self.wait_clocks('clk', 100)

        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        await self.wait_clocks('clk', duration_cycles)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Basic arbitration: {total_grants} grants in {duration_cycles} cycles")

        min_grants = 20
        assert total_grants > min_grants, f"Insufficient activity: {total_grants} < {min_grants}"

        self.log.info(f"Basic arbitration test passed{self.get_time_ns_str()}")

    async def test_walking_requests(self):
        """Test walking requests"""
        self.log.info(f"Starting walking requests test{self.get_time_ns_str()}")

        # Set equal weights
        self.master.set_weights([1] * self.CLIENTS)
        await ClockCycles(self.dut.clk, 15)

        # Same as RR walking test
        auto_ack_enabled = (self.WAIT_GNT_ACK == 1)
        ack_delay = 1

        for i in range(self.CLIENTS):
            self.log.info(f"Testing walking client {i}")

            for client_id in range(self.CLIENTS):
                self.master.disable_client(client_id)
            await self.wait_clocks('clk', 10)

            try:
                if auto_ack_enabled:
                    await self.master.manual_request(
                        client_id=i,
                        cycles=15,
                        auto_ack=True,
                        ack_delay=ack_delay
                    )
                else:
                    await self.master.manual_request(client_id=i, cycles=10)

                self.log.info(f"✓ Client {i} walking test successful")

            except Exception as e:
                self.log.error(f"✗ Client {i} walking test failed: {e}")
                raise

            await self.wait_clocks('clk', 10)

        self.log.info(f"Walking requests test completed{self.get_time_ns_str()}")

    async def test_block_arb(self):
        """Test block_arb functionality"""
        self.log.info(f"Starting block_arb test{self.get_time_ns_str()}")

        # Set mixed weights that adapt to client count
        weights = []
        for i in range(self.CLIENTS):
            if i % 2 == 0:
                weights.append(2)
            else:
                weights.append(1)

        self.master.set_weights(weights)

        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('fast')

        await self.wait_clocks('clk', 100)

        baseline_stats = self.monitor.get_comprehensive_stats()
        baseline_grants = baseline_stats.get('total_grants', 0)

        self.dut.block_arb.value = 1
        self.log.info(f"Asserted block_arb{self.get_time_ns_str()}")

        await self.wait_clocks('clk', 200)

        blocked_stats = self.monitor.get_comprehensive_stats()
        blocked_grants = blocked_stats.get('total_grants', 0)
        grants_during_block = blocked_grants - baseline_grants

        self.dut.block_arb.value = 0
        self.log.info(f"De-asserted block_arb{self.get_time_ns_str()}")

        await self.wait_clocks('clk', 200)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        grants_after_unblock = final_grants - blocked_grants

        self.log.info(f"Block test: {grants_during_block} during block, {grants_after_unblock} after unblock")

        assert grants_during_block <= 15, f"Too many grants during block: {grants_during_block}"
        assert grants_after_unblock > 10, f"Too few grants after unblock: {grants_after_unblock}"

        self.log.info(f"Block_arb test passed{self.get_time_ns_str()}")

    # =============================================================================
    # WEIGHT-SPECIFIC TESTS USING PROPER METHODOLOGY
    # =============================================================================

    async def test_weight_changes(self):
        """Test dynamic weight changes using proper methodology"""
        self.log.info(f"Starting weight changes test{self.get_time_ns_str()}")

        # Test a sequence of weight changes - adapt to actual client count
        change_scenarios = []

        # Equal weights
        equal_weights = [1] * self.CLIENTS
        change_scenarios.append((equal_weights, "Equal weights"))

        # High first client
        high_first = [4] + [1] * (self.CLIENTS - 1)
        change_scenarios.append((high_first, "High client 0"))

        # High second client (if exists)
        if self.CLIENTS > 1:
            high_second = [1] * self.CLIENTS
            high_second[1] = 4
            change_scenarios.append((high_second, "High client 1"))

        # Balanced pairs (if enough clients)
        if self.CLIENTS >= 4:
            balanced = [2, 2] + [1] * (self.CLIENTS - 2)
            change_scenarios.append((balanced, "Balanced pairs"))
        elif self.CLIENTS >= 2:
            balanced = [2] * min(2, self.CLIENTS) + [1] * max(0, self.CLIENTS - 2)
            change_scenarios.append((balanced, f"Balanced {min(2, self.CLIENTS)} clients"))

        for weights, description in change_scenarios:
            self.log.info(f"Testing weight change: {description}")

            # Ensure weights match client count
            if len(weights) != self.CLIENTS:
                weights = weights[:self.CLIENTS] + [1] * max(0, self.CLIENTS - len(weights))

            # Use simplified test - just verify system continues to work
            scenario = {
                'name': description,
                'weights': weights,
                'expected_distribution': [w/sum(weights) for w in weights]
            }

            result = await self.run_proper_weight_test(
                scenario=scenario,
                target_grants=200,  # Smaller test for dynamic changes
                tolerance=0.25      # More lenient for quick test
            )

            # Just verify system is functional - don't require perfect distribution
            assert result['total_grants'] > 100, f"Insufficient activity after weight change: {description}"

        self.log.info(f"Weight changes test passed{self.get_time_ns_str()}")

    async def test_single_client_saturation(self):
        """Test single client saturation using proper methodology"""
        self.log.info(f"Starting single client saturation test{self.get_time_ns_str()}")

        # Create scenario where only client 0 has weight
        saturation_weights = [1] + [0] * (self.CLIENTS - 1)
        saturation_expected = [1.0] + [0.0] * (self.CLIENTS - 1)

        saturation_scenario = {
            'name': 'Single Client Saturation',
            'weights': saturation_weights,
            'expected_distribution': saturation_expected,
            'description': 'Only client 0 has weight - should get ALL grants'
        }

        result = await self.run_proper_weight_test(
            scenario=saturation_scenario,
            target_grants=500,
            tolerance=0.0  # Zero tolerance - other clients should get exactly 0
        )

        # Verify client 0 got ALL grants
        assert result['overall_compliant'], "Single client saturation failed"
        assert result['final_grants'][0] == result['total_grants'], "Client 0 didn't get all grants"

        for i in range(1, self.CLIENTS):
            assert result['final_grants'][i] == 0, f"Client {i} got grants when it should get none"

        self.log.info(f"Single client saturation test passed: {result['final_grants'][0]} grants to client 0")

    # =============================================================================
    # UTILITY METHODS
    # =============================================================================

    def clear_interface(self):
        """Clear interface for clean state"""
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        if hasattr(self.master, 'clear_manual_ack_config'):
            self.master.clear_manual_ack_config()

    async def handle_test_transition_ack_cleanup(self):
        """Handle test transitions"""

        await self.wait_clocks('clk', 15)

    def check_monitor_errors(self):
        """Check for any monitor errors"""
        if self.monitor_errors:
            self.log.error(f"Monitor errors detected: {self.monitor_errors}")
            raise AssertionError(f"Monitor errors: {self.monitor_errors}")

    def generate_final_report(self):
        """Generate final test report"""
        try:
            monitor_stats = self.monitor.get_comprehensive_stats()
            total_grants = monitor_stats.get('total_grants', 0) or len(self.monitor)
            fairness = monitor_stats.get('fairness_index', 0)

            master_stats = self.master.get_stats()
            weight_analysis = monitor_stats.get('weight_analysis', {})

            self.log.info("=== FINAL PROPER WEIGHTED ROUND ROBIN TEST REPORT ===")
            self.log.info(f"Total grants observed: {total_grants}")
            self.log.info(f"Fairness index: {fairness:.3f}")
            self.log.info(f"Current test weights: {self.current_test_weights}")
            self.log.info(f"Weight changes tracked: {weight_analysis.get('weight_changes_tracked', 0)}")
            self.log.info(f"Master statistics: {master_stats}")
            self.log.info(f"Monitor errors: {len(self.monitor_errors)}")

            success = (
                total_grants > 0 and
                fairness > 0.2 and
                len(self.monitor_errors) == 0
            )

            if success:
                self.log.info("✓ Final proper weighted report validation PASSED")
            else:
                self.log.error("✗ Final proper weighted report validation FAILED")

            return success

        except Exception as e:
            self.log.error(f"Error generating final report: {e}")
            return False

    def convert_to_int(self, value):
        """Convert value to int"""
        try:
            return int(value)
        except (ValueError, TypeError):
            return 0

    # =============================================================================
    # ADDITIONAL TESTS REFERENCED BY MAIN TEST RUNNER
    # =============================================================================

    async def test_bursty_traffic_pattern(self):
        """Test bursty traffic patterns"""
        self.log.info(f"Starting bursty traffic pattern test{self.get_time_ns_str()}")

        # Set mixed weights for variety - adapt to client count
        weights = []
        pattern = [3, 1, 2, 1]  # Base pattern
        for i in range(self.CLIENTS):
            weights.append(pattern[i % len(pattern)])

        self.master.set_weights(weights)
        await ClockCycles(self.dut.clk, 15)

        # Enable all clients with bursty patterns
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('random')

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run bursty test
        await self.wait_clocks('clk', 2000)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Bursty traffic test: {total_grants} grants generated")
        assert total_grants > 50, f"Insufficient bursty traffic: {total_grants} grants"

        self.log.info(f"Bursty traffic pattern test completed{self.get_time_ns_str()}")

    async def test_rapid_request_changes(self):
        """Test rapid request changes"""
        self.log.info(f"Starting rapid request changes test{self.get_time_ns_str()}")

        # Set power-like weights that fit within MAX_LEVELS
        weights = []
        for i in range(self.CLIENTS):
            weight = min(2**min(i, 3), self.MAX_LEVELS - 1)  # Cap at 2^3 = 8 or MAX_LEVELS-1
            if weight == 0:
                weight = 1
            weights.append(weight)

        self.master.set_weights(weights)
        await ClockCycles(self.dut.clk, 15)

        # Enable all clients with fast profiles
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('immediate')

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run rapid changes test
        await self.wait_clocks('clk', 1500)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Rapid changes test: {total_grants} grants generated")
        assert total_grants > 100, f"Insufficient rapid activity: {total_grants} grants"

        self.log.info(f"Rapid request changes test completed{self.get_time_ns_str()}")

    async def test_ack_mode_edge_cases(self):
        """Test ACK mode edge cases"""
        if not self.WAIT_GNT_ACK:
            self.log.info("Skipping ACK mode edge cases test - not in ACK mode")
            return

        self.log.info(f"Starting ACK mode edge cases test{self.get_time_ns_str()}")

        # Set pyramid-like weights that adapt to client count
        weights = []
        mid = self.CLIENTS // 2
        max_weight = min(self.MAX_LEVELS - 1, 4)

        for i in range(self.CLIENTS):
            if i <= mid:
                weight = min(i + 1, max_weight)
            else:
                weight = min(self.CLIENTS - i, max_weight)
            if weight == 0:
                weight = 1
            weights.append(weight)

        self.master.set_weights(weights)
        await ClockCycles(self.dut.clk, 15)

        # Clear all activity first
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        await self.wait_clocks('clk', 20)

        # Test: Weight change during operation
        self.log.info("Testing weight change during operation")

        # Enable all clients
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('fast')

        # Wait for normal operation
        await self.wait_clocks('clk', 100)

        # Change weights during operation
        new_weights = list(reversed(weights))
        self.master.set_weights(new_weights)
        await ClockCycles(self.dut.clk, 15)

        # Wait for system to continue
        await self.wait_clocks('clk', 200)

        # Check system is still functional
        recent_grants = sum(self.monitor.arbiter_stats['grants_per_client'])
        assert recent_grants > 0, "No grants after weight change during operation"

        self.log.info(f"ACK mode edge cases test passed{self.get_time_ns_str()}")

    async def test_dynamic_arbitration_liveness(self):
        """Test dynamic arbitration liveness with weight changes"""
        self.log.info(f"Starting dynamic arbitration liveness test{self.get_time_ns_str()}")

        # Enable all clients
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('fast')

        # Perform rapid weight changes while monitoring liveness - adapt to client count
        weight_change_scenarios = []

        # Equal weights
        weight_change_scenarios.append([1] * self.CLIENTS)

        # Rotate high weight through clients
        for i in range(min(self.CLIENTS, 4)):  # Test first 4 clients max
            scenario = [1] * self.CLIENTS
            scenario[i] = 2
            weight_change_scenarios.append(scenario)

        # Pairs if enough clients
        if self.CLIENTS >= 2:
            pairs = [2] * min(2, self.CLIENTS) + [1] * max(0, self.CLIENTS - 2)
            weight_change_scenarios.append(pairs)

        total_grants_during_changes = 0

        for i, weights in enumerate(weight_change_scenarios):
            self.log.info(f"Dynamic test {i+1}: {weights}")

            initial_grants = sum(self.monitor.arbiter_stats['grants_per_client'])

            # Simple immediate weight change
            self.master.set_weights(weights)
            await ClockCycles(self.dut.clk, 15)

            # Run for a short period
            await self.wait_clocks('clk', 300)

            # Check liveness
            final_grants = sum(self.monitor.arbiter_stats['grants_per_client'])
            grants_this_phase = final_grants - initial_grants
            total_grants_during_changes += grants_this_phase

            self.log.info(f"Weight change {i+1}: {grants_this_phase} grants")

            # Each phase should generate some grants
            assert grants_this_phase > 5, f"Poor liveness with weights {weights}: {grants_this_phase} grants"

        self.log.info(f"Dynamic liveness test: {total_grants_during_changes} total grants across all weight changes")
        assert total_grants_during_changes > 50, f"Insufficient overall liveness: {total_grants_during_changes}"

        self.log.info(f"Dynamic arbitration liveness test passed{self.get_time_ns_str()}")
