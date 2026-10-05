# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterRoundRobinSimpleTB
# Purpose: Simple Round Robin Testbench
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Simple Round Robin Testbench

Follows the WeightedRoundRobinTB methodology. The weighted TB's directed checks
are weight scenarios; an unweighted arbiter's are REQUEST-SET scenarios -- which
clients are requesting -- and the expected share is equal across the requesters
and exactly zero for everyone else.

Each scenario runs the same six steps as run_proper_weight_test:
  1. drain and idle   2. configure the requester set   3. continuous requests
  4. run to a target grant count   5. drain   6. validate the distribution

The class serves both simple arbiters. WAIT_GNT_ACK selects the mode exactly as
it does in the weighted TB; ArbiterRoundRobinSimpleAckTB sets it to 1.
"""

import math
import os
from collections import deque
import random
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import ClockCycles
from cocotb.clock import Clock

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.arbiter_monitor import RoundRobinArbiterMonitor
from CocoTBFramework.components.shared.arbiter_master import ArbiterMaster


class ArbiterRoundRobinSimpleTB(TBBase):
    """
    Simple Round Robin Arbiter Testbench (no block_arb, no weights)
    """

    # 0 = arbiter_round_robin_simple (combinational grant, no ACK)
    # 1 = arbiter_round_robin_simple_ack (registered grant held until grant_ack)
    WAIT_GNT_ACK = 0

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        self.CLIENTS = int(dut.N)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Per-test depth. REG_LEVEL picks how many parameter combinations run;
        # TEST_LEVEL decides how hard each one works.
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        random.seed(self.SEED)

        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n

        ack_mode = (self.WAIT_GNT_ACK == 1)
        self.monitor = RoundRobinArbiterMonitor(
            dut=dut,
            title="Simple_RR_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=self.dut.grant_ack if ack_mode else None,
            block_arb_signal=None,  # No block_arb in the simple arbiters
            clients=self.CLIENTS,
            ack_mode=ack_mode,
            log=self.log,
            clock_period_ns=10,
            # The no-ACK arbiter drives grant combinationally off request, so the
            # compliance check must pair it with the CURRENT request vector (common
            # BUG-008, was COMMON-018). The ACK arbiter registers its grant.
            registered_grant=ack_mode
        )

        self.master = ArbiterMaster(
            dut=dut,
            title="Simple_RR_Driver",
            clock=self.dut.clk,
            num_clients=self.CLIENTS,
            ack_mode=ack_mode,
            log=self.log
        )

        self.monitor_errors = []
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)
        self.monitor.enable_debug()

        # Same ACK timeout as the RR and WRR TBs
        if ack_mode and hasattr(self.monitor, 'compliance'):
            self.monitor.compliance.ack_timeout_cycles = 8000
            self.log.info(f"Configured ACK timeout: 8000 cycles ({8000 * 10}ns)")

        self.clock_started = False

        self.request_test_scenarios = self._setup_request_scenarios()
        self._validate_request_scenarios()

        self.log.info(f"Simple Round Robin TB initialized with CLIENTS={self.CLIENTS}{self.get_time_ns_str()}")
        self.log.info(f"WAIT_GNT_ACK={self.WAIT_GNT_ACK}, SEED={self.SEED}{self.get_time_ns_str()}")

    # =============================================================================
    # REQUEST-SET SCENARIOS (the unweighted analogue of weight scenarios)
    # =============================================================================

    def _scenario(self, name, requesters, description):
        """Build a scenario: equal share across requesters, zero for the rest."""
        share = 1.0 / len(requesters) if requesters else 0.0
        return {
            'name': name,
            'requesters': sorted(requesters),
            'expected_distribution': [share if c in requesters else 0.0
                                      for c in range(self.CLIENTS)],
            'description': description,
        }

    def _setup_request_scenarios(self):
        """Request patterns chosen to hit each path through the mask/fallback logic."""
        n = self.CLIENTS
        everyone = list(range(n))
        scenarios = [self._scenario('All Clients', everyone,
                                    'Every client requesting - full rotation, equal shares')]

        if n > 1:
            scenarios.append(self._scenario(
                'Single Client Only', [0],
                'Only client 0 requests - must get every grant, others none'))
            scenarios.append(self._scenario(
                'Last Client Only', [n - 1],
                'Only client N-1 requests - its win empties the mask, so every '
                'grant goes through the unmasked fallback'))
            scenarios.append(self._scenario(
                'Even Clients', [c for c in everyone if c % 2 == 0],
                'Even clients only - masked search must skip idle neighbours'))
            scenarios.append(self._scenario(
                'Odd Clients', [c for c in everyone if c % 2 == 1],
                'Odd clients only - client 0 idle, so the wrap lands on client 1'))

        if n >= 3:
            scenarios.append(self._scenario(
                'Wrap Pair', [0, n - 1],
                'Clients 0 and N-1 - alternates a masked hit and a fallback every grant'))
            scenarios.append(self._scenario(
                'All But One', [c for c in everyone if c != n // 2],
                f'Every client except {n // 2} - the hole must be skipped, never granted'))

        if n >= 4:
            scenarios.append(self._scenario(
                'Lower Half', everyone[:(n + 1) // 2],
                'Lower half only - upper mask bits never match, wrap every pass'))

        return scenarios

    def _validate_request_scenarios(self):
        """Every scenario must name valid clients; drop duplicates that small N produces."""
        seen = set()
        valid = []
        for scenario in self.request_test_scenarios:
            reqs = scenario['requesters']
            if not reqs:
                raise ValueError(f"Request scenario '{scenario['name']}' has no requesters")
            if any(c < 0 or c >= self.CLIENTS for c in reqs):
                raise ValueError(f"Request scenario '{scenario['name']}' names a client "
                                 f"outside 0..{self.CLIENTS - 1}: {reqs}")
            if abs(sum(scenario['expected_distribution']) - 1.0) > 1e-9:
                raise ValueError(f"Request scenario '{scenario['name']}' distribution "
                                 f"does not sum to 1")
            key = tuple(reqs)
            if key in seen:
                self.log.debug(f"Scenario '{scenario['name']}' duplicates an earlier "
                               f"requester set {reqs} at CLIENTS={self.CLIENTS} - dropped")
                continue
            seen.add(key)
            valid.append(scenario)
        self.request_test_scenarios = valid
        self.log.info(f"Validation complete: {len(valid)} request scenarios")

    def _on_monitor_transaction(self, transaction):
        """Callback for monitor transactions - validate transaction properties"""
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

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------

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

    async def reset_dut(self):
        """Reset the DUT. The master is started by test_grant_signals, as in the WRR TB."""
        self.dut.request.value = 0
        if self.WAIT_GNT_ACK:
            self.dut.grant_ack.value = 0
        self.dut.rst_n.value = 0
        await ClockCycles(self.dut.clk, 10)
        self.dut.rst_n.value = 1
        await ClockCycles(self.dut.clk, 5)
        self.log.info(f"DUT reset complete{self.get_time_ns_str()}")

    async def wait_clocks(self, clock_name: str, num_clocks: int):
        """Wait for specified number of clock cycles"""
        await ClockCycles(getattr(self.dut, clock_name), num_clocks)

    def get_time_ns_str(self):
        """Get current simulation time as string"""
        return f" @ {get_sim_time('ns'):.1f}ns"

    def _grants_of(self, client_id: int) -> int:
        """Cumulative monitor grant count for one client."""
        gpc = self.monitor.arbiter_stats.get('grants_per_client', [])
        return gpc[client_id] if client_id < len(gpc) else 0

    # =============================================================================
    # PROPER REQUEST-SET TESTING METHODOLOGY
    # =============================================================================

    def _reset_grant_counters(self, target_grants: int):
        """Zero the monitor's counters so the window is measured from a clean baseline."""
        for i in range(self.CLIENTS):
            self.monitor.arbiter_stats['grants_per_client'][i] = 0
        self.monitor.arbiter_stats['total_grants'] = 0
        if hasattr(self.monitor, 'total_transactions'):
            self.monitor.total_transactions = 0
        if hasattr(self.monitor, 'transactions'):
            # ACK mode counts progress from this deque, which the monitor caps at
            # 1000 -- size it to the target or the window silently becomes a
            # fixed-duration one (same fix as the WRR TB).
            need = max(2 * target_grants, 2048)
            if self.monitor.transactions.maxlen is not None and \
                    self.monitor.transactions.maxlen < need:
                self.monitor.transactions = deque(self.monitor.transactions, maxlen=need)
            self.monitor.transactions.clear()

    def _grants_collected(self) -> int:
        """Grants in the current window (ACK mode: new grants only, not continuations)."""
        if self.WAIT_GNT_ACK:
            return len([t for t in self.monitor.transactions
                        if t.metadata.get('transaction_type') == 'new_grant'])
        return sum(self.monitor.arbiter_stats['grants_per_client'])

    def _check_distribution(self, final_grants, expected_dist, tolerance):
        """Per-client verdicts: exact zero for non-requesters, else the larger of the
        relative tolerance and a 3-sigma counting band on the expected count."""
        total = sum(final_grants)
        results = []
        for i in range(self.CLIENTS):
            expected = expected_dist[i]
            actual = final_grants[i] / total if total else 0.0
            if expected == 0.0:
                compliant = (final_grants[i] == 0)
                error_pct = 0.0 if compliant else 100.0
            else:
                error_pct = abs(actual - expected) / expected * 100
                exp_count = expected * total
                allowed = max(tolerance * exp_count, 3.0 * math.sqrt(exp_count))
                compliant = abs(final_grants[i] - exp_count) <= allowed
            results.append({'client': i, 'expected': expected, 'actual': actual,
                            'error_pct': error_pct, 'compliant': compliant,
                            'grants': final_grants[i]})
            status = "OK" if compliant else "FAIL"
            self.log.info(f"  Client {i}: {status} Expected {expected:.3f}, "
                          f"Got {actual:.3f}, Error {error_pct:.1f}%")
        return results

    async def run_proper_request_test(self, scenario, target_grants=1000, tolerance=0.15):
        """
        Run one request-set scenario (same steps as run_proper_weight_test):
        1. Idle all requests
        2. Select the requester set
        3. Set those requests continuously true
        4. Run for ~target_grants grants
        5. Set requests to 0
        6. Validate the grant distribution
        """
        name = scenario['name']
        requesters = scenario['requesters']
        expected_dist = scenario['expected_distribution']

        self.log.info(f"=== Running Request Test: {name} ===")
        self.log.info(f"Requesters: {requesters}")
        self.log.info(f"Target grants: {target_grants}, Tolerance: ±{tolerance*100:.1f}%")

        # Step 1: Idle all requests
        if not await self.master.drain_and_idle(idle_cycles=50, drain_timeout_cycles=500):
            self.log.warning("Drain timeout - continuing anyway")
        status = self.master.get_drain_status()
        if not status['is_idle']:
            self.log.warning(f"System not fully idle: {status}")

        # Steps 2-3: only the scenario's requesters, requesting continuously
        self.master.update_request_profiles({'continuous': {
            'inter_request_delay': ([(1, 1)], [1.0]),
            'request_duration': ([(1000, 1000)], [1.0]),
            'enabled_probability': ([(1, 1)], [1.0]),
        }})
        for client_id in range(self.CLIENTS):
            if client_id in requesters:
                self.master.set_client_profile(client_id, 'continuous')
                self.master.enable_client(client_id)
            else:
                self.master.disable_client(client_id)
        self.master.set_ack_profile('immediate')
        await self.wait_clocks('clk', 20)

        # Step 4: run to the target from a zeroed baseline
        self._reset_grant_counters(target_grants)
        max_cycles = target_grants * 10  # Safety timeout
        cycles = 0
        while self._grants_collected() < target_grants and cycles < max_cycles:
            await self.wait_clocks('clk', 10)
            cycles += 10

        # Step 5: idle
        await self.master.drain_and_idle(idle_cycles=20)

        # Step 6: validate
        final_grants = self.monitor.arbiter_stats['grants_per_client'][:self.CLIENTS]
        total_grants = sum(final_grants)
        self.log.info(f"Results for {name}: {total_grants} grants, per client {final_grants}")
        results = self._check_distribution(final_grants, expected_dist, tolerance)
        compliant_clients = sum(1 for r in results if r['compliant'])
        overall = (compliant_clients == self.CLIENTS) and total_grants > 0

        if overall:
            self.log.info(f"Request test PASSED for scenario: {name}")
        else:
            self.log.error(f"Request test FAILED for scenario: {name} {requesters=}")
            for r in results:
                if not r['compliant']:
                    self.log.error(f"  Client {r['client']}: Expected {r['expected']:.3f}, "
                                   f"Got {r['actual']:.3f} ({r['grants']} grants)")

        return {'scenario_name': name, 'requesters': requesters,
                'total_grants': total_grants, 'final_grants': final_grants,
                'compliance_results': results, 'overall_compliant': overall,
                'compliant_clients': compliant_clients}

    async def test_request_fairness(self):
        """Run every request-set scenario. Each is a directed check: ALL must pass."""
        self.log.info(f"Starting request-set fairness test{self.get_time_ns_str()}")
        target = {'gate': 500, 'func': 1000, 'full': 2500}[self.TEST_LEVEL]
        results = []

        for idx, scenario in enumerate(self.request_test_scenarios):
            self.log.info(f"=== Scenario {idx + 1}/{len(self.request_test_scenarios)}: "
                          f"{scenario['name']} ===")
            try:
                results.append(await self.run_proper_request_test(
                    scenario=scenario, target_grants=target, tolerance=0.15))
            except Exception as e:
                self.log.error(f"Scenario '{scenario['name']}' FAILED with exception: {e}")
                results.append({'scenario_name': scenario['name'],
                                'overall_compliant': False, 'error': str(e)})
            await self.wait_clocks('clk', 50)

        self.log.info("=== REQUEST-SET FAIRNESS SUMMARY ===")
        for r in results:
            if 'error' in r:
                self.log.info(f"  {r['scenario_name']}: ERROR - {r['error']}")
            else:
                verdict = "PASS" if r['overall_compliant'] else "FAIL"
                self.log.info(f"  {r['scenario_name']}: {verdict} "
                              f"({r['compliant_clients']}/{self.CLIENTS} clients) {r['final_grants']}")

        # No pass-rate tolerance: these are directed checks, not samples
        # ([[measure-over-the-window]]).
        failed = [r['scenario_name'] for r in results if not r.get('overall_compliant')]
        assert not failed, (
            f"{len(failed)} of {len(results)} request scenario(s) failed: {failed}. "
            f"Each is a directed check -- there is no pass-rate tolerance for these.")
        self.log.info(f"Request-set fairness test PASSED: {len(results)} scenarios")

    async def test_request_set_changes(self):
        """Change the requester set between short windows; arbitration must follow."""
        self.log.info(f"Starting request-set changes test{self.get_time_ns_str()}")
        n = self.CLIENTS
        sets = [(list(range(n)), "All clients"), ([0], "Client 0 only")]
        if n > 1:
            sets.append(([1], "Client 1 only"))
            sets.append(([0, 1], "Clients 0 and 1"))

        for requesters, description in sets:
            result = await self.run_proper_request_test(
                scenario=self._scenario(description, requesters, description),
                target_grants=200, tolerance=0.25)
            assert result['total_grants'] > 100, (
                f"Insufficient activity after request-set change: {description}")
            idle = [c for c in range(n) if c not in requesters and result['final_grants'][c]]
            assert not idle, f"{description}: non-requesting client(s) {idle} were granted"

        self.log.info(f"Request-set changes test passed{self.get_time_ns_str()}")

    async def test_single_client_saturation(self):
        """Only client 0 requests: it must get every grant, everyone else exactly zero."""
        self.log.info(f"Starting single client saturation test{self.get_time_ns_str()}")
        result = await self.run_proper_request_test(
            scenario=self._scenario('Single Client Saturation', [0],
                                    'Only client 0 requests - should get ALL grants'),
            target_grants=500, tolerance=0.0)

        assert result['overall_compliant'], "Single client saturation failed"
        assert result['final_grants'][0] == result['total_grants'], "Client 0 didn't get all grants"
        for i in range(1, self.CLIENTS):
            assert result['final_grants'][i] == 0, f"Client {i} got grants when it should get none"
        self.log.info(f"Single client saturation test passed: {result['final_grants'][0]} grants")

    # =============================================================================
    # BASIC TESTS
    # =============================================================================

    async def test_grant_signals(self):
        """Each client alone gets a grant (ACK mode: retired by an explicit ACK)."""
        self.log.info(f"Starting grant signals test{self.get_time_ns_str()}")

        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)
        self.master.set_ack_profile('immediate')

        for client_id in range(self.CLIENTS):
            self.log.info(f"Testing grant signal for client {client_id}")
            # Counted on the monitor: manual_request raises nothing when no grant
            # arrives, and in ACK mode the WRR TB's version asserted nothing at all.
            before = self._grants_of(client_id)
            if self.WAIT_GNT_ACK:
                await self.master.manual_request(client_id=client_id, cycles=20,
                                                 auto_ack=False, ack_delay=1)
                self.master._set_ack_signal(client_id, 1)
                await self.wait_clocks('clk', 1)
                self.master._set_ack_signal(client_id, 0)
                await self.wait_clocks('clk', 1)
            else:
                await self.master.manual_request(client_id, cycles=5)
            granted = self._grants_of(client_id) - before
            assert granted > 0, f"Client {client_id} did not receive grant"
            await self.wait_clocks('clk', 15)

        self.log.info(f"Grant signals test passed{self.get_time_ns_str()}")
        await self.master.startup()

    async def run_basic_arbitration_test(self, duration_cycles: int = 800):
        """Basic arbitration under the default random profile"""
        self.log.info(f"Starting basic arbitration test for {duration_cycles} cycles{self.get_time_ns_str()}")
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)
        self.master.set_ack_profile('fast')

        await self.wait_clocks('clk', 100)
        initial = self.monitor.get_comprehensive_stats().get('total_grants', 0)
        await self.wait_clocks('clk', duration_cycles)
        total_grants = self.monitor.get_comprehensive_stats().get('total_grants', 0) - initial

        self.log.info(f"Basic arbitration: {total_grants} grants in {duration_cycles} cycles")
        assert total_grants > 20, f"Insufficient activity: {total_grants} < 20"
        self.log.info(f"Basic arbitration test passed{self.get_time_ns_str()}")

    async def test_walking_requests(self):
        """One client at a time; each must be granted while it is the only requester."""
        self.log.info(f"Starting walking requests test{self.get_time_ns_str()}")
        cycles = 15 if self.WAIT_GNT_ACK else 10

        for i in range(self.CLIENTS):
            for client_id in range(self.CLIENTS):
                self.master.disable_client(client_id)
            await self.master.drain_and_idle(idle_cycles=10)

            before = self._grants_of(i)
            if self.WAIT_GNT_ACK:
                await self.master.manual_request(client_id=i, cycles=cycles,
                                                 auto_ack=True, ack_delay=1)
            else:
                await self.master.manual_request(client_id=i, cycles=cycles)
            granted = self._grants_of(i) - before
            assert granted > 0, (
                f"Client {i} was the ONLY requester for {cycles} cycles and received "
                f"no grant (WAIT_GNT_ACK={self.WAIT_GNT_ACK})")
            self.log.info(f"Client {i} walking test successful ({granted} grant(s))")
            await self.wait_clocks('clk', 10)

        self.log.info(f"Walking requests test completed{self.get_time_ns_str()}")

    async def _activity_window(self, profile, ack_profile, cycles, min_grants, label):
        """Enable everyone on a profile, run a window, assert a grant floor."""
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, profile)
            self.master.enable_client(client_id)
        self.master.set_ack_profile(ack_profile)

        initial = self.monitor.get_comprehensive_stats().get('total_grants', 0)
        await self.wait_clocks('clk', cycles)
        total_grants = self.monitor.get_comprehensive_stats().get('total_grants', 0) - initial

        self.log.info(f"{label}: {total_grants} grants generated")
        assert total_grants > min_grants, f"Insufficient {label.lower()}: {total_grants} grants"

    async def test_bursty_traffic_pattern(self):
        """Fast requests with random ACK latency"""
        self.log.info(f"Starting bursty traffic pattern test{self.get_time_ns_str()}")
        await self._activity_window('fast', 'random', 2000, 50, "Bursty traffic")
        self.log.info(f"Bursty traffic pattern test completed{self.get_time_ns_str()}")

    async def test_rapid_request_changes(self):
        """Fast request churn with immediate ACK"""
        self.log.info(f"Starting rapid request changes test{self.get_time_ns_str()}")
        await self._activity_window('fast', 'immediate', 1500, 100, "Rapid changes")
        self.log.info(f"Rapid request changes test completed{self.get_time_ns_str()}")

    async def test_dynamic_arbitration_liveness(self):
        """Swap the enabled client set under live traffic; every window must make progress."""
        self.log.info(f"Starting dynamic arbitration liveness test{self.get_time_ns_str()}")
        self.master.set_ack_profile('fast')

        n = self.CLIENTS
        windows = [list(range(n))]
        windows += [[c for c in range(n) if c != i] or [i] for i in range(min(n, 4))]
        if n >= 2:
            windows.append([0, n - 1])

        total = 0
        for i, enabled in enumerate(windows):
            # Drain first. In ACK mode the master only ACKs clients it still has
            # enabled, so disabling one that holds a grant strands it and the
            # arbiter -- correctly -- never grants again. That is a stimulus bug,
            # not a liveness failure (see drain_arbiter in the RR TB).
            await self.master.drain_and_idle(idle_cycles=5)
            for client_id in range(n):
                self.master.set_client_profile(client_id, 'default')
                if client_id in enabled:
                    self.master.enable_client(client_id)
                else:
                    self.master.disable_client(client_id)
            before = sum(self.monitor.arbiter_stats['grants_per_client'])
            await self.wait_clocks('clk', 300)
            this_phase = sum(self.monitor.arbiter_stats['grants_per_client']) - before
            total += this_phase
            self.log.info(f"Liveness window {i + 1} {enabled}: {this_phase} grants")
            assert this_phase > 5, f"Poor liveness with clients {enabled}: {this_phase} grants"

        self.log.info(f"Dynamic liveness test: {total} total grants across all windows")
        assert total > 50, f"Insufficient overall liveness: {total}"
        self.log.info(f"Dynamic arbitration liveness test passed{self.get_time_ns_str()}")

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
        """Check for any monitor errors, including the compliance verdict."""
        if self.monitor_errors:
            self.log.error(f"Monitor errors detected: {self.monitor_errors}")
            raise AssertionError(f"Monitor errors: {self.monitor_errors}")

        compliance = getattr(self.monitor, 'compliance', None)
        if compliance is None or not hasattr(compliance, 'get_warning_summary'):
            return
        summary = compliance.get_warning_summary()
        self.log.info(
            f"Compliance verdict: {summary['total_errors']} error(s), "
            f"{summary['total_warnings']} warning(s); "
            f"errors={summary['error_types']} warnings={summary['warning_types']}")
        errs = [w for w in compliance.protocol_warnings if w.get('severity') == 'error']
        assert summary['total_errors'] == 0, (
            f"Arbiter protocol compliance: {summary['total_errors']} error(s) "
            f"{summary['error_types']}\n" + "\n".join(
                f"  @{w.get('timestamp')}ns {w.get('type')}: {w.get('message')} "
                f"details={w.get('details')}" for w in errs[:10]))

        # 'unexpected_ack' is only a warning in the model, so it is gated here.
        # Every one must be accounted for by a stray ACK this TB injected on
        # purpose (the ACK TB's hold test counts its own); any other is an ACK
        # the monitor failed to pair with its grant. Before RTLDesignSherpa-DV
        # #50 (residual 2) was fixed that was 5,009 per single-requester window
        # on this arbiter, and it hid behind warning severity.
        injected = getattr(self, '_injected_stray_acks', 0)
        reported = summary['warning_types'].get('unexpected_ack', 0)
        assert reported == injected, (
            f"unexpected_ack: compliance reported {reported}, the TB injected "
            f"{injected} stray ACK edge(s) on purpose. A surplus is an ACK the "
            f"monitor could not pair with its grant; a shortfall means stray ACK "
            f"detection is broken.")

    def generate_final_report(self):
        """Generate final test report"""
        try:
            monitor_stats = self.monitor.get_comprehensive_stats()
            total_grants = monitor_stats.get('total_grants', 0) or len(self.monitor)
            fairness = monitor_stats.get('fairness_index', 0)

            self.log.info("=== FINAL SIMPLE ROUND ROBIN TEST REPORT ===")
            self.log.info(f"Total grants observed: {total_grants}")
            self.log.info(f"Fairness index: {fairness:.3f}")
            self.log.info(f"Master statistics: {self.master.get_stats()}")
            self.log.info(f"Monitor errors: {len(self.monitor_errors)}")

            # The cumulative fairness index is reported, not gated: it spans
            # deliberately unfair phases (single-client saturation, single-client
            # scenarios). test_request_fairness asserts per scenario window.
            success = total_grants > 0 and len(self.monitor_errors) == 0
            if success:
                self.log.info("Final report validation PASSED")
            else:
                self.log.error("Final report validation FAILED")
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
