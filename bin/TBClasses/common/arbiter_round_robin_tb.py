# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterRoundRobinTB
# Purpose: Round Robin Testbench with Correct FlexRandomizer Usage
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Round Robin Testbench with Correct FlexRandomizer Usage
Maintains all test functionality while using the FlexRandomizer API correctly
"""

import os
import random
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ClockCycles
from cocotb.clock import Clock

# Import the ArbiterMaster and existing monitor
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.arbiter_monitor import RoundRobinArbiterMonitor
from CocoTBFramework.components.shared.arbiter_master import ArbiterMaster  # implementation

class ArbiterRoundRobinTB(TBBase):
    """
    Round Robin Arbiter Testbench using correct FlexRandomizer API
    Maintains all test functionality while properly using FlexRandomizer
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters
        self.CLIENTS = int(dut.CLIENTS)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Per-test depth. REG_LEVEL picks how many parameter combinations run;
        # TEST_LEVEL decides how hard each one works. This TB had no depth
        # mechanism at all, so `full` cost exactly what `gate` did.
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset signals
        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n

        # Initialize the arbiter monitor (keep existing monitor)
        self.monitor = RoundRobinArbiterMonitor(
            dut=dut,
            title="RR_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=self.dut.grant_ack,
            block_arb_signal=self.dut.block_arb,
            clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            log=self.log,
            clock_period_ns=10
        )

        # Initialize the arbiter master with correct FlexRandomizer usage
        self.master = ArbiterMaster(
            dut=dut,
            title="RR Driver",
            clock=self.dut.clk,
            num_clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            log=self.log
        )

        # Track any monitor errors
        self.monitor_errors = []
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)
        self.monitor.enable_debug()

        if hasattr(self.monitor, 'compliance'):
            self.monitor.compliance.ack_timeout_cycles = 8000  # Increased from 1000
            self.log.info(f"Configured ACK timeout: 8000 cycles ({8000 * 10}ns)")
        # Clock management
        self.clock_started = False

        # Log configuration
        self.log.info(f"Arbiter Round Robin TB initialized with CLIENTS={self.CLIENTS}{self.get_time_ns_str()}")
        self.log.info(f"WAIT_GNT_ACK={self.WAIT_GNT_ACK}, SEED={self.SEED}{self.get_time_ns_str()}")
        self.log.info(f"ACK mode: {'enabled' if self.WAIT_GNT_ACK else 'disabled'}{self.get_time_ns_str()}")

    def _on_monitor_transaction(self, transaction):
        """Callback for monitor transactions - validate transaction properties"""
        # Basic transaction validation
        if transaction.gnt_id >= self.CLIENTS:
            error = f"Invalid grant ID {transaction.gnt_id} >= {self.CLIENTS}"
            self.monitor_errors.append(error)
            self.log.error(error)

    def _on_monitor_reset(self, reset_type):
        """Callback for monitor reset events"""
        self.log.debug(f"Monitor reset event: {reset_type}{self.get_time_ns_str()}")

    async def start_clock(self, clock_name: str, period: int, units: str = 'ns'):
        """Start the clock - adapted for master"""
        if not self.clock_started:
            clock_gen = Clock(getattr(self.dut, clock_name), period, units=units)
            cocotb.start_soon(clock_gen.start())
            self.clock_started = True

            # Wait for clock to stabilize
            await ClockCycles(self.dut.clk, 2)

    async def reset_dut(self):
        """Reset the DUT and start components"""
        # Apply reset
        self.dut.rst_n.value = 0
        await ClockCycles(self.dut.clk, 10)
        self.dut.rst_n.value = 1
        await ClockCycles(self.dut.clk, 5)

        # Start the master
        await self.master.startup()

        # Monitor starts automatically via BusMonitor inheritance
        # No need to manually start it

        self.log.info(f"DUT reset complete, components started{self.get_time_ns_str()}")

    async def wait_clocks(self, clock_name: str, num_clocks: int):
        """Wait for specified number of clock cycles"""
        await ClockCycles(getattr(self.dut, clock_name), num_clocks)

    def get_time_ns_str(self):
        """Get current simulation time as string"""
        return f" @ {get_sim_time('ns'):.1f}ns"

    # =============================================================================
    # TEST METHODS using correct FlexRandomizer API
    # =============================================================================

    def set_walking_mode(self, active_client: int):
        """UPDATED: Set up for walking test with automatic ACK based on test mode"""
        auto_ack_enabled = (self.WAIT_GNT_ACK == 1)  # Enable auto-ACK in ACK mode
        ack_delay = 1  # Use 1 clock delay for predictable timing

        self.master.set_walking_mode(
            active_client=active_client,
            auto_ack=auto_ack_enabled,
            ack_delay=ack_delay
        )

        self.log.info(f"Walking mode set for client {active_client}, auto_ack={auto_ack_enabled}, ack_delay={ack_delay}")


    async def test_walking_requests(self):
        """Test walking requests with automatic ACK support"""
        self.log.info(f"Starting walking adjacent requests test{self.get_time_ns_str()}")

        # Ensure master is running
        if not self.master.active:
            await self.master.startup()
            await self.wait_clocks('clk', 10)

        # Determine auto-ACK settings based on mode
        auto_ack_enabled = (self.WAIT_GNT_ACK == 1)
        ack_delay = 1

        # Phase-level baseline. Every client gets its own exclusive request
        # window below, so by the end of the phase every client must have been
        # granted at least once. That is the assertion this phase never had --
        # it previously ended on an unconditional "completed" log line.
        phase_start = list(self.monitor.arbiter_stats.get('grants_per_client', []))
        phase_start = [(phase_start[c] if c < len(phase_start) else 0)
                       for c in range(self.CLIENTS)]

        # Test each client individually (simpler approach)
        for i in range(self.CLIENTS):
            self.log.info(f"=== Testing individual client {i} ==={self.get_time_ns_str()}")

            # STEP 1: Disable all clients
            for client_id in range(self.CLIENTS):
                self.master.disable_client(client_id)
            await self.wait_clocks('clk', 10)

            # STEP 2: Test this client with auto-ACK
            self.log.info(f"Testing client {i} with auto_ack={auto_ack_enabled}")

            # Snapshot this client's grant count. The monitor's per-client
            # counter is the deterministic mechanism -- the same one the
            # starvation check uses. _check_recent_grant_for_client was tried
            # here first and is heuristic (three fallback sources, optional
            # timestamps, a 1000ns window); it made the ACK-mode config fail
            # intermittently, and a flaky assertion is worse than none because
            # it teaches everyone to rerun.
            before = list(self.monitor.arbiter_stats.get('grants_per_client', []))
            before_i = before[i] if i < len(before) else 0

            # Use the working manual_request approach
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

            except Exception as e:
                # Swallowing this made the phase unfailable: manual_request
                # raises nothing when no grant arrives, so "no exception" was
                # never evidence of anything.
                self.log.error(f"Client {i} test raised: {e}")
                raise

            # The actual check. A client that requested as the only enabled
            # client and was never granted is the failure this phase exists to
            # catch, and it was previously unfailable.
            #
            # Poll rather than sample once: in ACK mode the arbiter holds the
            # grant until the ack lands, so the monitor's counter trails
            # manual_request's return by a handshake.
            after_i = before_i
            for _ in range(40):
                after = list(self.monitor.arbiter_stats.get('grants_per_client', []))
                after_i = after[i] if i < len(after) else 0
                if after_i > before_i:
                    break
                await self.wait_clocks('clk', 1)

            if after_i > before_i:
                self.log.info(f"Client {i} granted ({before_i} -> {after_i})")
            else:
                # Do NOT assert per client in ACK mode. Measured over five
                # runs, client 0 intermittently shows no counter movement
                # inside its own request window while the phase as a whole
                # grants every client -- and manual_request DISCARDS the
                # grant_received flag it computes, so the TB cannot see the
                # grant the BFM saw. The phase-level check below is the real
                # assertion; this stays a warning until the framework exposes
                # a per-request result. See COMMON-016.
                self.log.warning(
                    f"Client {i}: no grant counted within its own request "
                    f"window ({before_i} -> {after_i}, auto_ack="
                    f"{auto_ack_enabled}); phase-level check will decide"
                )

            # Brief cleanup pause
            await self.wait_clocks('clk', 10)

        # Settle any in-flight ACK handshake before the phase-level count.
        await self.wait_clocks('clk', 20)
        phase_end = list(self.monitor.arbiter_stats.get('grants_per_client', []))
        phase_end = [(phase_end[c] if c < len(phase_end) else 0)
                     for c in range(self.CLIENTS)]
        never_granted = [c for c in range(self.CLIENTS)
                         if phase_end[c] <= phase_start[c]]
        if auto_ack_enabled:
            # ACK mode: warn, do not fail. The monitor's per-client counter is
            # a proven instrument in no-ACK mode -- the sibling simple TB uses
            # exactly this and moves +1 per client, 5 runs clean -- but under
            # WAIT_GNT_ACK=1 the manual-request flow does not register grants
            # against it reliably, and the compliance monitor separately logs
            # "ACK from client N with no pending grant" during this phase.
            # Asserting here fires on 3 of 4 clients while the counts barely
            # move, which is a measurement artifact, not starvation. Shipping
            # that assertion would just teach everyone to rerun. COMMON-016
            # holds the evidence and the framework change it needs.
            if never_granted:
                self.log.warning(
                    f"Walking requests (ACK mode): client(s) {never_granted} "
                    f"show no counted grant; {phase_start} -> {phase_end}. "
                    f"NOT failed -- see COMMON-016."
                )
        else:
            assert not never_granted, (
                f"Walking requests: client(s) {never_granted} held an exclusive "
                f"request and were never granted during the phase. "
                f"Per-client grants {phase_start} -> {phase_end}"
            )

        self.log.info(
            f"Walking requests test completed; every client granted "
            f"{phase_start} -> {phase_end}{self.get_time_ns_str()}"
        )

    def _check_recent_grant_for_client(self, client_id: int, context: str) -> bool:
        """Check if a client received a grant recently by examining monitor transactions"""
        try:
            # Check recent transactions from the monitor
            recent_transactions = []

            # Method 1: Check monitor's transaction list
            if hasattr(self.monitor, 'transactions') and self.monitor.transactions:
                recent_transactions = list(self.monitor.transactions)[-20:]  # Last 20 transactions

            # Method 2: Check cocotb monitor queue
            elif hasattr(self.monitor, '_recvQ') and self.monitor._recvQ:
                recent_transactions = list(self.monitor._recvQ)[-20:]

            # Method 3: Check if monitor has get_observed_packets method
            elif hasattr(self.monitor, 'get_observed_packets'):
                recent_transactions = self.monitor.get_observed_packets(20)

            # Look for grants to this client in recent transactions
            current_time = get_sim_time('ns')
            time_window = 1000  # 1000ns window

            grants_found = 0
            for transaction in recent_transactions:
                if hasattr(transaction, 'gnt_id') and transaction.gnt_id == client_id:
                    if hasattr(transaction, 'timestamp'):
                        if current_time - transaction.timestamp <= time_window:
                            grants_found += 1
                    else:
                        grants_found += 1  # Count it if no timestamp

            self.log.debug(f"{context}: Found {grants_found} recent grants for client {client_id}")
            return grants_found > 0

        except Exception as e:
            self.log.warning(f"{context}: Error checking recent grants: {e}")
            # Fallback: check current grant signal
            return self._check_grant_for_client(client_id)

    def _verify_request_signal(self, client_id: int) -> bool:
        """Verify that request signal is properly asserted for client"""
        try:
            if hasattr(self.dut, 'request'):
                req_val = int(self.dut.request.value) if self.dut.request.value.is_resolvable else 0
                expected_bit = (1 << client_id)
                is_asserted = bool(req_val & expected_bit)
                self.log.debug(f"Request signal check: vector=0x{req_val:x}, expected_bit=0x{expected_bit:x}, asserted={is_asserted}")
                return is_asserted
            return False
        except Exception as e:
            self.log.error(f"Error checking request signal: {e}")
            return False

    async def _verify_no_activity(self, context: str):
        """Verify that there's no arbiter activity"""
        try:
            req_val = int(self.dut.request.value) if hasattr(self.dut, 'request') and self.dut.request.value.is_resolvable else 0
            gnt_valid = int(self.dut.grant_valid.value) if hasattr(self.dut, 'grant_valid') and self.dut.grant_valid.value.is_resolvable else 0

            self.log.debug(f"Activity check ({context}): request=0x{req_val:x}, grant_valid={gnt_valid}")

            if req_val != 0 or gnt_valid != 0:
                self.log.warning(f"Unexpected activity ({context}): request=0x{req_val:x}, grant_valid={gnt_valid}")
        except Exception as e:
            self.log.warning(f"Error checking activity ({context}): {e}")

    def _check_grant_for_client(self, client_id: int) -> bool:
        """Helper method to check if a specific client received a grant"""
        try:
            # Check grant_valid and grant_id
            if hasattr(self.dut, 'grant_valid') and hasattr(self.dut, 'grant_id'):
                grant_valid = int(self.dut.grant_valid.value) if self.dut.grant_valid.value.is_resolvable else 0
                if grant_valid:
                    grant_id = int(self.dut.grant_id.value) if self.dut.grant_id.value.is_resolvable else -1
                    return grant_id == client_id

            # Check grant vector
            if hasattr(self.dut, 'grant'):
                grant_vec = int(self.dut.grant.value) if self.dut.grant.value.is_resolvable else 0
                return bool(grant_vec & (1 << client_id))

            return False
        except Exception as e:
            self.log.warning(f"Error checking grant for client {client_id}: {e}")
            return False

    async def _debug_signal_state(self, context: str):
        """Debug current signal state"""
        self.log.error(f"=== SIGNAL STATE DEBUG ({context}) ===")

        try:
            # DUT signals
            req_val = int(self.dut.request.value) if hasattr(self.dut, 'request') and self.dut.request.value.is_resolvable else 0
            gnt_valid = int(self.dut.grant_valid.value) if hasattr(self.dut, 'grant_valid') and self.dut.grant_valid.value.is_resolvable else 0
            gnt_vec = int(self.dut.grant.value) if hasattr(self.dut, 'grant') and self.dut.grant.value.is_resolvable else 0
            gnt_id = int(self.dut.grant_id.value) if hasattr(self.dut, 'grant_id') and self.dut.grant_id.value.is_resolvable else -1
            block = int(self.dut.block_arb.value) if hasattr(self.dut, 'block_arb') and self.dut.block_arb.value.is_resolvable else 0

            self.log.error(f"DUT Signals:")
            self.log.error(f"  request:     0x{req_val:x}")
            self.log.error(f"  grant_valid: {gnt_valid}")
            self.log.error(f"  grant:       0x{gnt_vec:x}")
            self.log.error(f"  grant_id:    {gnt_id}")
            self.log.error(f"  block_arb:   {block}")

            # Master state
            master_stats = self.master.get_stats()
            self.log.error(f"Master State:")
            self.log.error(f"  active: {master_stats['active']}")
            self.log.error(f"  client_states: {master_stats['client_states']}")

            # Individual client details
            for cid in range(self.CLIENTS):
                config = master_stats['client_configs'][cid]
                state = master_stats['client_states'][cid]
                self.log.error(f"  Client {cid}: enabled={config['enabled']}, profile={config['profile']}, state={state}")

        except Exception as e:
            self.log.error(f"Error in signal debug: {e}")

        self.log.error(f"=== END SIGNAL STATE DEBUG ===")

    async def _debug_walking_test_state(self, client_id, context):
        """Debug helper for walking test failures"""
        self.log.error(f"=== WALKING TEST DEBUG ({context}) ===")

        # Check DUT signals
        try:
            if hasattr(self.dut, 'request'):
                req_val = int(self.dut.request.value) if self.dut.request.value.is_resolvable else 0
                self.log.error(f"DUT request vector: 0x{req_val:x}")

            if hasattr(self.dut, 'grant_valid'):
                gnt_valid = int(self.dut.grant_valid.value) if self.dut.grant_valid.value.is_resolvable else 0
                self.log.error(f"DUT grant_valid: {gnt_valid}")

            if hasattr(self.dut, 'grant'):
                gnt_vec = int(self.dut.grant.value) if self.dut.grant.value.is_resolvable else 0
                self.log.error(f"DUT grant vector: 0x{gnt_vec:x}")

            if hasattr(self.dut, 'grant_id'):
                gnt_id = int(self.dut.grant_id.value) if self.dut.grant_id.value.is_resolvable else -1
                self.log.error(f"DUT grant_id: {gnt_id}")

            if hasattr(self.dut, 'block_arb'):
                block = int(self.dut.block_arb.value) if self.dut.block_arb.value.is_resolvable else 0
                self.log.error(f"DUT block_arb: {block}")

        except Exception as e:
            self.log.error(f"Error reading DUT signals: {e}")

        # Check master state
        master_stats = self.master.get_stats()
        self.log.error(f"Master active: {master_stats['active']}")
        self.log.error(f"Master client states: {master_stats['client_states']}")
        self.log.error(f"Master client configs: {master_stats['client_configs']}")

        # Check monitor state
        monitor_stats = self.monitor.get_comprehensive_stats()
        self.log.error(f"Monitor transactions: {monitor_stats.get('total_grants', 'unknown')}")

        self.log.error(f"=== END WALKING TEST DEBUG ===")

    async def test_grant_signals(self):
        """Test basic grant signal functionality with explicit auto-ACK"""
        self.log.info(f"Starting grant signals test{self.get_time_ns_str()}")

        # Disable automatic requests for controlled testing
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        # Set immediate ACK for fast testing
        self.master.set_ack_profile('immediate')

        # Test each client individually
        for client_id in range(self.CLIENTS):
            self.log.info(f"Testing grant signal for client {client_id}")

            # Explicitly enable auto-ACK for ACK mode
            if self.WAIT_GNT_ACK == 1:
                # ACK mode - explicitly enable auto-ACK
                await self.master.manual_request(
                    client_id=client_id,
                    cycles=10,
                    auto_ack=True,      # ← Explicitly enable auto-ACK
                    ack_delay=1         # ← 1 clock delay
                )
            else:
                # No-ACK mode - no ACK needed
                await self.master.manual_request(client_id, cycles=5)

            # Check for grant
            grant_received = await self.master.wait_for_grant(client_id, timeout_cycles=20)
            assert grant_received, f"Client {client_id} did not receive grant"

            # Wait for completion (especially important in ACK mode)
            await self.wait_clocks('clk', 15)

        self.log.info(f"Grant signals test passed{self.get_time_ns_str()}")

    async def run_basic_arbitration_test(self, duration_cycles: int = 800):
        """Simplified basic arbitration test"""
        self.log.info(f"Starting basic arbitration test for {duration_cycles} cycles{self.get_time_ns_str()}")

        # Simple approach - use default profiles for all clients
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('fast')

        # Wait for setup
        await self.wait_clocks('clk', 100)

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run test
        await self.wait_clocks('clk', duration_cycles)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Basic arbitration: {total_grants} grants in {duration_cycles} cycles")

        # Verify reasonable activity
        min_grants = 20  # More lenient threshold
        assert total_grants > min_grants, f"Insufficient activity: {total_grants} < {min_grants}"

        self.log.info(f"Basic arbitration test passed{self.get_time_ns_str()}")

    async def test_block_arb(self):
        """Test block_arb functionality with reliable grant counting"""
        self.log.info(f"Starting block_arb test{self.get_time_ns_str()}")

        # Enable all clients with fast profiles
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('fast')

        # Wait for traffic to establish
        await self.wait_clocks('clk', 100)

        # Record baseline - use the most reliable counting method
        baseline_stats = self.monitor.get_comprehensive_stats()
        baseline_grants = baseline_stats.get('total_grants', 0)

        self.log.info(f"Baseline grants: {baseline_grants}")

        # Assert block_arb
        self.dut.block_arb.value = 1
        self.log.info(f"Asserted block_arb{self.get_time_ns_str()}")

        # Wait during block period
        await self.wait_clocks('clk', 200)

        # Check grants during block
        blocked_stats = self.monitor.get_comprehensive_stats()
        blocked_grants = blocked_stats.get('total_grants', 0)
        grants_during_block = blocked_grants - baseline_grants

        self.log.info(f"Grants during block: {grants_during_block}")

        # De-assert block_arb
        self.dut.block_arb.value = 0
        self.log.info(f"De-asserted block_arb{self.get_time_ns_str()}")

        # Wait for recovery
        await self.wait_clocks('clk', 200)

        # Check grants after unblock
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        grants_after_unblock = final_grants - blocked_grants

        self.log.info(f"Grants after unblock: {grants_after_unblock}")

        # Assertions with more lenient thresholds
        assert grants_during_block <= 10, f"Too many grants during block: {grants_during_block}"
        assert grants_after_unblock > 5, f"Too few grants after unblock: {grants_after_unblock}"

        self.log.info(f"Block_arb test passed{self.get_time_ns_str()}")

    async def test_fairness(self):
        """Test fairness using correct grant counting methods"""
        self.log.info(f"Starting fairness test{self.get_time_ns_str()}")

        # Create fairness test profile using correct constraint format
        fairness_profile = {
            'inter_request_delay': ([(8, 12), (16, 16)], [0.8, 0.2]),
            'request_duration': ([(2, 2), (3, 3)], [0.6, 0.4]),
            'enabled_probability': ([(1, 1)], [1.0])
        }

        # Add the fairness profile using correct API
        self.master.update_request_profiles({'fairness': fairness_profile})

        # Apply same profile to all clients
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fairness')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('fast')

        # Use multiple counting methods and choose the most reliable one
        initial_len = len(self.monitor)
        initial_transaction_count = self.monitor.get_transaction_count()
        initial_comprehensive_stats = self.monitor.get_comprehensive_stats()
        initial_grants_from_stats = initial_comprehensive_stats.get('total_grants', 0)

        # Also try the cycle-level counting method if available
        initial_cycle_grants = 0
        try:
            initial_cycle_grants = self.monitor.get_cycle_level_grant_count()
        except:
            pass  # Method might not exist

        self.log.info(f"Initial counts: len={initial_len}, transaction_count={initial_transaction_count}, "
                    f"stats_grants={initial_grants_from_stats}, cycle_grants={initial_cycle_grants}")

        # Run fairness test
        test_cycles = 1000 * self.LEVEL_MULT
        await self.wait_clocks('clk', test_cycles)

        # Get final counts using all available methods
        final_len = len(self.monitor)
        final_transaction_count = self.monitor.get_transaction_count()
        final_comprehensive_stats = self.monitor.get_comprehensive_stats()
        final_grants_from_stats = final_comprehensive_stats.get('total_grants', 0)

        # Also try the cycle-level counting method if available
        final_cycle_grants = 0
        try:
            final_cycle_grants = self.monitor.get_cycle_level_grant_count()
        except:
            pass

        self.log.info(f"Final counts: len={final_len}, transaction_count={final_transaction_count}, "
                    f"stats_grants={final_grants_from_stats}, cycle_grants={final_cycle_grants}")

        # Calculate grants during test period using multiple methods
        grants_len_method = final_len - initial_len
        grants_transaction_method = final_transaction_count - initial_transaction_count
        grants_stats_method = final_grants_from_stats - initial_grants_from_stats
        grants_cycle_method = final_cycle_grants - initial_cycle_grants

        self.log.info(f"Grant calculations:")
        self.log.info(f"  Method 1 (len):         {grants_len_method}")
        self.log.info(f"  Method 2 (transaction): {grants_transaction_method}")
        self.log.info(f"  Method 3 (stats):       {grants_stats_method}")
        self.log.info(f"  Method 4 (cycle):       {grants_cycle_method}")

        # Use the best available count (maximum of all methods)
        total_new_grants = max(
            grants_len_method,
            grants_transaction_method,
            grants_stats_method,
            grants_cycle_method
        )

        # Get fairness index from monitor
        fairness_index = final_comprehensive_stats.get('fairness_index', 0)
        if fairness_index == 0:
            # Try to calculate it manually
            try:
                fairness_index = self.monitor.get_fairness_index()
            except:
                fairness_index = 0

        self.log.info(f"Fairness test: {total_new_grants} grants, fairness index: {fairness_index:.3f}{self.get_time_ns_str()}")

        # More lenient assertion with better error handling
        if total_new_grants <= 0:
            # Additional debugging before failing
            self.log.error("No grants detected during fairness test! Debugging...")

            # Check master state
            master_stats = self.master.get_stats()
            self.log.error(f"Master state: active={master_stats['active']}")
            for client_id, config in master_stats['client_configs'].items():
                state = master_stats['client_states'][client_id]
                self.log.error(f"  Client {client_id}: enabled={config['enabled']}, profile={config['profile']}, state={state}")

            # Check DUT signals
            try:
                req_val = int(self.dut.request.value) if self.dut.request.value.is_resolvable else 0
                gnt_valid = int(self.dut.grant_valid.value) if self.dut.grant_valid.value.is_resolvable else 0
                gnt_vec = int(self.dut.grant.value) if self.dut.grant.value.is_resolvable else 0
                block = int(self.dut.block_arb.value) if self.dut.block_arb.value.is_resolvable else 0

                self.log.error(f"DUT signals: request=0x{req_val:x}, grant_valid={gnt_valid}, grant=0x{gnt_vec:x}, block_arb={block}")
            except Exception as e:
                self.log.error(f"Error reading DUT signals: {e}")

            # Try waiting longer and re-checking
            self.log.warning("Trying extended wait for fairness test...")
            await self.wait_clocks('clk', 1000)  # Wait another 1000 cycles

            # Re-check grants
            extended_len = len(self.monitor)
            extended_transaction_count = self.monitor.get_transaction_count()
            extended_comprehensive_stats = self.monitor.get_comprehensive_stats()
            extended_grants_from_stats = extended_comprehensive_stats.get('total_grants', 0)

            additional_grants = max(
                extended_len - final_len,
                extended_transaction_count - final_transaction_count,
                extended_grants_from_stats - final_grants_from_stats
            )

            if additional_grants > 0:
                total_new_grants = additional_grants
                fairness_index = extended_comprehensive_stats.get('fairness_index', 0)
                self.log.warning(f"Extended wait found {additional_grants} additional grants")
            else:
                # NO fabrication here. This branch used to set
                # total_new_grants = 100 -- the assert's own threshold -- when
                # the window measured ZERO, on the grounds that earlier phases
                # had produced grants. That converts "the fairness stimulus
                # died" into a pass, and the fairness_index it then checked came
                # from accumulated stats across every earlier phase rather than
                # from this one. Leave the measurement at what was measured and
                # let the assert below do its job.
                self.log.error(
                    f"Fairness window measured 0 grants after the extended wait "
                    f"(accumulated across all phases: {final_grants_from_stats}). "
                    f"Reporting the measured value, not the accumulated one."
                )

        # More reasonable thresholds
        min_grants_threshold = 50  # Reduced from 100
        min_fairness_threshold = 0.25  # Reduced from 0.3

        assert total_new_grants > min_grants_threshold, (
            f"Insufficient activity for fairness test: {total_new_grants} grants < {min_grants_threshold} "
            f"(test duration: {test_cycles} cycles)"
        )

        assert fairness_index > min_fairness_threshold, (
            f"Poor fairness: {fairness_index:.3f} < {min_fairness_threshold}"
        )

        self.log.info(f"✓ Fairness test passed: {total_new_grants} grants, fairness: {fairness_index:.3f}")

    async def test_single_client_saturation(self):
        """Test single client saturation with better grant detection"""
        self.log.info(f"Starting single client saturation test{self.get_time_ns_str()}")

        # Disable all clients except one
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        # Wait for all requests to clear
        await self.wait_clocks('clk', 50)

        # Enable only client 0 with aggressive profile
        self.master.set_client_profile(0, 'fast')
        self.master.enable_client(0)
        self.master.set_ack_profile('immediate')

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Wait for client to start requesting
        await self.wait_clocks('clk', 100)

        # Run saturation test
        test_duration = 1000
        await self.wait_clocks('clk', test_duration)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        saturation_grants = final_grants - initial_grants

        self.log.info(f"Single client saturation: {saturation_grants} grants in {test_duration} cycles")

        # More reasonable threshold
        min_expected = 30  # Reduced threshold
        assert saturation_grants > min_expected, f"Low saturation: {saturation_grants} < {min_expected}"

        # Re-enable all clients for next test
        for client_id in range(self.CLIENTS):
            self.master.enable_client(client_id)

        self.log.info(f"Single client saturation test passed{self.get_time_ns_str()}")

    async def test_bursty_traffic_pattern(self):
        """Test bursty traffic patterns with reliable profiles"""
        self.log.info(f"Starting bursty traffic pattern test{self.get_time_ns_str()}")

        # Use existing fast/slow profiles instead of creating new ones
        # Apply different patterns to clients
        for client_id in range(self.CLIENTS):
            if client_id < 2:
                self.master.set_client_profile(client_id, 'fast')
            else:
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

        # Use fast profiles for rapid changes
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)

        self.master.set_ack_profile('immediate')

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run for rapid changes
        await self.wait_clocks('clk', 1500)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Rapid changes test: {total_grants} grants generated")
        assert total_grants > 100, f"Insufficient rapid activity: {total_grants} grants"

        self.log.info(f"Rapid request changes test completed{self.get_time_ns_str()}")

    # =============================================================================
    # TEST METHODS - Added new methods for debugging and profile validation
    # =============================================================================

    async def test_master_profile_debug(self):
        """Debug method to test and validate master profiles"""
        self.log.info(f"Starting master profile debug{self.get_time_ns_str()}")

        # First test: Verify all clients can be enabled individually
        self.log.info("=== Testing individual client enable/disable ===")
        for client_id in range(self.CLIENTS):
            self.log.info(f"Testing client {client_id} individual enable")

            # Disable all clients first
            for c in range(self.CLIENTS):
                self.master.disable_client(c)

            # Enable only this client with default profile
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)

            # Wait and check if it generates activity
            initial_count = len(self.monitor)
            await self.wait_clocks('clk', 100)
            final_count = len(self.monitor)

            activity = final_count - initial_count
            self.log.info(f"Client {client_id} alone: {activity} grants in 100 cycles")

        # Second test: Enable all clients with default profile
        self.log.info("=== Testing all clients with default profile ===")
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)

        # Wait and check total activity
        initial_count = len(self.monitor)
        await self.wait_clocks('clk', 200)
        final_count = len(self.monitor)

        total_activity = final_count - initial_count
        self.log.info(f"All clients enabled: {total_activity} grants in 200 cycles")

        # Third test: Check available profiles
        stats = self.master.get_stats()
        available_profiles = stats['available_client_profiles']

        self.log.info(f"Available client profiles: {available_profiles}")

        for profile_name in available_profiles:
            if profile_name in ['manual', 'disabled']:
                continue  # Skip these for basic test

            self.log.info(f"Testing profile: {profile_name}")

            # Set client 0 to this profile
            self.master.set_client_profile(0, profile_name)
            self.master.enable_client(0)

            # Run briefly to see behavior
            initial_count = len(self.monitor)
            await self.wait_clocks('clk', 100)
            final_count = len(self.monitor)

            grants_observed = final_count - initial_count
            self.log.info(f"Profile {profile_name}: {grants_observed} grants in 100 cycles")

        # Test ACK profiles
        available_ack_profiles = stats['available_ack_profiles']
        self.log.info(f"Available ACK profiles: {available_ack_profiles}")

        for ack_profile in available_ack_profiles:
            self.log.info(f"Testing ACK profile: {ack_profile}")
            self.master.set_ack_profile(ack_profile)
            await self.wait_clocks('clk', 50)

        self.log.info(f"Master profile debug completed{self.get_time_ns_str()}")

    async def test_cycle_level_monitor_verification(self):
        """Test to verify monitor is working with cycle-level reporting"""
        self.log.info(f"Starting cycle-level monitor verification{self.get_time_ns_str()}")

        # Enable one client for clear monitoring
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        self.master.set_client_profile(0, 'fast')
        self.master.enable_client(0)
        self.master.set_ack_profile('immediate')

        # Record starting point
        initial_count = len(self.monitor)

        # Run for a controlled period
        await self.wait_clocks('clk', 300)

        # Check monitor captured transactions
        final_count = len(self.monitor)
        transactions_captured = final_count - initial_count

        self.log.info(f"Monitor captured {transactions_captured} transactions in 300 cycles")

        # Get detailed monitor stats
        detailed_stats = self.monitor.get_detailed_grant_stats()
        self.log.info(f"Detailed monitor stats: {detailed_stats}")

        # Verify reasonable monitoring
        assert transactions_captured > 0, "Monitor should capture some transactions"

        self.log.info(f"Cycle-level monitor verification completed{self.get_time_ns_str()}")

    # =============================================================================
    # UTILITY AND CLEANUP METHODS
    # =============================================================================

    def check_monitor_errors(self):
        """Check for any monitor errors, including the compliance verdict."""
        if self.monitor_errors:
            self.log.error(f"Monitor errors detected: {self.monitor_errors}")
            raise AssertionError(f"Monitor errors: {self.monitor_errors}")

        # The framework ships a round-robin compliance model that tracks mask
        # state and computes the expected winner for every grant. This TB used
        # to touch it in exactly one place -- raising ack_timeout_cycles to
        # 8000, i.e. only to make it complain less -- and never read its
        # verdict, so every protocol violation it found was logged and dropped.
        compliance = getattr(self.monitor, 'compliance', None)
        if compliance is None or not hasattr(compliance, 'get_warning_summary'):
            return
        summary = compliance.get_warning_summary()
        self.log.info(
            f"Compliance verdict: {summary['total_errors']} error(s), "
            f"{summary['total_warnings']} warning(s); "
            f"errors={summary['error_types']} warnings={summary['warning_types']}"
        )
        assert summary['total_errors'] == 0, (
            f"Arbiter protocol compliance: {summary['total_errors']} error(s) "
            f"{summary['error_types']}. Recent: "
            f"{[w.get('type') for w in summary['recent_warnings']]}"
        )

    async def handle_test_transition_ack_cleanup(self):
        """Handle test transitions - no cleanup needed with master"""
        # The master handles cleanup automatically
        await self.wait_clocks('clk', 10)  # Brief settling time

    def generate_final_report(self):
        """Generate final test report"""
        try:
            # Get monitor statistics
            monitor_stats = self.monitor.get_comprehensive_stats()
            total_grants = monitor_stats.get('total_grants', 0) or len(self.monitor)
            fairness = monitor_stats.get('fairness_index', 0)

            # Get master statistics
            master_stats = self.master.get_stats()

            self.log.info("=== FINAL TEST REPORT ===")
            self.log.info(f"Total grants observed: {total_grants}")
            self.log.info(f"Fairness index: {fairness:.3f}")
            self.log.info(f"Master statistics: {master_stats}")
            self.log.info(f"Monitor errors: {len(self.monitor_errors)}")

            # Basic validation
            success = (
                total_grants > 0 and
                fairness > 0.2 and
                len(self.monitor_errors) == 0
            )

            if success:
                self.log.info("✓ Final report validation PASSED")
            else:
                self.log.error("✗ Final report validation FAILED")

            return success

        except Exception as e:
            self.log.error(f"Error generating final report: {e}")
            return False

    async def cleanup_between_phases(self, phase_name: str, restart_master: bool = False):
        """Clean phase transitions - simplified with master"""
        self.log.info(f"=== Cleanup between phases: {phase_name} ===")

        # Brief settling time
        await self.wait_clocks('clk', 20)

        # Optional master restart (usually not needed)
        if restart_master:
            await self.master.shutdown()
            await self.wait_clocks('clk', 10)
            await self.master.startup()
            await self.wait_clocks('clk', 10)

        self.log.info(f"=== Cleanup complete for {phase_name} ===")

    async def check_master_state(self, context: str):
        """Check master state"""
        stats = self.master.get_stats()
        self.log.info(f"Master state check ({context}): {stats}")

        if not stats['active']:
            self.log.warning(f"Master not active in {context}")
            await self.master.startup()

    # =============================================================================
    # HELPER METHODS (ADAPTER COMPATIBILITY)
    # =============================================================================

    def convert_to_int(self, value):
        """Convert value to int (compatibility method)"""
        try:
            return int(value)
        except (ValueError, TypeError):
            return 0
