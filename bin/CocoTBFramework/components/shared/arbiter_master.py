# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ClientState
# Purpose: ArbiterMaster with Unified Behavior and Drain/Idle Functionality
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
ArbiterMaster with Unified Behavior and Drain/Idle Functionality
Identical behavior for weighted/unweighted arbiters except weight signal management
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.clock import Clock
from cocotb.utils import get_sim_time

from dataclasses import dataclass
from typing import Dict, Optional, Set, List
from enum import Enum

# Import the existing flex randomizer system
from .flex_randomizer import FlexRandomizer

class ClientState(Enum):
    IDLE = "IDLE"
    COUNTING = "COUNTING"
    REQUESTING = "REQUESTING"
    WAITING_ACK = "WAITING_ACK"
    MANUAL_CONTROL = "MANUAL_CONTROL"

@dataclass
class ClientConfig:
    """Simple client configuration"""
    enabled: bool = True
    randomizer_profile: str = "default"

class ArbiterMaster:
    """
    Unified arbiter master driver with identical behavior for weighted/unweighted arbiters
    """

    def __init__(self, dut, title, clock, num_clients: int, ack_mode: bool = True,
                is_weighted: bool = False, log=None):
        self.dut = dut
        self.title = title
        self.clock = clock
        self.num_clients = num_clients
        self.ack_mode = ack_mode
        self.is_weighted = is_weighted
        if log:
            self.log = log
        else:
            self.log = cocotb.log.getChild("ArbiterMaster")

        # Client management
        self.client_configs: Dict[int, ClientConfig] = {}
        self.client_timers: Dict[int, int] = {}
        self.client_states: Dict[int, ClientState] = {}

        # Create separate FlexRandomizers for each profile
        self.client_randomizers: Dict[str, FlexRandomizer] = {}
        self.ack_randomizers: Dict[str, FlexRandomizer] = {}
        self.current_ack_profile = "immediate"

        # Weight management - simple and immediate
        if self.is_weighted:
            self.current_weights = [1] * num_clients
            self._max_levels_width = 4  # Set by testbench if needed

        # Setup default profiles
        self._setup_default_profiles()

        # Tracking
        self.pending_acks: Set[int] = set()
        self.active = False

        # Tasks
        self._request_task = None
        self._grant_task = None

        # Initialize all clients
        for client_id in range(num_clients):
            self.client_configs[client_id] = ClientConfig()
            self.client_timers[client_id] = 0
            self.client_states[client_id] = ClientState.IDLE

    @staticmethod
    def get_time_ns_str():
        time_ns = get_sim_time('ns')
        return f' @ {time_ns}ns'

    def _setup_default_profiles(self):
        """Setup default randomization profiles"""
        # === CLIENT REQUEST PROFILES ===

        # Default profile
        default_constraints = {
            'inter_request_delay': ([(5, 10), (15, 20)], [0.7, 0.3]),
            'request_duration': ([(1, 2), (3, 3)], [0.8, 0.2]),
            'enabled_probability': ([(1, 1)], [1.0])
        }
        self.client_randomizers['default'] = FlexRandomizer(default_constraints)

        # Fast profile
        fast_constraints = {
            'inter_request_delay': ([(1, 2), (3, 3)], [0.8, 0.2]),
            'request_duration': ([(1, 1), (2, 2)], [0.9, 0.1]),
            'enabled_probability': ([(1, 1)], [1.0])
        }
        self.client_randomizers['fast'] = FlexRandomizer(fast_constraints)

        # Slow profile
        slow_constraints = {
            'inter_request_delay': ([(20, 30), (40, 50)], [0.6, 0.4]),
            'request_duration': ([(2, 3), (4, 5)], [0.7, 0.3]),
            'enabled_probability': ([(1, 1)], [1.0])
        }
        self.client_randomizers['slow'] = FlexRandomizer(slow_constraints)

        # Disabled profile
        disabled_constraints = {
            'inter_request_delay': ([(1000, 1000)], [1.0]),
            'request_duration': ([(1, 1)], [1.0]),
            'enabled_probability': ([(0, 0)], [1.0])
        }
        self.client_randomizers['disabled'] = FlexRandomizer(disabled_constraints)

        # Manual profile for walking tests
        manual_constraints = {
            'inter_request_delay': ([(1000, 1000)], [1.0]),
            'request_duration': ([(1, 1)], [1.0]),
            'enabled_probability': ([(1, 1)], [1.0])
        }
        self.client_randomizers['manual'] = FlexRandomizer(manual_constraints)

        # === ACK PROFILES ===

        # Immediate ACK
        immediate_ack_constraints = {
            'ack_delay': ([(0, 0)], [1.0]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['immediate'] = FlexRandomizer(immediate_ack_constraints)

        # Fast ACK
        fast_ack_constraints = {
            'ack_delay': ([(0, 0), (1, 2)], [0.7, 0.3]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['fast'] = FlexRandomizer(fast_ack_constraints)

        # Random ACK
        random_ack_constraints = {
            'ack_delay': ([(1, 2), (3, 5)], [0.6, 0.4]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['random'] = FlexRandomizer(random_ack_constraints)

        # Slow ACK
        slow_ack_constraints = {
            'ack_delay': ([(5, 10), (10, 15)], [0.7, 0.3]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['slow'] = FlexRandomizer(slow_ack_constraints)

    # =============================================================================
    # WEIGHT MANAGEMENT - SIMPLE AND IMMEDIATE (ONLY FOR WEIGHTED ARBITERS)
    # =============================================================================

    def set_weights(self, weights: List[int]):
        """
        Set weights immediately - simple signal assignment like any other DUT input
        Only active when is_weighted=True, no-op otherwise
        """
        if not self.is_weighted:
            return

        if len(weights) != self.num_clients:
            raise ValueError(f"Weight list length ({len(weights)}) != num_clients ({self.num_clients}){self.get_time_ns_str()}")

        # Clamp weights to valid range
        max_weight = (1 << self._max_levels_width) - 1
        clamped_weights = [min(max(w, 0), max_weight) for w in weights]

        # Pack and apply immediately - just like setting any other signal
        packed_weights = self._pack_weights(clamped_weights)

        try:
            if hasattr(self.dut, 'max_thresh'):
                self.dut.max_thresh.value = packed_weights
                self.current_weights = clamped_weights.copy()
                self.log.debug(f"ArbiterMaster({self.title}): Applied weights {clamped_weights} -> 0x{packed_weights:x}{self.get_time_ns_str()}")
            else:
                self.log.warning(f"ArbiterMaster({self.title}): max_thresh signal not found")
        except Exception as e:
            self.log.error(f"ArbiterMaster({self.title}): Error applying weights: {e}")
            raise

    def _pack_weights(self, weights: List[int]) -> int:
        """Pack individual weights into max_thresh signal format"""
        packed = 0
        for i, weight in enumerate(weights):
            packed |= (weight << (i * self._max_levels_width))
        return packed

    def get_current_weights(self) -> List[int]:
        """Get current weight configuration"""
        return self.current_weights.copy() if self.is_weighted else []

    # =============================================================================
    # DRAIN AND IDLE FUNCTIONALITY
    # =============================================================================

    async def drain_and_idle(self, idle_cycles: int = 100, drain_timeout_cycles: int = 500):
        """
        Drain all current requests and go idle for specified period

        Essential for clean testing scenarios:
        - Weight changes during idle periods
        - Block arbitration testing
        - Protocol compliance validation
        - Clean phase transitions

        Args:
            idle_cycles: How long to stay idle (no requests)
            drain_timeout_cycles: Max cycles to wait for current requests to complete

        Returns:
            bool: True if drain completed successfully, False if timeout
        """
        self.log.info(f"ArbiterMaster({self.title}): Starting drain and idle: drain_timeout={drain_timeout_cycles}, idle={idle_cycles} cycles{self.get_time_ns_str()}")

        # Step 1: Stop all new request generation by disabling all clients
        original_configs = {}
        for client_id in range(self.num_clients):
            original_configs[client_id] = {
                'enabled': self.client_configs[client_id].enabled,
                'profile': self.client_configs[client_id].randomizer_profile
            }
            self.disable_client(client_id)

        # Step 2: Wait for all current requests to drain
        self.log.debug("Waiting for current requests to drain...")
        drain_successful = False

        for cycle in range(drain_timeout_cycles):
            await RisingEdge(self.clock)

            # Check if all requests have cleared
            all_requests_clear = True
            active_requests = 0

            # Check request signals
            try:
                if hasattr(self.dut, 'request'):
                    req_val = int(self.dut.request.value) if self.dut.request.value.is_resolvable else 0
                    active_requests = req_val
                    if req_val != 0:
                        all_requests_clear = False
            except:
                pass

            # Check internal client states
            for client_id in range(self.num_clients):
                state = self.client_states[client_id]
                if state in [ClientState.REQUESTING, ClientState.WAITING_ACK]:
                    all_requests_clear = False

            # Check pending ACKs
            if self.ack_mode and len(self.pending_acks) > 0:
                all_requests_clear = False

            if all_requests_clear:
                drain_successful = True
                self.log.info(f"ArbiterMaster({self.title}): Drain completed successfully after {cycle} cycles{self.get_time_ns_str()}")
                break

            # Periodic progress reporting
            if cycle % 100 == 0 and cycle > 0:
                self.log.debug(f"Drain progress: cycle {cycle}, active_requests=0x{active_requests:x}, "
                            f"pending_acks={len(self.pending_acks)}{self.get_time_ns_str()}")

        if not drain_successful:
            self.log.warning(f"ArbiterMaster({self.title}): Drain timeout after {drain_timeout_cycles} cycles - forcing idle anyway{self.get_time_ns_str()}")

        # Step 3: Ensure all signals are cleared
        self._update_all_request_signals()  # Should be all zeros now

        # Step 4: ACK Mode Cleanup
        if self.ack_mode:
            self.log.debug(f"ArbiterMaster({self.title}): Starting ACK mode cleanup procedure{self.get_time_ns_str()}")

            # Ensure requests are cleared
            if hasattr(self.dut, 'request'):
                self.dut.request.value = 0

            # Clear any lingering ACK signals
            if hasattr(self.dut, 'grant_ack'):
                self.dut.grant_ack.value = 0

            # Wait one clock for signals to settle
            await ClockCycles(self.clock, 1)

            # Check if grant_valid is still asserted
            grant_valid_still_active = False
            current_grant_vector = 0

            try:
                if hasattr(self.dut, 'grant_valid') and self.dut.grant_valid.value.is_resolvable:
                    grant_valid_still_active = bool(int(self.dut.grant_valid.value))

                if grant_valid_still_active and hasattr(self.dut, 'grant') and self.dut.grant.value.is_resolvable:
                    current_grant_vector = int(self.dut.grant.value)

            except Exception as e:
                self.log.warning(f"ArbiterMaster({self.title}): Error reading grant signals during cleanup: {e}")

            if grant_valid_still_active:
                self.log.info(f"ArbiterMaster({self.title}): Grant still active (0x{current_grant_vector:x}), forcing ACK to complete transaction{self.get_time_ns_str()}")

                # Force ACK signal to match current grant to complete the transaction
                if hasattr(self.dut, 'grant_ack'):
                    self.dut.grant_ack.value = current_grant_vector

                # Wait one clock for ACK to be processed
                await ClockCycles(self.clock, 1)

                # Clear the ACK signal
                self.dut.grant_ack.value = 0

                # Wait one more clock for cleanup
                await ClockCycles(self.clock, 1)

                # Final check - grant_valid should now be clear
                try:
                    if hasattr(self.dut, 'grant_valid') and self.dut.grant_valid.value.is_resolvable:
                        final_grant_valid = bool(int(self.dut.grant_valid.value))

                        if final_grant_valid:
                            # Something is seriously wrong
                            self.log.error(f"ArbiterMaster({self.title}): FATAL ERROR - grant_valid still active after forced ACK cleanup!{self.get_time_ns_str()}")
                            self.log.error(f"  This indicates a serious problem with the arbiter ACK protocol implementation")
                            raise RuntimeError(f"ArbiterMaster({self.title}): ACK mode cleanup failed - grant_valid remains active")
                        else:
                            self.log.info(f"ArbiterMaster({self.title}): ACK cleanup successful - grant_valid now clear{self.get_time_ns_str()}")

                except Exception as e:
                    self.log.error(f"ArbiterMaster({self.title}): Error during final grant_valid check: {e}")
                    raise
            else:
                self.log.debug(f"ArbiterMaster({self.title}): No active grants detected during cleanup{self.get_time_ns_str()}")

        # Step 5: Stay idle for specified period
        self.log.info(f"ArbiterMaster({self.title}): Entering idle period for {idle_cycles} cycles{self.get_time_ns_str()}")
        await ClockCycles(self.clock, idle_cycles)

        # Step 6: Store configuration for restoration
        self._pre_drain_configs = original_configs

        self.log.info(f"ArbiterMaster({self.title}): Drain and idle completed, success={drain_successful}{self.get_time_ns_str()}")
        return drain_successful

    def restore_pre_drain_config(self):
        """Restore client configuration from before drain_and_idle()"""
        if not hasattr(self, '_pre_drain_configs'):
            self.log.warning(f"ArbiterMaster({self.title}): No pre-drain configuration to restore{self.get_time_ns_str()}")
            return

        self.log.info(f"ArbiterMaster({self.title}): Restoring pre-drain client configuration{self.get_time_ns_str()}")
        for client_id, config in self._pre_drain_configs.items():
            self.client_configs[client_id].enabled = config['enabled']
            self.client_configs[client_id].randomizer_profile = config['profile']

            if config['enabled']:
                self._restart_client_countdown(client_id)
            else:
                self.client_states[client_id] = ClientState.IDLE

        # Clear the stored config
        del self._pre_drain_configs

    async def idle_period(self, cycles: int):
        """Simple idle period without drain - just disable everything temporarily"""
        self.log.info(f"ArbiterMaster({self.title}): Starting idle period: {cycles} cycles{self.get_time_ns_str()}")

        # Store current state
        original_states = {}
        for client_id in range(self.num_clients):
            original_states[client_id] = {
                'enabled': self.client_configs[client_id].enabled,
                'state': self.client_states[client_id],
                'timer': self.client_timers[client_id]
            }

        # Force all clients to idle
        for client_id in range(self.num_clients):
            self.client_configs[client_id].enabled = False
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0

        self._update_all_request_signals()

        # Wait for idle period
        await ClockCycles(self.clock, cycles)

        # Restore original state
        for client_id, state in original_states.items():
            self.client_configs[client_id].enabled = state['enabled']
            self.client_states[client_id] = state['state']
            self.client_timers[client_id] = state['timer']

        self.log.info(f"ArbiterMaster({self.title}): Idle period completed, restored original state{self.get_time_ns_str()}")

    def get_drain_status(self) -> Dict:
        """Get current drain/idle status"""
        # Check if any requests are active
        active_requests = 0
        requesting_clients = []

        try:
            if hasattr(self.dut, 'request'):
                req_val = int(self.dut.request.value) if self.dut.request.value.is_resolvable else 0
                active_requests = req_val
                for i in range(self.num_clients):
                    if req_val & (1 << i):
                        requesting_clients.append(i)
        except:
            pass

        # Check internal states
        internal_activity = []
        for client_id in range(self.num_clients):
            state = self.client_states[client_id]
            if state != ClientState.IDLE:
                internal_activity.append({
                    'client': client_id,
                    'state': state.value,
                    'timer': self.client_timers[client_id]
                })

        return {
            'is_idle': (active_requests == 0 and len(internal_activity) == 0 and len(self.pending_acks) == 0),
            'active_request_vector': f"0x{active_requests:x}",
            'requesting_clients': requesting_clients,
            'internal_activity': internal_activity,
            'pending_acks': list(self.pending_acks),
            'has_pre_drain_config': hasattr(self, '_pre_drain_configs')
        }

    # =============================================================================
    # CONFIGURATION API - IDENTICAL FOR BOTH MODES
    # =============================================================================

    def set_client_profile(self, client_id: int, profile_name: str):
        """Set randomizer profile for specific client"""
        if client_id < self.num_clients and profile_name in self.client_randomizers:
            self.client_configs[client_id].randomizer_profile = profile_name
            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} profile set to '{profile_name}'{self.get_time_ns_str()}")
        else:
            self.log.warning(f"ArbiterMaster({self.title}): Invalid profile '{profile_name}' or client {client_id}{self.get_time_ns_str()}")

    def set_ack_profile(self, profile_name: str):
        """Set global ACK profile"""
        if profile_name in self.ack_randomizers:
            self.current_ack_profile = profile_name
            self.log.debug(f"ArbiterMaster({self.title}): ACK profile set to '{profile_name}'{self.get_time_ns_str()}")
        else:
            self.log.warning(f"ArbiterMaster({self.title}): Invalid ACK profile '{profile_name}'{self.get_time_ns_str()}")

    def enable_client(self, client_id: int):
        """Enable a client and start its countdown"""
        if client_id < self.num_clients:
            self.client_configs[client_id].enabled = True
            self._restart_client_countdown(client_id)
            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} enabled{self.get_time_ns_str()}")

    def disable_client(self, client_id: int):
        """Disable a client and clear its request"""
        if client_id < self.num_clients:
            self.client_configs[client_id].enabled = False
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0
            self._update_all_request_signals()
            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} disabled{self.get_time_ns_str()}")

    def enable_clients(self, client_list):
        """Enable multiple clients"""
        for client_id in client_list:
            self.enable_client(client_id)

    def disable_clients(self, client_list):
        """Disable multiple clients"""
        for client_id in client_list:
            self.disable_client(client_id)

    def set_walking_mode(self, active_client: int, auto_ack: bool = None, ack_delay: int = None):
        """Set up for walking test with automatic ACK support"""
        # Disable all clients first
        for client_id in range(self.num_clients):
            self.disable_client(client_id)
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0

        self._update_all_request_signals()
        self.clear_manual_ack_config()

        # Enable only the specified client
        if active_client < self.num_clients:
            self.client_configs[active_client].enabled = True
            self.client_configs[active_client].randomizer_profile = 'manual'
            self.client_states[active_client] = ClientState.IDLE
            self.client_timers[active_client] = 0

            # Set up auto-ACK if requested
            if auto_ack is True or (auto_ack is None and self.ack_mode):
                if ack_delay is None:
                    import random
                    ack_delay = random.randint(0, 3)
                else:
                    ack_delay = max(0, min(3, int(ack_delay)))

                if not hasattr(self, '_manual_ack_config'):
                    self._manual_ack_config = {}

                self._manual_ack_config[active_client] = {
                    'enabled': True,
                    'delay_clocks': ack_delay,
                    'grant_detected': False,
                    'ack_pending': False
                }

                self.log.info(f"ArbiterMaster({self.title}): Walking mode: client {active_client} ready with auto-ACK (delay={ack_delay}){self.get_time_ns_str()}")
            else:
                self.log.info(f"ArbiterMaster({self.title}): Walking mode: client {active_client} ready for manual control (no auto-ACK){self.get_time_ns_str()}")
        else:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client {active_client} for walking mode{self.get_time_ns_str()}")

    def force_client_request(self, client_id: int, enable: bool = True, auto_ack: bool = None, ack_delay: int = None):
        """Force a client request signal with automatic ACK support"""
        if client_id >= self.num_clients:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client_id {client_id}")
            return

        self.log.debug(f"ArbiterMaster({self.title}): FORCE REQUEST - client_id={client_id} enable={enable} auto_ack={auto_ack} ack_delay={ack_delay}{self.get_time_ns_str()}")

        if enable:
            self.client_states[client_id] = ClientState.MANUAL_CONTROL
            self.client_timers[client_id] = 0

            # Set up automatic ACK if requested
            if auto_ack is True or (auto_ack is None and self.ack_mode):
                if ack_delay is None:
                    import random
                    ack_delay = random.randint(0, 3)
                else:
                    ack_delay = max(0, min(3, int(ack_delay)))

                if not hasattr(self, '_manual_ack_config'):
                    self._manual_ack_config = {}

                self._manual_ack_config[client_id] = {
                    'enabled': True,
                    'delay_clocks': ack_delay,
                    'grant_detected': False,
                    'ack_pending': False
                }

                self.log.info(f"ArbiterMaster({self.title}): Client {client_id} manual control with auto-ACK enabled (delay={ack_delay} clocks)")
            else:
                if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                    del self._manual_ack_config[client_id]

                self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} set to MANUAL_CONTROL state (no auto-ACK)")

        else:
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0

            if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                del self._manual_ack_config[client_id]

            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} set to IDLE state (manual control cleared)")

        self._update_all_request_signals()

    # =============================================================================
    # PROFILE MANAGEMENT
    # =============================================================================

    def update_request_profiles(self, new_profiles: Dict):
        """Update request randomizer profiles using correct API with robust error handling"""
        for profile_name, constraints in new_profiles.items():
            try:
                self.log.debug(f"ArbiterMaster({self.title}): Adding profile '{profile_name}' with constraints: {constraints}")

                flex_constraints = self._convert_profile_to_constraints(constraints)
                self.log.debug(f"ArbiterMaster({self.title}): Converted constraints for '{profile_name}': {flex_constraints}")

                required_fields = ['inter_request_delay', 'request_duration', 'enabled_probability']
                for field in required_fields:
                    if field not in flex_constraints:
                        self.log.error(f"ArbiterMaster({self.title}): Profile '{profile_name}' missing required field: {field}")
                        continue

                self.client_randomizers[profile_name] = FlexRandomizer(flex_constraints)
                self.log.info(f"ArbiterMaster({self.title}): Successfully added request profile '{profile_name}'")

                # Test the randomizer
                test_randomizer = self.client_randomizers[profile_name]
                test_values = test_randomizer.next()
                self.log.debug(f"ArbiterMaster({self.title}): Test generation for '{profile_name}': {test_values}")

            except Exception as e:
                self.log.error(f"ArbiterMaster({self.title}): Failed to add profile '{profile_name}': {e}")
                import traceback
                self.log.error(f"ArbiterMaster({self.title}): Traceback: {traceback.format_exc()}")

    def update_ack_profiles(self, new_profiles: Dict):
        """Update ACK randomizer profiles using correct API"""
        for profile_name, constraints in new_profiles.items():
            try:
                flex_constraints = self._convert_profile_to_constraints(constraints)
                self.ack_randomizers[profile_name] = FlexRandomizer(flex_constraints)
                self.log.debug(f"ArbiterMaster({self.title}): Added ACK profile '{profile_name}'")
            except Exception as e:
                self.log.error(f"ArbiterMaster({self.title}): Failed to add ACK profile '{profile_name}': {e}")

    # =============================================================================
    # INTERNAL METHODS - IDENTICAL FOR BOTH MODES
    # =============================================================================

    def _update_all_request_signals(self):
        """Update the entire request vector based on current client states"""
        request_vector = 0
        for client_id in range(self.num_clients):
            if (self.client_states[client_id] == ClientState.REQUESTING or
                self.client_states[client_id] == ClientState.WAITING_ACK or
                self.client_states[client_id] == ClientState.MANUAL_CONTROL):
                request_vector |= (1 << client_id)

        try:
            if hasattr(self.dut, 'request'):
                self.dut.request.value = request_vector
                self.log.debug(f"ArbiterMaster({self.title}): Updated request vector to 0x{request_vector:x}{self.get_time_ns_str}")
            else:
                for client_id in range(self.num_clients):
                    bit_value = 1 if (request_vector & (1 << client_id)) else 0
                    req_signal = getattr(self.dut, f'request_{client_id}', None)
                    if req_signal is None:
                        req_signal = getattr(self.dut, f'req_{client_id}', None)
                    if req_signal is not None:
                        req_signal.value = bit_value
                        self.log.debug(f"ArbiterMaster({self.title}): Set req_{client_id} = {bit_value}")
        except Exception as e:
            self.log.warning(f"ArbiterMaster({self.title}): Could not set request signals: {e}")

    def _convert_profile_to_constraints(self, profile_dict: Dict) -> Dict:
        """Convert profile dictionary to FlexRandomizer constraint format with robust validation"""
        constraints = {}

        self.log.debug(f"ArbiterMaster({self.title}): Converting profile dict: {profile_dict}")

        for param_name, param_config in profile_dict.items():
            self.log.debug(f"ArbiterMaster({self.title}): Processing parameter '{param_name}': {param_config}")

            if isinstance(param_config, tuple) and len(param_config) == 2:
                bins, weights = param_config

                if not isinstance(bins, list) or not isinstance(weights, list):
                    self.log.error(f"ArbiterMaster({self.title}): Invalid bins/weights format for {param_name}: bins={bins}, weights={weights}")
                    continue

                if len(bins) != len(weights):
                    self.log.error(f"ArbiterMaster({self.title}): Bins/weights length mismatch for {param_name}: {len(bins)} vs {len(weights)}")
                    continue

                constraints[param_name] = param_config
                self.log.debug(f"ArbiterMaster({self.title}): Used existing format for {param_name}: {param_config}")

            elif isinstance(param_config, list):
                if len(param_config) == 0:
                    self.log.warning(f"ArbiterMaster({self.title}): Empty list for parameter {param_name}, skipping")
                    continue

                bins = []
                for val in param_config:
                    if isinstance(val, (int, float)):
                        bins.append((int(val), int(val)))
                    elif isinstance(val, (tuple, list)) and len(val) == 2:
                        bins.append((int(val[0]), int(val[1])))
                    else:
                        self.log.error(f"ArbiterMaster({self.title}): Invalid value in list for {param_name}: {val}")
                        continue

                weights = [1.0 / len(bins)] * len(bins)
                constraints[param_name] = (bins, weights)
                self.log.debug(f"ArbiterMaster({self.title}): Converted list to bins for {param_name}: bins={bins}, weights={weights}")

            else:
                self.log.error(f"ArbiterMaster({self.title}): Unsupported constraint format for {param_name}: {param_config} (type: {type(param_config)})")

        self.log.debug(f"ArbiterMaster({self.title}): Final converted constraints: {constraints}")
        return constraints

    def _restart_client_countdown(self, client_id: int):
        """Start new countdown for client - but only if not in manual control"""
        config = self.client_configs[client_id]

        if self.client_states[client_id] == ClientState.MANUAL_CONTROL:
            self.log.debug(f"ArbiterMaster({self.title}): Skipping countdown restart for client {client_id} - in manual control")
            return

        self.log.debug(f"ArbiterMaster({self.title}): _restart_client_countdown: client_id={client_id}, enabled={config.enabled}, profile={config.randomizer_profile}")

        if config.enabled:
            profile_name = config.randomizer_profile
            if profile_name in self.client_randomizers:
                try:
                    randomizer = self.client_randomizers[profile_name]
                    params = randomizer.next()

                    enabled_prob = params.get('enabled_probability', 1)
                    inter_request_delay = params.get('inter_request_delay', 10)

                    if enabled_prob > 0:
                        self.client_timers[client_id] = inter_request_delay
                        self.client_states[client_id] = ClientState.COUNTING
                        self.log.info(f"ArbiterMaster({self.title}): Client {client_id} COUNTDOWN STARTED: {inter_request_delay} cycles (profile: {profile_name})")
                    else:
                        self.client_states[client_id] = ClientState.IDLE
                        self.log.warning(f"ArbiterMaster({self.title}): Client {client_id} DISABLED by probability {enabled_prob} (profile: {profile_name})")

                except Exception as e:
                    self.log.error(f"ArbiterMaster({self.title}): Client {client_id}: Error generating values: {e}")
                    self.client_states[client_id] = ClientState.IDLE
            else:
                self.log.error(f"ArbiterMaster({self.title}): Client {client_id}: Unknown profile '{profile_name}'")
                self.client_states[client_id] = ClientState.IDLE

    def _check_grant_signal(self, client_id: int) -> bool:
        """Check if grant is asserted for client"""
        try:
            if hasattr(self.dut, 'grant_valid') and hasattr(self.dut, 'grant_id'):
                grant_valid = int(self.dut.grant_valid.value) if self.dut.grant_valid.value.is_resolvable else 0
                if grant_valid:
                    grant_id = int(self.dut.grant_id.value) if self.dut.grant_id.value.is_resolvable else -1
                    return grant_id == client_id
            elif hasattr(self.dut, 'grant'):
                grant_val = int(self.dut.grant.value) if self.dut.grant.value.is_resolvable else 0
                return bool(grant_val & (1 << client_id))
            else:
                grant_signal = getattr(self.dut, f'grant_{client_id}', None)
                if grant_signal is None:
                    grant_signal = getattr(self.dut, f'gnt_{client_id}', None)
                if grant_signal is not None:
                    return bool(int(grant_signal.value))
        except Exception as e:
            self.log.warning(f"ArbiterMaster({self.title}): Could not read grant signal for client {client_id}: {e}")

        return False

    def _set_ack_signal(self, client_id: int, value: int):
        """Set ACK signal for client"""
        if not self.ack_mode:
            return

        try:
            if hasattr(self.dut, 'grant_ack'):
                current_val = int(self.dut.grant_ack.value) if self.dut.grant_ack.value.is_resolvable else 0
                if value:
                    new_val = current_val | (1 << client_id)
                else:
                    new_val = current_val & ~(1 << client_id)
                self.dut.grant_ack.value = new_val
            else:
                ack_signal = getattr(self.dut, f'ack_{client_id}', None)
                if ack_signal is None:
                    ack_signal = getattr(self.dut, f'grant_ack_{client_id}', None)
                if ack_signal is not None:
                    ack_signal.value = value
        except Exception as e:
            self.log.warning(f"ArbiterMaster({self.title}): Could not set ACK signal for client {client_id}: {e}")

    # =============================================================================
    # ASYNC BACKGROUND PROCESSES - IDENTICAL FOR BOTH MODES
    # =============================================================================

    async def startup(self):
        """Initialize and start the arbiter master"""
        if self.active:
            return

        self.active = True
        await self.reset_signals()

        # Start background processes
        self._request_task = cocotb.start_soon(self._request_generator())
        self._grant_task = cocotb.start_soon(self._grant_monitor())

        self.log.info(f"ArbiterMaster({self.title}): Started (weighted: {self.is_weighted})")

    async def shutdown(self):
        """Clean shutdown of arbiter master"""
        if not self.active:
            return

        self.active = False

        # Clear manual ACK configurations
        self.clear_manual_ack_config()

        # Cancel background tasks
        if self._request_task and not self._request_task.done():
            self._request_task.cancel()
        if self._grant_task and not self._grant_task.done():
            self._grant_task.cancel()

        # Clear all signals
        await self.reset_signals()

        self.log.info(f"ArbiterMaster({self.title}): Stopped{self.get_time_ns_str()}")

    async def reset_signals(self):
        """Reset all signals and state"""
        await RisingEdge(self.clock)

        # Reset internal state first
        self.pending_acks.clear()
        for client_id in range(self.num_clients):
            config = self.client_configs[client_id]
            if config.enabled:
                self._restart_client_countdown(client_id)
            else:
                self.client_states[client_id] = ClientState.IDLE
                self.client_timers[client_id] = 0

        # Clear all request signals
        self._update_all_request_signals()

        # Clear ACK signals if needed
        if self.ack_mode:
            if hasattr(self.dut, 'grant_ack'):
                self.dut.grant_ack.value = 0
            else:
                for client_id in range(self.num_clients):
                    ack_signal = getattr(self.dut, f'ack_{client_id}', None)
                    if ack_signal is None:
                        ack_signal = getattr(self.dut, f'grant_ack_{client_id}', None)
                    if ack_signal is not None:
                        ack_signal.value = 0

        # Apply initial weights if weighted
        if self.is_weighted and hasattr(self, 'current_weights'):
            try:
                self.set_weights(self.current_weights)
            except Exception as e:
                self.log.warning(f"ArbiterMaster({self.title}): Could not apply initial weights during reset: {e}")

    async def _request_generator(self):
        """Generate requests based on correct FlexRandomizer usage - IDENTICAL FOR BOTH MODES"""
        while self.active:
            await RisingEdge(self.clock)

            for client_id in range(self.num_clients):
                config = self.client_configs[client_id]
                state = self.client_states[client_id]

                if state == ClientState.MANUAL_CONTROL:
                    continue

                if not config.enabled:
                    continue

                if state == ClientState.COUNTING:
                    self.client_timers[client_id] -= 1
                    if self.client_timers[client_id] <= 0:
                        profile_name = config.randomizer_profile
                        if profile_name in self.client_randomizers:
                            randomizer = self.client_randomizers[profile_name]
                            params = randomizer.next()
                            duration = params.get('request_duration', 1)

                            self.client_states[client_id] = ClientState.REQUESTING
                            self.client_timers[client_id] = duration

                elif state == ClientState.REQUESTING:
                    self.client_timers[client_id] -= 1
                    if self.client_timers[client_id] <= 0 and client_id not in self.pending_acks:
                        if not self.ack_mode:
                            self._restart_client_countdown(client_id)

            self._update_all_request_signals()

    async def _grant_monitor(self):
        """Monitor grants and handle ACK generation including manual control auto-ACK - IDENTICAL FOR BOTH MODES"""
        while self.active:
            await RisingEdge(self.clock)

            for client_id in range(self.num_clients):
                state = self.client_states[client_id]

                if (self._check_grant_signal(client_id) and
                    (state == ClientState.REQUESTING or state == ClientState.MANUAL_CONTROL)):

                    if self.ack_mode:
                        if (state == ClientState.MANUAL_CONTROL and
                            hasattr(self, '_manual_ack_config') and
                            client_id in self._manual_ack_config):

                            config = self._manual_ack_config[client_id]
                            if config['enabled'] and not config['ack_pending']:
                                config['ack_pending'] = True
                                config['grant_detected'] = True
                                cocotb.start_soon(self._generate_manual_ack(client_id))
                                self.log.debug(f"ArbiterMaster({self.title}): Started manual auto-ACK for client {client_id}")
                        else:
                            self.client_states[client_id] = ClientState.WAITING_ACK
                            if client_id not in self.pending_acks:
                                self.pending_acks.add(client_id)
                                cocotb.start_soon(self._generate_ack(client_id))
                    else:
                        if state == ClientState.MANUAL_CONTROL:
                            self.log.debug(f"ArbiterMaster({self.title}): Manual client {client_id} received grant, staying in manual control")
                        else:
                            self._restart_client_countdown(client_id)

    async def _generate_manual_ack(self, client_id: int):
        """Generate ACK signal for manual control with configurable delay"""
        try:
            if not hasattr(self, '_manual_ack_config') or client_id not in self._manual_ack_config:
                self.log.error(f"ArbiterMaster({self.title}): No manual ACK config for client {client_id}")
                return

            config = self._manual_ack_config[client_id]
            delay_cycles = config['delay_clocks']

            self.log.debug(f"ArbiterMaster({self.title}): Generating manual ACK for client {client_id} with {delay_cycles} cycle delay")

            if delay_cycles > 0:
                await ClockCycles(self.clock, delay_cycles)

            if (self.active and
                config['grant_detected'] and
                self._check_grant_signal(client_id)):

                self._set_ack_signal(client_id, 1)
                self.log.info(f"ArbiterMaster({self.title}): Client {client_id} manual ACK asserted (delay={delay_cycles} cycles){self.get_time_ns_str()}")

                await ClockCycles(self.clock, 1)
                self._set_ack_signal(client_id, 0)

                self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} manual ACK completed{self.get_time_ns_str()}")
            else:
                self.log.warning(f"ArbiterMaster({self.title}): Manual ACK for client {client_id} cancelled - grant no longer present")

            config['ack_pending'] = False
            config['grant_detected'] = False

        except Exception as e:
            self.log.error(f"ArbiterMaster({self.title}): Manual ACK generation error for client {client_id}: {e}{self.get_time_ns_str()}")

            if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                self._manual_ack_config[client_id]['ack_pending'] = False
                self._manual_ack_config[client_id]['grant_detected'] = False

    async def _generate_ack(self, client_id: int):
        """Generate ACK signal with correct FlexRandomizer timing"""
        try:
            if self.current_ack_profile in self.ack_randomizers:
                ack_randomizer = self.ack_randomizers[self.current_ack_profile]
                params = ack_randomizer.next()
                delay_cycles = params.get('ack_delay', 0)
                duration_cycles = params.get('ack_duration', 1)

                if delay_cycles > 0:
                    await ClockCycles(self.clock, delay_cycles)

                if self.active and client_id in self.pending_acks:
                    self._set_ack_signal(client_id, 1)
                    self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} ACK asserted (delay={delay_cycles}, profile={self.current_ack_profile}){self.get_time_ns_str()}")

                    await ClockCycles(self.clock, duration_cycles)
                    self._set_ack_signal(client_id, 0)

                    self.pending_acks.discard(client_id)
                    self._restart_client_countdown(client_id)
                    self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} transaction complete{self.get_time_ns_str()}")
            else:
                self.log.error(f"ArbiterMaster({self.title}): Unknown ACK profile: {self.current_ack_profile}{self.get_time_ns_str()}")

        except Exception as e:
            self.log.error(f"ArbiterMaster({self.title}): ACK generation error for client {client_id}: {e}{self.get_time_ns_str()}")
            self.pending_acks.discard(client_id)

    # =============================================================================
    # TEST UTILITY METHODS
    # =============================================================================

    async def wait_for_grant(self, client_id: int, timeout_cycles: int = 100) -> bool:
        """Wait for grant signal for specific client"""
        for _ in range(timeout_cycles):
            if self._check_grant_signal(client_id):
                return True
            await RisingEdge(self.clock)
        return False

    async def manual_request(self, client_id: int, cycles: int = 1, auto_ack: bool = None, ack_delay: int = None):
        """Manually assert request for specified cycles with automatic ACK support - IDENTICAL FOR BOTH MODES"""
        if client_id >= self.num_clients:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client_id {client_id} for manual request")
            return

        self.log.debug(f"ArbiterMaster({self.title}): Manual Request - client_id={client_id} cycles={cycles} auto_ack={auto_ack} ack_delay={ack_delay}{self.get_time_ns_str()}")

        self.force_client_request(client_id, enable=True, auto_ack=auto_ack, ack_delay=ack_delay)

        grant_received = False
        for cycle in range(cycles):
            await RisingEdge(self.clock)

            if self._check_grant_signal(client_id):
                grant_received = True
                self.log.debug(f"ArbiterMaster({self.title}): Manual request for client {client_id} received grant at cycle {cycle}")

                if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                    self._manual_ack_config[client_id]['grant_detected'] = True

                break

        if grant_received and hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
            config = self._manual_ack_config[client_id]
            if config['enabled']:
                self.log.debug(f"ArbiterMaster({self.title}): Grant received for client {client_id}, waiting for auto-ACK to complete")

                self.client_states[client_id] = ClientState.MANUAL_CONTROL
                self._update_all_request_signals()

                ack_delay_cycles = config['delay_clocks']
                total_wait = ack_delay_cycles + 5
                await ClockCycles(self.clock, total_wait)

                if client_id in self._manual_ack_config:
                    del self._manual_ack_config[client_id]

                self.log.debug(f"ArbiterMaster({self.title}): Manual request completed for client {client_id}, auto-ACK should be done")
            else:
                self.force_client_request(client_id, enable=False)
        else:
            self.force_client_request(client_id, enable=False)
            self.log.debug(f"ArbiterMaster({self.title}): Manual request ended for client {client_id}, grant_received={grant_received}")

        self.client_states[client_id] = ClientState.IDLE
        self.client_timers[client_id] = 0
        self._update_all_request_signals()

    def check_manual_request_success(self, client_id: int) -> bool:
        """Check if the last manual request for a client was successful (received grant)"""
        try:
            return self._check_grant_signal(client_id)
        except:
            return False

    def get_stats(self) -> Dict:
        """Get current statistics - only difference is weight info"""
        base_stats = {
            'active': self.active,
            'num_clients': self.num_clients,
            'ack_mode': self.ack_mode,
            'is_weighted': self.is_weighted,
            'pending_acks': list(self.pending_acks),
            'current_ack_profile': self.current_ack_profile,
            'available_client_profiles': list(self.client_randomizers.keys()),
            'available_ack_profiles': list(self.ack_randomizers.keys()),
            'client_states': {i: self.client_states[i].value for i in range(self.num_clients)},
            'client_configs': {i: {
                'enabled': self.client_configs[i].enabled,
                'profile': self.client_configs[i].randomizer_profile
            } for i in range(self.num_clients)}
        }

        # Add weight-specific stats only if weighted
        if self.is_weighted:
            base_stats['current_weights'] = self.current_weights.copy()

        # Add manual ACK status if available
        if hasattr(self, '_manual_ack_config') and self._manual_ack_config:
            base_stats['manual_ack_configs'] = self._manual_ack_config.copy()

        return base_stats

    def get_manual_control_status(self):
        """Get status of all clients in manual control"""
        manual_clients = {}
        for client_id in range(self.num_clients):
            if self.client_states[client_id] == ClientState.MANUAL_CONTROL:
                manual_clients[client_id] = {
                    'state': self.client_states[client_id].value,
                    'enabled': self.client_configs[client_id].enabled,
                    'timer': self.client_timers[client_id]
                }
        return manual_clients

    def get_manual_ack_status(self, client_id: int = None):
        """Get status of manual ACK configuration"""
        if not hasattr(self, '_manual_ack_config'):
            return {} if client_id is None else None

        if client_id is not None:
            return self._manual_ack_config.get(client_id, None)
        else:
            return self._manual_ack_config.copy()

    def clear_manual_ack_config(self, client_id: int = None):
        """Clear manual ACK configuration"""
        if not hasattr(self, '_manual_ack_config'):
            return

        if client_id is not None:
            if client_id in self._manual_ack_config:
                del self._manual_ack_config[client_id]
                self.log.debug(f"ArbiterMaster({self.title}): Cleared manual ACK config for client {client_id}")
        else:
            self._manual_ack_config.clear()
            self.log.debug(f"ArbiterMaster({self.title}): Cleared all manual ACK configs")
