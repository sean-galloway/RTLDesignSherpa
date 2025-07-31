"""
Fixed Arbiter Master Driver with Correct FlexRandomizer Usage
Maintains all required randomization features while following the FlexRandomizer API correctly
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.clock import Clock
from cocotb.utils import get_sim_time

from dataclasses import dataclass
from typing import Dict, Optional, Set
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
    Fixed async arbiter master driver with correct FlexRandomizer usage
    Maintains all required randomization features
    """

    def __init__(self, dut, title, clock, num_clients: int, ack_mode: bool = True, log=None):
        self.dut = dut
        self.title = title
        self.clock = clock
        self.num_clients = num_clients
        self.ack_mode = ack_mode
        if log:
            self.log = log
        else:
            self.log = cocotb.log.getChild("ArbiterMaster")

        # Client management
        self.client_configs: Dict[int, ClientConfig] = {}
        self.client_timers: Dict[int, int] = {}
        self.client_states: Dict[int, ClientState] = {}

        # FIXED: Create separate FlexRandomizers for each profile
        self.client_randomizers: Dict[str, FlexRandomizer] = {}
        self.ack_randomizers: Dict[str, FlexRandomizer] = {}
        self.current_ack_profile = "immediate"

        # Setup default profiles using correct FlexRandomizer API
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
        """Setup default randomization profiles using correct FlexRandomizer API"""

        # FIXED: Create separate FlexRandomizer instances for each client profile
        # Each profile is its own FlexRandomizer with the correct constraint format

        # Default profile
        default_constraints = {
            'inter_request_delay': ([(5, 10), (15, 20)], [0.7, 0.3]),
            'request_duration': ([(1, 2), (3, 3)], [0.8, 0.2]),
            'enabled_probability': ([(1, 1)], [1.0])  # Always enabled
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

        # Disabled profile - always generates zero for enabled_probability
        disabled_constraints = {
            'inter_request_delay': ([(1000, 1000)], [1.0]),  # Very long delay
            'request_duration': ([(1, 1)], [1.0]),
            'enabled_probability': ([(0, 0)], [1.0])  # Never enabled
        }
        self.client_randomizers['disabled'] = FlexRandomizer(disabled_constraints)

        # Manual profile for walking tests - disabled by default
        manual_constraints = {
            'inter_request_delay': ([(1000, 1000)], [1.0]),  # Long delay - manual control takes over
            'request_duration': ([(1, 1)], [1.0]),           # Short duration by default
            'enabled_probability': ([(1, 1)], [1.0])         # ✅ ENABLED - manual control decides when to request
        }
        self.client_randomizers['manual'] = FlexRandomizer(manual_constraints)

        # FIXED: Create separate FlexRandomizer instances for ACK profiles

        # Immediate ACK (same cycle)
        immediate_ack_constraints = {
            'ack_delay': ([(0, 0)], [1.0]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['immediate'] = FlexRandomizer(immediate_ack_constraints)

        # Fast ACK with small delays
        fast_ack_constraints = {
            'ack_delay': ([(0, 0), (1, 2)], [0.7, 0.3]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['fast'] = FlexRandomizer(fast_ack_constraints)

        # Random ACK delays
        random_ack_constraints = {
            'ack_delay': ([(1, 2), (3, 5)], [0.6, 0.4]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['random'] = FlexRandomizer(random_ack_constraints)

        # Slow ACK for stress testing
        slow_ack_constraints = {
            'ack_delay': ([(5, 10), (10, 15)], [0.7, 0.3]),
            'ack_duration': ([(1, 1)], [1.0])
        }
        self.ack_randomizers['slow'] = FlexRandomizer(slow_ack_constraints)

    # =============================================================================
    # CONFIGURATION API - FIXED to use correct FlexRandomizer API
    # =============================================================================

    def set_client_profile(self, client_id: int, profile_name: str):
        """Set randomizer profile for specific client"""
        if client_id < self.num_clients and profile_name in self.client_randomizers:
            self.client_configs[client_id].randomizer_profile = profile_name
            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} profile set to '{profile_name}'")
        else:
            self.log.warning(f"ArbiterMaster({self.title}): Invalid profile '{profile_name}' or client {client_id}")

    def set_ack_profile(self, profile_name: str):
        """Set global ACK profile"""
        if profile_name in self.ack_randomizers:
            self.current_ack_profile = profile_name
            self.log.debug(f"ArbiterMaster({self.title}): ACK profile set to '{profile_name}'")
        else:
            self.log.warning(f"ArbiterMaster({self.title}): Invalid ACK profile '{profile_name}'")

    def enable_client(self, client_id: int):
        """Enable a client and start its countdown"""
        if client_id < self.num_clients:
            self.client_configs[client_id].enabled = True
            self._restart_client_countdown(client_id)
            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} enabled")

    def disable_client(self, client_id: int):
        """Disable a client and clear its request - FIXED VERSION"""
        if client_id < self.num_clients:
            self.client_configs[client_id].enabled = False
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0

            # FIXED: Use the new method to update all signals
            self._update_all_request_signals()

            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} disabled")

    def enable_clients(self, client_list):
        """Enable multiple clients"""
        for client_id in client_list:
            self.enable_client(client_id)

    def disable_clients(self, client_list):
        """Disable multiple clients"""
        for client_id in client_list:
            self.disable_client(client_id)

    def set_walking_mode(self, active_client: int, auto_ack: bool = None, ack_delay: int = None):
        """ENHANCED: Set up for walking test with automatic ACK support

        Args:
            active_client: Client to enable for walking test
            auto_ack: Enable automatic ACK for manual requests (default: use ACK mode setting)
            ack_delay: ACK delay in clocks 0-3 (default: random)
        """
        # Disable all clients first
        for client_id in range(self.num_clients):
            self.disable_client(client_id)
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0

        # Clear all request signals
        self._update_all_request_signals()

        # Clear any existing manual ACK configs
        self.clear_manual_ack_config()

        # Enable only the specified client with manual profile and auto-ACK
        if active_client < self.num_clients:
            self.client_configs[active_client].enabled = True
            self.client_configs[active_client].randomizer_profile = 'manual'

            # Set to IDLE state initially, manual control will override when needed
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

                self.log.info(f"ArbiterMaster({self.title}): Walking mode: client {active_client} ready with auto-ACK (delay={ack_delay})")
            else:
                self.log.info(f"ArbiterMaster({self.title}): Walking mode: client {active_client} ready for manual control (no auto-ACK)")
        else:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client {active_client} for walking mode")

    # ADDITIONAL METHOD: For debugging walking tests
    def force_client_request(self, client_id: int, enable: bool = True, auto_ack: bool = None, ack_delay: int = None):
        """ENHANCED: Force a client request signal with automatic ACK support

        Args:
            client_id: Client to control
            enable: True to assert request, False to clear
            auto_ack: If True, automatically ACK grants. If None, use current ACK mode setting
            ack_delay: Delay in clocks before ACK (0-3). If None, random 0-3
        """
        if client_id >= self.num_clients:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client_id {client_id}")
            return

        self.log.debug(f"ArbiterMaster({self.title}): FORCE REQUEST - client_id={client_id} enable={enable} auto_ack={auto_ack} ack_delay={ack_delay}{self.get_time_ns_str()}")

        if enable:
            # Set to manual control state to bypass automatic state machine
            self.client_states[client_id] = ClientState.MANUAL_CONTROL
            self.client_timers[client_id] = 0  # Clear any timer

            # NEW: Set up automatic ACK if requested
            if auto_ack is True or (auto_ack is None and self.ack_mode):
                # Determine ACK delay
                if ack_delay is None:
                    import random
                    ack_delay = random.randint(0, 3)  # Random 0-3 clocks
                else:
                    ack_delay = max(0, min(3, int(ack_delay)))  # Clamp to 0-3

                # Store manual ACK configuration
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
                # Clear any existing manual ACK config
                if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                    del self._manual_ack_config[client_id]

                self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} set to MANUAL_CONTROL state (no auto-ACK)")

        else:
            # Return to IDLE state and clear manual ACK config
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0

            if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                del self._manual_ack_config[client_id]

            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} set to IDLE state (manual control cleared)")

        # Update signals immediately
        self._update_all_request_signals()


    def update_request_profiles(self, new_profiles: Dict):
        """FIXED: Update request randomizer profiles using correct API with robust error handling"""
        for profile_name, constraints in new_profiles.items():
            try:
                self.log.debug(f"ArbiterMaster({self.title}): Adding profile '{profile_name}' with constraints: {constraints}")

                # FIXED: Convert the profile format to FlexRandomizer constraints
                flex_constraints = self._convert_profile_to_constraints(constraints)
                self.log.debug(f"ArbiterMaster({self.title}): Converted constraints for '{profile_name}': {flex_constraints}")

                # Validate that we have the required fields
                required_fields = ['inter_request_delay', 'request_duration', 'enabled_probability']
                for field in required_fields:
                    if field not in flex_constraints:
                        self.log.error(f"ArbiterMaster({self.title}): Profile '{profile_name}' missing required field: {field}")
                        continue

                # Create the FlexRandomizer
                self.client_randomizers[profile_name] = FlexRandomizer(flex_constraints)
                self.log.info(f"ArbiterMaster({self.title}): Successfully added request profile '{profile_name}'")

                # Test the randomizer to make sure it works
                test_randomizer = self.client_randomizers[profile_name]
                test_values = test_randomizer.next()
                self.log.debug(f"ArbiterMaster({self.title}): Test generation for '{profile_name}': {test_values}")

            except Exception as e:
                self.log.error(f"ArbiterMaster({self.title}): Failed to add profile '{profile_name}': {e}")
                import traceback
                self.log.error(f"ArbiterMaster({self.title}): Traceback: {traceback.format_exc()}")

    def update_ack_profiles(self, new_profiles: Dict):
        """FIXED: Update ACK randomizer profiles using correct API"""
        for profile_name, constraints in new_profiles.items():
            try:
                # Convert the profile format to FlexRandomizer constraints
                flex_constraints = self._convert_profile_to_constraints(constraints)
                self.ack_randomizers[profile_name] = FlexRandomizer(flex_constraints)
                self.log.debug(f"ArbiterMaster({self.title}): Added ACK profile '{profile_name}'")
            except Exception as e:
                self.log.error(f"ArbiterMaster({self.title}): Failed to add ACK profile '{profile_name}': {e}")

    def _update_all_request_signals(self):
        """FIXED: Update the entire request vector based on current client states"""
        request_vector = 0
        for client_id in range(self.num_clients):
            # CRITICAL FIX: Include MANUAL_CONTROL state in request generation
            if (self.client_states[client_id] == ClientState.REQUESTING or
                self.client_states[client_id] == ClientState.WAITING_ACK or
                self.client_states[client_id] == ClientState.MANUAL_CONTROL):  # NEW
                request_vector |= (1 << client_id)

        try:
            # Support both vector and individual signals
            if hasattr(self.dut, 'request'):
                # Vector signal - drive the complete vector
                self.dut.request.value = request_vector
                self.log.debug(f"ArbiterMaster({self.title}): Updated request vector to 0x{request_vector:x}")
            else:
                # Individual signals - drive each one
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
        """FIXED: Convert profile dictionary to FlexRandomizer constraint format with robust validation"""
        constraints = {}

        self.log.debug(f"ArbiterMaster({self.title}): Converting profile dict: {profile_dict}")

        for param_name, param_config in profile_dict.items():
            self.log.debug(f"ArbiterMaster({self.title}): Processing parameter '{param_name}': {param_config}")

            if isinstance(param_config, tuple) and len(param_config) == 2:
                # Already in correct format (bins, weights)
                bins, weights = param_config

                # Validate bins and weights
                if not isinstance(bins, list) or not isinstance(weights, list):
                    self.log.error(f"ArbiterMaster({self.title}): Invalid bins/weights format for {param_name}: bins={bins}, weights={weights}")
                    continue

                if len(bins) != len(weights):
                    self.log.error(f"ArbiterMaster({self.title}): Bins/weights length mismatch for {param_name}: {len(bins)} vs {len(weights)}")
                    continue

                constraints[param_name] = param_config
                self.log.debug(f"ArbiterMaster({self.title}): Used existing format for {param_name}: {param_config}")

            elif isinstance(param_config, list):
                # Convert list to single bin with equal weights
                if len(param_config) == 0:
                    self.log.warning(f"ArbiterMaster({self.title}): Empty list for parameter {param_name}, skipping")
                    continue

                # FIXED: Create bins from consecutive values - handle both single values and ranges
                bins = []
                for val in param_config:
                    if isinstance(val, (int, float)):
                        # Single value - create a range [val, val]
                        bins.append((int(val), int(val)))
                    elif isinstance(val, (tuple, list)) and len(val) == 2:
                        # Already a range
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

    # =============================================================================
    # INTERNAL METHODS - FIXED to use correct FlexRandomizer API
    # =============================================================================

    def _restart_client_countdown(self, client_id: int):
        """FIXED: Start new countdown for client - but only if not in manual control"""
        config = self.client_configs[client_id]

        # CRITICAL FIX: Don't restart countdown for clients in manual control
        if self.client_states[client_id] == ClientState.MANUAL_CONTROL:
            self.log.debug(f"ArbiterMaster({self.title}): Skipping countdown restart for client {client_id} - in manual control")
            return

        self.log.debug(f"ArbiterMaster({self.title}): _restart_client_countdown: client_id={client_id}, enabled={config.enabled}, profile={config.randomizer_profile}")

        if config.enabled:
            # ... rest of existing countdown logic ...
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
            # Support multiple grant signal formats
            if hasattr(self.dut, 'grant_valid') and hasattr(self.dut, 'grant_id'):
                # grant_valid + grant_id interface
                grant_valid = int(self.dut.grant_valid.value) if self.dut.grant_valid.value.is_resolvable else 0
                if grant_valid:
                    grant_id = int(self.dut.grant_id.value) if self.dut.grant_id.value.is_resolvable else -1
                    return grant_id == client_id
            elif hasattr(self.dut, 'grant'):
                # Vector grant signal
                grant_val = int(self.dut.grant.value) if self.dut.grant.value.is_resolvable else 0
                return bool(grant_val & (1 << client_id))
            else:
                # Individual grant signals
                grant_signal = getattr(self.dut, f'grant_{client_id}', None)
                if grant_signal is None:
                    grant_signal = getattr(self.dut, f'gnt_{client_id}', None)
                if grant_signal is not None:
                    return bool(int(grant_signal.value))
        except Exception as e:
            self.log.warning(f"ArbiterMaster({self.title}): Could not read grant signal for client {client_id}: {e}")

        return False

    def _set_ack_signal(self, client_id: int, value: int):
        """Set ACK signal for client - FIXED to not call _set_request_signal"""
        if not self.ack_mode:
            return

        try:
            # Support both vector and individual ACK signals
            if hasattr(self.dut, 'grant_ack'):
                # Vector ACK signal
                current_val = int(self.dut.grant_ack.value) if self.dut.grant_ack.value.is_resolvable else 0
                if value:
                    new_val = current_val | (1 << client_id)
                else:
                    new_val = current_val & ~(1 << client_id)
                self.dut.grant_ack.value = new_val
            else:
                # Individual ACK signals
                ack_signal = getattr(self.dut, f'ack_{client_id}', None)
                if ack_signal is None:
                    ack_signal = getattr(self.dut, f'grant_ack_{client_id}', None)
                if ack_signal is not None:
                    ack_signal.value = value
        except Exception as e:
            self.log.warning(f"ArbiterMaster({self.title}): Could not set ACK signal for client {client_id}: {e}")

    # =============================================================================
    # ASYNC BACKGROUND PROCESSES - FIXED to use correct FlexRandomizer API
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

        self.log.info("ArbiterMaster started")

    async def shutdown(self):
        """ENHANCED: Clean shutdown of arbiter master including manual ACK cleanup"""
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

        self.log.info(f"ArbiterMaster stopped{self.get_time_ns_str()}")

    async def reset_signals(self):
        """Reset all signals and state - FIXED VERSION"""
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

        # FIXED: Clear all request signals using the new method
        self._update_all_request_signals()

        # Clear ACK signals if needed
        if self.ack_mode:
            if hasattr(self.dut, 'grant_ack'):
                self.dut.grant_ack.value = 0
            else:
                # Individual ACK signals
                for client_id in range(self.num_clients):
                    ack_signal = getattr(self.dut, f'ack_{client_id}', None)
                    if ack_signal is None:
                        ack_signal = getattr(self.dut, f'grant_ack_{client_id}', None)
                    if ack_signal is not None:
                        ack_signal.value = 0

    async def _request_generator(self):
        """FIXED: Generate requests based on correct FlexRandomizer usage - SKIP MANUAL_CONTROL clients"""
        while self.active:
            await RisingEdge(self.clock)

            for client_id in range(self.num_clients):
                config = self.client_configs[client_id]
                state = self.client_states[client_id]

                # CRITICAL FIX: Skip clients in MANUAL_CONTROL state
                if state == ClientState.MANUAL_CONTROL:
                    continue  # Don't interfere with manual control

                # Skip disabled clients
                if not config.enabled:
                    continue

                # Update client state machine for automatic clients only
                if state == ClientState.COUNTING:
                    self.client_timers[client_id] -= 1
                    if self.client_timers[client_id] <= 0:
                        # Get request duration from correct randomizer
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
                        # Request duration expired, but no grant yet
                        if not self.ack_mode:
                            # In no-ACK mode, restart immediately
                            self._restart_client_countdown(client_id)

            # Update ALL request signals once per clock cycle
            self._update_all_request_signals()

    async def _grant_monitor(self):
        """ENHANCED: Monitor grants and handle ACK generation including manual control auto-ACK"""
        while self.active:
            await RisingEdge(self.clock)

            for client_id in range(self.num_clients):
                state = self.client_states[client_id]

                # Check for new grant - include MANUAL_CONTROL state
                if (self._check_grant_signal(client_id) and
                    (state == ClientState.REQUESTING or state == ClientState.MANUAL_CONTROL)):

                    if self.ack_mode:
                        # Check if this is manual control with auto-ACK
                        if (state == ClientState.MANUAL_CONTROL and
                            hasattr(self, '_manual_ack_config') and
                            client_id in self._manual_ack_config):

                            config = self._manual_ack_config[client_id]
                            if config['enabled'] and not config['ack_pending']:
                                # Start manual auto-ACK process
                                config['ack_pending'] = True
                                config['grant_detected'] = True
                                cocotb.start_soon(self._generate_manual_ack(client_id))
                                self.log.debug(f"ArbiterMaster({self.title}): Started manual auto-ACK for client {client_id}")
                        else:
                            # Normal ACK mode processing
                            self.client_states[client_id] = ClientState.WAITING_ACK
                            if client_id not in self.pending_acks:
                                self.pending_acks.add(client_id)
                                cocotb.start_soon(self._generate_ack(client_id))
                    else:
                        # No-ACK mode: completion handling
                        if state == ClientState.MANUAL_CONTROL:
                            # For manual control, just log the grant but stay in manual control
                            self.log.debug(f"ArbiterMaster({self.title}): Manual client {client_id} received grant, staying in manual control")
                        else:
                            # For automatic clients, restart countdown
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

            # Wait for specified delay
            if delay_cycles > 0:
                await ClockCycles(self.clock, delay_cycles)

            # Assert ACK if still active and grant still present
            if (self.active and
                config['grant_detected'] and
                self._check_grant_signal(client_id)):

                self._set_ack_signal(client_id, 1)
                self.log.info(f"ArbiterMaster({self.title}): Client {client_id} manual ACK asserted (delay={delay_cycles} cycles){self.get_time_ns_str()}")

                # Hold ACK for one cycle
                await ClockCycles(self.clock, 1)
                self._set_ack_signal(client_id, 0)

                self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} manual ACK completed{self.get_time_ns_str()}")
            else:
                self.log.warning(f"ArbiterMaster({self.title}): Manual ACK for client {client_id} cancelled - grant no longer present")

            # Clean up manual ACK config
            config['ack_pending'] = False
            config['grant_detected'] = False

        except Exception as e:
            self.log.error(f"ArbiterMaster({self.title}): Manual ACK generation error for client {client_id}: {e}{self.get_time_ns_str()}")

            # Cleanup on error
            if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                self._manual_ack_config[client_id]['ack_pending'] = False
                self._manual_ack_config[client_id]['grant_detected'] = False

    async def _generate_ack(self, client_id: int):
        """Generate ACK signal with correct FlexRandomizer timing"""
        try:
            # FIXED: Get ACK timing from correct randomizer
            if self.current_ack_profile in self.ack_randomizers:
                ack_randomizer = self.ack_randomizers[self.current_ack_profile]
                params = ack_randomizer.next()
                delay_cycles = params.get('ack_delay', 0)
                duration_cycles = params.get('ack_duration', 1)

                # Wait for delay if not immediate
                if delay_cycles > 0:
                    await ClockCycles(self.clock, delay_cycles)

                # Assert ACK
                if self.active and client_id in self.pending_acks:
                    self._set_ack_signal(client_id, 1)
                    self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} ACK asserted (delay={delay_cycles}, profile={self.current_ack_profile}){self.get_time_ns_str()}")

                    # Hold ACK for specified duration
                    await ClockCycles(self.clock, duration_cycles)
                    self._set_ack_signal(client_id, 0)

                    # Complete transaction
                    self.pending_acks.discard(client_id)
                    self._restart_client_countdown(client_id)
                    self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} transaction complete{self.get_time_ns_str()}")
            else:
                self.log.error(f"ArbiterMaster({self.title}): Unknown ACK profile: {self.current_ack_profile}{self.get_time_ns_str()}")

        except Exception as e:
            self.log.error(f"ArbiterMaster({self.title}): ACK generation error for client {client_id}: {e}{self.get_time_ns_str()}")
            # Cleanup on error
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
        """FIXED: Manually assert request for specified cycles with automatic ACK support"""
        if client_id >= self.num_clients:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client_id {client_id} for manual request")
            return

        self.log.debug(f"ArbiterMaster({self.title}): Manual Request - client_id={client_id} cycles={cycles} auto_ack={auto_ack} ack_delay={ack_delay}{self.get_time_ns_str()}")

        # Store original state for restoration
        original_state = self.client_states[client_id]
        original_timer = self.client_timers[client_id]

        # Set up manual control with automatic ACK
        self.force_client_request(client_id, enable=True, auto_ack=auto_ack, ack_delay=ack_delay)

        # Wait for the specified cycles while monitoring
        grant_received = False
        for cycle in range(cycles):
            await RisingEdge(self.clock)

            # Check if grant was received
            if self._check_grant_signal(client_id):
                grant_received = True
                self.log.debug(f"ArbiterMaster({self.title}): Manual request for client {client_id} received grant at cycle {cycle}")

                # Mark grant detected for auto-ACK processing
                if hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
                    self._manual_ack_config[client_id]['grant_detected'] = True

                break

        # FIXED: Don't clear the request immediately if we have auto-ACK enabled
        # Let the grant monitor handle the ACK first
        if grant_received and hasattr(self, '_manual_ack_config') and client_id in self._manual_ack_config:
            config = self._manual_ack_config[client_id]
            if config['enabled']:
                self.log.debug(f"ArbiterMaster({self.title}): Grant received for client {client_id}, waiting for auto-ACK to complete")

                # Just clear the request signal but keep the ACK config
                self.client_states[client_id] = ClientState.MANUAL_CONTROL  # Keep in manual control
                self._update_all_request_signals()  # This will clear the request since not REQUESTING state

                # Wait for ACK to complete
                ack_delay_cycles = config['delay_clocks']
                total_wait = ack_delay_cycles + 5  # ACK delay + ACK duration + margin
                await ClockCycles(self.clock, total_wait)

                # Now clean up
                if client_id in self._manual_ack_config:
                    del self._manual_ack_config[client_id]

                self.log.debug(f"ArbiterMaster({self.title}): Manual request completed for client {client_id}, auto-ACK should be done")
            else:
                # No auto-ACK, clear immediately
                self.force_client_request(client_id, enable=False)
        else:
            # No grant received or no auto-ACK, clear immediately
            self.force_client_request(client_id, enable=False)
            self.log.debug(f"ArbiterMaster({self.title}): Manual request ended for client {client_id}, grant_received={grant_received}")

        # Restore to IDLE state
        self.client_states[client_id] = ClientState.IDLE
        self.client_timers[client_id] = 0
        self._update_all_request_signals()

    # ADDITIONAL FIX: Add a method to check if manual request was successful
    def check_manual_request_success(self, client_id: int) -> bool:
        """Check if the last manual request for a client was successful (received grant)"""
        try:
            return self._check_grant_signal(client_id)
        except:
            return False

    def get_stats(self) -> Dict:
        """ENHANCED: Get current statistics including manual ACK status"""
        base_stats = {
            'active': self.active,
            'num_clients': self.num_clients,
            'ack_mode': self.ack_mode,
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

        # Add manual ACK status if available
        if hasattr(self, '_manual_ack_config') and self._manual_ack_config:
            base_stats['manual_ack_configs'] = self._manual_ack_config.copy()

        return base_stats

    # Add debug method for checking manual control status
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
        """Get status of manual ACK configuration

        Args:
            client_id: If specified, get status for specific client. If None, get all clients.

        Returns:
            Dictionary with manual ACK status
        """
        if not hasattr(self, '_manual_ack_config'):
            return {} if client_id is None else None

        if client_id is not None:
            return self._manual_ack_config.get(client_id, None)
        else:
            return self._manual_ack_config.copy()

    def clear_manual_ack_config(self, client_id: int = None):
        """Clear manual ACK configuration

        Args:
            client_id: If specified, clear config for specific client. If None, clear all.
        """
        if not hasattr(self, '_manual_ack_config'):
            return

        if client_id is not None:
            if client_id in self._manual_ack_config:
                del self._manual_ack_config[client_id]
                self.log.debug(f"ArbiterMaster({self.title}): Cleared manual ACK config for client {client_id}")
        else:
            self._manual_ack_config.clear()
            self.log.debug(f"ArbiterMaster({self.title}): Cleared all manual ACK configs")

