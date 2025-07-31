"""
Unified Arbiter Master Driver supporting both weighted and non-weighted arbiters
Maintains all existing functionality while adding weight support based on parameters
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
    Unified async arbiter master driver supporting both weighted and non-weighted arbiters
    Automatically adapts to weighted mode based on is_weighted parameter
    """

    def __init__(self, dut, title, clock, num_clients: int, ack_mode: bool = True, 
                 is_weighted: bool = False, log=None):
        self.dut = dut
        self.title = title
        self.clock = clock
        self.num_clients = num_clients
        self.ack_mode = ack_mode
        self.is_weighted = is_weighted  # NEW: Support weighted arbiters
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

        # NEW: Weight management for weighted arbiters
        self.weight_randomizers: Dict[str, FlexRandomizer] = {}
        self.current_weight_profile = "static"
        self.current_weights = [1] * num_clients  # Default equal weights
        self.weight_change_pending = False

        # Setup default profiles using correct FlexRandomizer API
        self._setup_default_profiles()

        # Tracking
        self.pending_acks: Set[int] = set()
        self.active = False

        # Tasks
        self._request_task = None
        self._grant_task = None
        self._weight_task = None  # NEW: Weight management task

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
        """Setup default randomization profiles for both client requests and weights"""

        # === CLIENT REQUEST PROFILES (existing) ===
        
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

        # === ACK PROFILES (existing) ===
        
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

        # === WEIGHT PROFILES (NEW: only used if is_weighted=True) ===
        if self.is_weighted:
            self._setup_weight_profiles()

    def _setup_weight_profiles(self):
        """Setup weight randomization profiles for weighted arbiters"""
        
        # Static weights - no changes
        static_constraints = {
            'weight_change_interval': ([(10000, 10000)], [1.0]),  # Very long interval = no changes
            'weight_hold_duration': ([(1000, 1000)], [1.0])
        }
        self.weight_randomizers['static'] = FlexRandomizer(static_constraints)

        # Slow weight changes
        slow_weight_constraints = {
            'weight_change_interval': ([(2000, 5000)], [1.0]),
            'weight_hold_duration': ([(100, 200)], [1.0])
        }
        self.weight_randomizers['slow_changes'] = FlexRandomizer(slow_weight_constraints)

        # Fast weight changes
        fast_weight_constraints = {
            'weight_change_interval': ([(500, 1000)], [1.0]),
            'weight_hold_duration': ([(50, 100)], [1.0])
        }
        self.weight_randomizers['fast_changes'] = FlexRandomizer(fast_weight_constraints)

        # Rapid weight changes (stress test)
        rapid_weight_constraints = {
            'weight_change_interval': ([(100, 300)], [1.0]),
            'weight_hold_duration': ([(20, 50)], [1.0])
        }
        self.weight_randomizers['rapid_changes'] = FlexRandomizer(rapid_weight_constraints)

    # =============================================================================
    # CONFIGURATION API - Extended for weight support
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

    def set_weight_profile(self, profile_name: str):
        """NEW: Set weight randomization profile (only for weighted arbiters)"""
        if not self.is_weighted:
            self.log.warning(f"ArbiterMaster({self.title}): Weight profile ignored - not a weighted arbiter")
            return
            
        if profile_name in self.weight_randomizers:
            self.current_weight_profile = profile_name
            self.log.debug(f"ArbiterMaster({self.title}): Weight profile set to '{profile_name}'")
        else:
            self.log.warning(f"ArbiterMaster({self.title}): Invalid weight profile '{profile_name}'")

    def set_static_weights(self, weights: List[int]):
        """NEW: Set static weights for weighted arbiters"""
        if not self.is_weighted:
            self.log.warning(f"ArbiterMaster({self.title}): Static weights ignored - not a weighted arbiter")
            return
            
        if len(weights) != self.num_clients:
            self.log.error(f"ArbiterMaster({self.title}): Weight list length ({len(weights)}) != num_clients ({self.num_clients})")
            return
            
        if any(w < 0 for w in weights):
            self.log.error(f"ArbiterMaster({self.title}): All weights must be >= 0")
            return
            
        self.current_weights = weights.copy()
        self._apply_weights_to_dut()
        self.log.info(f"ArbiterMaster({self.title}): Static weights set to {weights}")

    def get_current_weights(self) -> List[int]:
        """NEW: Get current weight configuration"""
        return self.current_weights.copy() if self.is_weighted else []

    def trigger_weight_change(self, new_weights: List[int], delay_cycles: int = 0):
        """NEW: Trigger a specific weight change after delay"""
        if not self.is_weighted:
            self.log.warning(f"ArbiterMaster({self.title}): Weight change ignored - not a weighted arbiter")
            return
            
        if len(new_weights) != self.num_clients:
            self.log.error(f"ArbiterMaster({self.title}): New weight list length mismatch")
            return
            
        # Schedule weight change
        cocotb.start_soon(self._scheduled_weight_change(new_weights, delay_cycles))
        self.log.info(f"ArbiterMaster({self.title}): Weight change scheduled: {new_weights} in {delay_cycles} cycles")

    # Existing methods remain unchanged
    def enable_client(self, client_id: int):
        """Enable a client and start its countdown"""
        if client_id < self.num_clients:
            self.client_configs[client_id].enabled = True
            self._restart_client_countdown(client_id)
            self.log.debug(f"ArbiterMaster({self.title}): Client {client_id} enabled")

    def disable_client(self, client_id: int):
        """Disable a client and clear its request"""
        if client_id < self.num_clients:
            self.client_configs[client_id].enabled = False
            self.client_states[client_id] = ClientState.IDLE
            self.client_timers[client_id] = 0
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

                self.log.info(f"ArbiterMaster({self.title}): Walking mode: client {active_client} ready with auto-ACK (delay={ack_delay})")
            else:
                self.log.info(f"ArbiterMaster({self.title}): Walking mode: client {active_client} ready for manual control (no auto-ACK)")
        else:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client {active_client} for walking mode")

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

    def update_weight_profiles(self, new_profiles: Dict):
        """NEW: Update weight randomizer profiles (only for weighted arbiters)"""
        if not self.is_weighted:
            self.log.warning(f"ArbiterMaster({self.title}): Weight profiles ignored - not a weighted arbiter")
            return
            
        for profile_name, constraints in new_profiles.items():
            try:
                flex_constraints = self._convert_profile_to_constraints(constraints)
                self.weight_randomizers[profile_name] = FlexRandomizer(flex_constraints)
                self.log.debug(f"ArbiterMaster({self.title}): Added weight profile '{profile_name}'")
            except Exception as e:
                self.log.error(f"ArbiterMaster({self.title}): Failed to add weight profile '{profile_name}': {e}")

    # =============================================================================
    # INTERNAL METHODS - Extended for weight support
    # =============================================================================

    def _apply_weights_to_dut(self):
        """NEW: Apply current weights to DUT max_thresh signal"""
        if not self.is_weighted:
            return
            
        try:
            if hasattr(self.dut, 'max_thresh'):
                # Pack weights into max_thresh signal based on arbiter's width requirements
                # Assuming each weight is MAX_LEVELS_WIDTH bits
                packed_weights = 0
                max_levels_width = getattr(self.dut, 'MAX_LEVELS_WIDTH', 4)  # Default 4 bits per weight
                
                for i, weight in enumerate(self.current_weights):
                    # Clamp weight to fit in allocated bits
                    max_weight = (1 << max_levels_width) - 1
                    clamped_weight = min(weight, max_weight)
                    packed_weights |= (clamped_weight << (i * max_levels_width))
                
                self.dut.max_thresh.value = packed_weights
                self.log.debug(f"ArbiterMaster({self.title}): Applied weights {self.current_weights} as 0x{packed_weights:x}")
            else:
                self.log.warning(f"ArbiterMaster({self.title}): max_thresh signal not found - cannot apply weights")
        except Exception as e:
            self.log.error(f"ArbiterMaster({self.title}): Error applying weights: {e}")

    async def _scheduled_weight_change(self, new_weights: List[int], delay_cycles: int):
        """NEW: Execute scheduled weight change after delay"""
        if delay_cycles > 0:
            await ClockCycles(self.clock, delay_cycles)
            
        old_weights = self.current_weights.copy()
        self.current_weights = new_weights.copy()
        self._apply_weights_to_dut()
        
        self.log.info(f"ArbiterMaster({self.title}): Weight change executed: {old_weights} -> {new_weights}{self.get_time_ns_str()}")

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
                self.log.debug(f"ArbiterMaster({self.title}): Updated request vector to 0x{request_vector:x}")
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
    # ASYNC BACKGROUND PROCESSES - Extended for weight support
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
        
        # NEW: Start weight management task for weighted arbiters
        if self.is_weighted:
            self._weight_task = cocotb.start_soon(self._weight_manager())

        self.log.info(f"ArbiterMaster started (weighted: {self.is_weighted})")

    async def shutdown(self):
        """Clean shutdown of arbiter master including weight management cleanup"""
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
        if self._weight_task and not self._weight_task.done():  # NEW
            self._weight_task.cancel()

        # Clear all signals
        await self.reset_signals()

        self.log.info(f"ArbiterMaster stopped{self.get_time_ns_str()}")

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

        # NEW: Apply initial weights for weighted arbiters
        if self.is_weighted:
            self._apply_weights_to_dut()

    async def _request_generator(self):
        """Generate requests based on correct FlexRandomizer usage - SKIP MANUAL_CONTROL clients"""
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
        """Monitor grants and handle ACK generation including manual control auto-ACK"""
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

    async def _weight_manager(self):
        """NEW: Background weight management for weighted arbiters"""
        if not self.is_weighted:
            return
            
        weight_timer = 0
        
        while self.active:
            await RisingEdge(self.clock)
            
            # Check if we should trigger weight changes based on current profile
            if self.current_weight_profile in self.weight_randomizers:
                if weight_timer <= 0:
                    # Generate next weight change timing
                    randomizer = self.weight_randomizers[self.current_weight_profile]
                    params = randomizer.next()
                    weight_timer = params.get('weight_change_interval', 10000)
                    
                    # Only trigger changes for non-static profiles
                    if self.current_weight_profile != 'static' and not self.weight_change_pending:
                        self._trigger_random_weight_change()
                else:
                    weight_timer -= 1

    def _trigger_random_weight_change(self):
        """NEW: Trigger a random weight change based on current configuration"""
        # Generate new random weights
        import random
        max_weight = 8  # Reasonable maximum
        new_weights = [random.randint(1, max_weight) for _ in range(self.num_clients)]
        
        # Schedule the change with small delay to avoid race conditions
        delay_cycles = random.randint(5, 20)
        cocotb.start_soon(self._scheduled_weight_change(new_weights, delay_cycles))
        
        self.weight_change_pending = True
        cocotb.start_soon(self._clear_weight_change_pending(delay_cycles + 10))

    async def _clear_weight_change_pending(self, delay_cycles: int):
        """NEW: Clear weight change pending flag after delay"""
        await ClockCycles(self.clock, delay_cycles)
        self.weight_change_pending = False

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
    # TEST UTILITY METHODS - Extended for weight support
    # =============================================================================

    async def wait_for_grant(self, client_id: int, timeout_cycles: int = 100) -> bool:
        """Wait for grant signal for specific client"""
        for _ in range(timeout_cycles):
            if self._check_grant_signal(client_id):
                return True
            await RisingEdge(self.clock)
        return False

    async def manual_request(self, client_id: int, cycles: int = 1, auto_ack: bool = None, ack_delay: int = None):
        """Manually assert request for specified cycles with automatic ACK support"""
        if client_id >= self.num_clients:
            self.log.error(f"ArbiterMaster({self.title}): Invalid client_id {client_id} for manual request")
            return

        self.log.debug(f"ArbiterMaster({self.title}): Manual Request - client_id={client_id} cycles={cycles} auto_ack={auto_ack} ack_delay={ack_delay}{self.get_time_ns_str()}")

        original_state = self.client_states[client_id]
        original_timer = self.client_timers[client_id]

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
        """Get current statistics including weight status for weighted arbiters"""
        base_stats = {
            'active': self.active,
            'num_clients': self.num_clients,
            'ack_mode': self.ack_mode,
            'is_weighted': self.is_weighted,  # NEW
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

        # NEW: Add weight-specific stats
        if self.is_weighted:
            base_stats.update({
                'current_weights': self.current_weights.copy(),
                'current_weight_profile': self.current_weight_profile,
                'available_weight_profiles': list(self.weight_randomizers.keys()),
                'weight_change_pending': self.weight_change_pending
            })

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
