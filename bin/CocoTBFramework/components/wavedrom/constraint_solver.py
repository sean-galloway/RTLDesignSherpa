"""
Temporal Sequence Constraint Solver with Fixed Boundary Detection and Edge Nodes

Key fixes:
1. Improved boundary detection that properly flushes constraint windows
2. Fixed edge node application to signal objects
3. Better constraint isolation between transactions
"""

import cocotb
from typing import Dict, List, Optional, Any, Set, Union, Callable
from collections import deque
from dataclasses import dataclass, field
from enum import Enum
from cocotb.triggers import RisingEdge, FallingEdge, Timer

# Required imports - no conditionals
from ortools.sat.python import cp_model
from .wavejson_gen import WaveJSONGenerator, TemporalAnnotation, create_wavejson_from_packet
from ..field_config import FieldConfig, FieldDefinition


class ClockEdge(Enum):
    RISING = "rising"
    FALLING = "falling"


class TemporalRelation(Enum):
    """Temporal relationships between events"""
    CONCURRENT = "concurrent"      # Events happen at the same time
    BEFORE = "before"             # A happens before B
    AFTER = "after"               # A happens after B
    WITHIN = "within"             # A happens within N cycles of B
    SEQUENCE = "sequence"         # Events happen in order: A, then B, then C


@dataclass
class SignalTransition:
    """Defines a signal transition"""
    signal: str
    from_value: int
    to_value: int

    def __str__(self):
        return f"{self.signal}: {self.from_value}→{self.to_value}"


@dataclass
class SignalStatic:
    """Defines a static signal value"""
    signal: str
    value: int

    def __str__(self):
        return f"{self.signal}={self.value}"


@dataclass
class TemporalEvent:
    """Defines a temporal event (transition or static)"""
    name: str
    pattern: Union[SignalTransition, SignalStatic]
    timing_tolerance: int = 0  # Allow +/- N cycles variation

    def __str__(self):
        return f"{self.name}: {self.pattern}"


@dataclass
class TemporalConstraint:
    """Temporal constraint definition with FieldConfig integration"""
    name: str
    events: List[TemporalEvent] = field(default_factory=list)
    temporal_relation: TemporalRelation = TemporalRelation.SEQUENCE
    max_window_size: int = 20
    required: bool = True
    max_matches: int = 1
    clock_group: str = "default"
    signals_to_show: List[str] = field(default_factory=list)

    # Timing constraints
    min_sequence_duration: int = 1    # Minimum cycles for sequence
    max_sequence_duration: int = 15   # Maximum cycles for sequence

    # FieldConfig integration
    field_config: Optional[FieldConfig] = None
    protocol_hint: Optional[str] = None

    def __post_init__(self):
        if not self.signals_to_show:
            # Auto-extract signals from events
            signals = set()
            for event in self.events:
                signals.add(event.pattern.signal)
            self.signals_to_show = list(signals)


@dataclass
class ClockGroup:
    """Clock group definition with configuration"""
    name: str
    clock_signal: Any
    edge: ClockEdge = ClockEdge.RISING
    sample_delay_ns: float = 1.0
    field_config: Optional[FieldConfig] = None  # Protocol-specific configuration


@dataclass
class SolutionResult:
    """Result from constraint solving with modular WaveJSON"""
    constraint_name: str
    filename: str
    window_data: Dict[str, List[int]]
    wavejson: Dict[str, Any]
    temporal_solution: Dict[str, Any]

    # Features
    field_config: Optional[FieldConfig] = None
    protocol_hint: Optional[str] = None
    wavejson_generator: Optional[WaveJSONGenerator] = None


class TemporalSolutionCollector(cp_model.CpSolverSolutionCallback):
    """Collects temporal solutions from CP-SAT solver"""

    def __init__(self, constraint_name: str, event_cycle_vars: Dict[str, Any]):
        cp_model.CpSolverSolutionCallback.__init__(self)
        self.constraint_name = constraint_name
        self.event_cycle_vars = event_cycle_vars
        self.solutions = []
        self.solution_count = 0

    def on_solution_callback(self):
        """Called when CP-SAT finds a solution"""
        self.solution_count += 1

        # Extract when each event occurs
        event_timing = {}
        for event_name, cycle_var in self.event_cycle_vars.items():
            event_timing[event_name] = self.Value(cycle_var)

        solution = {
            "constraint_name": self.constraint_name,
            "event_timing": event_timing,
            "sequence_start": min(event_timing.values()),
            "sequence_end": max(event_timing.values()),
            "sequence_duration": max(event_timing.values()) - min(event_timing.values()) + 1,
            "solution_count": self.solution_count
        }

        self.solutions.append(solution)


class TemporalConstraintSolver:
    """
    Temporal constraint solver with fixed boundary detection and edge node handling.

    Key improvements:
    - Fixed boundary detection that properly isolates constraints
    - Corrected edge node application for WaveDrom rendering
    - Better constraint window management
    """

    def __init__(self, dut, log, debug_level: int = 1,
                 wavejson_generator: Optional[WaveJSONGenerator] = None,
                 default_field_config: Optional[FieldConfig] = None):
        self.dut = dut
        self.log = log
        self.debug_level = debug_level
        self.default_field_config = default_field_config

        # Modular WaveJSON generation
        self.wavejson_generator = wavejson_generator
        if not self.wavejson_generator:
            self.wavejson_generator = WaveJSONGenerator(
                debug_level=debug_level,
                default_field_config=default_field_config
            )

        # Clock groups with FieldConfig support
        self.clock_groups: Dict[str, ClockGroup] = {}
        self.clock_tasks: List = []
        self.is_sampling = False

        # Signal bindings with FieldConfig integration
        self.signal_bindings: Dict[str, Any] = {}
        self.signal_field_configs: Dict[str, FieldConfig] = {}

        # Temporal constraints with protocol awareness
        self.constraints: Dict[str, TemporalConstraint] = {}
        self.constraint_windows: Dict[str, Dict[str, deque]] = {}
        self.constraint_cycle_counters: Dict[str, int] = {}

        # Transaction boundary management
        self.boundary_constraints: Dict[str, List[Dict]] = {}
        self.auto_boundary_configs: Dict[str, Dict] = {}
        self.protocol_boundary_handlers: Dict[str, Callable] = {}

        # Solutions with modular features
        self.solutions: List[SolutionResult] = []
        self.satisfied_constraints: Set[str] = set()

        # Custom callbacks with packet integration
        self.wavejson_callbacks: Dict[str, Callable] = {}
        self.packet_based_callbacks: Dict[str, Callable] = {}

        # Boundary detection state
        self.last_signal_values: Dict[str, int] = {}
        self.protocol_states: Dict[str, Dict] = {}

        self.log.info("Temporal Constraint Solver initialized with modular architecture")

    def set_wavejson_generator(self, generator: WaveJSONGenerator):
        """Set custom WaveJSON generator"""
        self.wavejson_generator = generator
        if self.debug_level >= 1:
            self.log.info(f"Set custom WaveJSON generator: {generator.get_stats()}")

    def configure_protocol_field_config(self, protocol_name: str, field_config: FieldConfig):
        """Configure FieldConfig for a specific protocol"""
        # Store protocol-specific FieldConfig
        self.signal_field_configs[protocol_name] = field_config

        # Configure WaveJSON generator if available
        if self.wavejson_generator:
            self.wavejson_generator.set_protocol_config(protocol_name, field_config)

        self.log.info(f"Configured FieldConfig for {protocol_name}: {len(field_config.field_names())} fields")

    def add_wavejson_callback(self, constraint_name: str, callback: Callable):
        """
        Add custom WaveJSON generation callback for specific constraint.

        Args:
            constraint_name: Name of constraint
            callback: Function(constraint, signal_data, temporal_solution) -> wavejson_dict
        """
        self.wavejson_callbacks[constraint_name] = callback

    def add_packet_based_callback(self, constraint_name: str, packet_class, callback: Callable):
        """
        Add packet-based WaveJSON generation callback.

        Args:
            constraint_name: Name of constraint
            packet_class: Packet class (APBPacket, GAXIPacket, etc.)
            callback: Function(packet_obj, signal_data, temporal_solution) -> wavejson_dict
        """
        self.packet_based_callbacks[constraint_name] = (packet_class, callback)

    def add_clock_group(self, name: str, clock_signal: Any,
                       edge: ClockEdge = ClockEdge.RISING,
                       sample_delay_ns: float = 1.0,
                       field_config: Optional[FieldConfig] = None):
        """Add a clock group with optional FieldConfig"""
        clock_group = ClockGroup(name, clock_signal, edge, sample_delay_ns, field_config)
        self.clock_groups[name] = clock_group

        # Configure WaveJSON generator for this clock group if FieldConfig provided
        if field_config and self.wavejson_generator:
            self.wavejson_generator.configure_from_field_config(
                field_config,
                interface_prefix=name,
                protocol_name=name
            )

        self.log.info(f"Added clock group '{name}': {edge.value} + {sample_delay_ns}ns")

    def add_signal_binding(self, signal_name: str, dut_path: str, field_definition: Optional[FieldDefinition] = None):
        """Add signal binding with optional FieldDefinition"""
        try:
            dut_signal = getattr(self.dut, dut_path)
            self.signal_bindings[signal_name] = {
                "dut_signal": dut_signal,
                "dut_path": dut_path,
                "field_definition": field_definition
            }

            if self.debug_level >= 2:
                self.log.info(f"  Bound {signal_name} -> {dut_path}")

            # Configure WaveJSON generator
            if self.wavejson_generator:
                if field_definition:
                    # Create temporary FieldConfig for this signal
                    temp_config = FieldConfig()
                    temp_config.add_field(field_definition)
                    self.wavejson_generator.configure_from_field_config(temp_config)
                else:
                    # Fallback to auto-configuration
                    self.wavejson_generator.auto_configure_signals([signal_name])

        except Exception as e:
            self.log.error(f"Failed to bind {signal_name} -> {dut_path}: {e}")
            raise

    def add_interface(self, name: str, signal_map: Dict[str, str], field_config: Optional[FieldConfig] = None):
        """Add interface with FieldConfig integration"""
        signal_names = []

        for field_name, dut_path in signal_map.items():
            signal_name = f"{name}_{field_name}"

            # Get field definition if FieldConfig provided
            field_definition = None
            if field_config and field_config.has_field(field_name):
                field_definition = field_config.get_field(field_name)

            self.add_signal_binding(signal_name, dut_path, field_definition)
            signal_names.append(signal_name)

        # Configure WaveJSON generator
        if self.wavejson_generator:
            if field_config:
                # Configure using FieldConfig
                self.wavejson_generator.configure_from_field_config(
                    field_config,
                    interface_prefix=name,
                    protocol_name=name
                )
            else:
                # Fallback to interface group
                interface_title = f"{name.upper()} Interface"
                self.wavejson_generator.add_interface_group(interface_title, signal_names)

    def add_constraint(self, constraint: TemporalConstraint):
        """Add temporal constraint with FieldConfig integration"""
        self.constraints[constraint.name] = constraint
        self.constraint_windows[constraint.name] = {}
        self.constraint_cycle_counters[constraint.name] = 0

        # Initialize rolling windows for each signal
        for signal_name in self.signal_bindings.keys():
            self.constraint_windows[constraint.name][signal_name] = deque(maxlen=constraint.max_window_size)

        # Configure WaveJSON generator for this constraint's signals
        if self.wavejson_generator and constraint.field_config:
            protocol_hint = constraint.protocol_hint or constraint.name.split('_')[0]
            self.wavejson_generator.configure_from_field_config(
                constraint.field_config,
                protocol_name=protocol_hint
            )

        event_count = len(constraint.events)
        relation = constraint.temporal_relation.value
        self.log.info(f"Added constraint '{constraint.name}': {event_count} events, {relation}, window={constraint.max_window_size}")

        if self.debug_level >= 2:
            for event in constraint.events:
                self.log.info(f"  Event: {event}")

    def add_transaction_boundary(self, constraint_name: str, boundary_cycle: int, reset_signals=None):
        """Add transaction boundary constraint for a specific temporal constraint"""
        if constraint_name not in self.constraints:
            self.log.warning(f"Constraint '{constraint_name}' not found")
            return

        if reset_signals is None:
            reset_signals = self._get_default_boundary_signals()

        if constraint_name not in self.boundary_constraints:
            self.boundary_constraints[constraint_name] = []

        self.boundary_constraints[constraint_name].append({
            'cycle': boundary_cycle,
            'reset_signals': reset_signals
        })

        self.log.info(f"Added boundary at cycle {boundary_cycle} for constraint '{constraint_name}'")

    def auto_detect_boundaries(self, constraint_name: str, transition_signal: str,
                             transition_value=(1, 0), reset_signals=None):
        """Auto-boundary detection with protocol awareness"""
        if constraint_name not in self.constraints:
            self.log.warning(f"Constraint '{constraint_name}' not found")
            return []

        if transition_signal not in self.signal_bindings:
            self.log.warning(f"Signal '{transition_signal}' not bound")
            return []

        # Set reset signals with protocol awareness
        if reset_signals is None:
            reset_signals = self._get_boundary_signals(constraint_name)

        self.auto_boundary_configs[constraint_name] = {
            'transition_signal': transition_signal,
            'transition_value': transition_value,
            'reset_signals': reset_signals
        }

        self.log.info(f"Auto-boundary configured for '{constraint_name}': {transition_signal} {transition_value}")
        return []

    def _get_boundary_signals(self, constraint_name: str) -> Dict[str, int]:
        """Get boundary signals with protocol awareness"""
        constraint = self.constraints.get(constraint_name)
        protocol_hint = constraint.protocol_hint if constraint else None

        boundary_signals = {}

        # Protocol-specific boundary patterns
        if protocol_hint == "apb" or "apb" in constraint_name.lower():
            # APB-specific boundary signals
            apb_patterns = ['psel', 'penable', 'pready']
            for signal_name in self.signal_bindings.keys():
                signal_lower = signal_name.lower()
                for pattern in apb_patterns:
                    if pattern in signal_lower:
                        boundary_signals[signal_name] = 0
                        break

        elif protocol_hint == "axi" or "axi" in constraint_name.lower():
            # AXI-specific boundary signals
            axi_patterns = ['valid', 'ready']
            for signal_name in self.signal_bindings.keys():
                signal_lower = signal_name.lower()
                for pattern in axi_patterns:
                    if pattern in signal_lower:
                        boundary_signals[signal_name] = 0
                        break

        else:
            # Generic boundary detection
            boundary_signals = self._get_default_boundary_signals()

        return boundary_signals

    def _get_default_boundary_signals(self):
        """Auto-detect which signals to reset based on what's bound"""
        boundary_signals = {}

        control_patterns = [
            'psel', 'penable', 'pready',           # APB
            'valid', 'ready',                     # AXI/Generic handshake
            'awvalid', 'awready', 'wvalid', 'wready', 'bvalid', 'bready',  # AXI Write
            'arvalid', 'arready', 'rvalid', 'rready',                      # AXI Read
            'req', 'ack', 'gnt'                   # Generic request/grant
        ]

        for signal_name in self.signal_bindings.keys():
            signal_lower = signal_name.lower()
            for pattern in control_patterns:
                if pattern in signal_lower:
                    boundary_signals[signal_name] = 0
                    break

        return boundary_signals

    async def start_sampling(self):
        """Start sampling on all clock groups"""
        if not self.clock_groups:
            self.log.error("No clock groups defined!")
            return

        self.is_sampling = True

        for group_name, clock_group in self.clock_groups.items():
            task = cocotb.start_soon(self._sample_clock_group(clock_group))
            self.clock_tasks.append(task)

        self.log.info(f"Started temporal sampling on {len(self.clock_groups)} clock groups")

    async def stop_sampling(self):
        """Stop all sampling"""
        self.is_sampling = False

        for task in self.clock_tasks:
            if hasattr(task, 'kill'):
                task.kill()

        self.clock_tasks.clear()
        self.log.info("Stopped temporal sampling")

    async def _sample_clock_group(self, clock_group: ClockGroup):
        """Sample signals for one clock group"""
        try:
            while self.is_sampling:
                # Wait for clock edge
                if clock_group.edge == ClockEdge.RISING:
                    await RisingEdge(clock_group.clock_signal)
                else:
                    await FallingEdge(clock_group.clock_signal)

                # Wait for sample delay
                if clock_group.sample_delay_ns > 0:
                    await Timer(clock_group.sample_delay_ns, units='ns')

                # Sample signals with protocol awareness
                await self._sample_signals_for_clock_group(clock_group.name)

        except Exception as e:
            if self.debug_level >= 1:
                self.log.info(f"Temporal sampling stopped for {clock_group.name}: {e}")

    async def _sample_signals_for_clock_group(self, clock_group_name: str):
        """Signal sampling with improved boundary detection"""

        # Get current signal values
        current_values = {}
        for signal_name, binding in self.signal_bindings.items():
            try:
                current_values[signal_name] = self._get_signal_value(binding["dut_signal"])
            except Exception as e:
                if self.debug_level >= 2:
                    self.log.warning(f"Error sampling {signal_name}: {e}")
                current_values[signal_name] = 0

        # Update windows for constraints using this clock group
        for constraint_name, constraint in self.constraints.items():
            if constraint.clock_group != clock_group_name:
                continue

            # Skip if we already have enough matches
            current_matches = len([s for s in self.solutions if s.constraint_name == constraint_name])
            if current_matches >= constraint.max_matches:
                continue

            self.constraint_cycle_counters[constraint_name] += 1

            # Check if this constraint should skip boundary detection
            skip_boundaries = getattr(constraint, 'skip_boundary_detection', False)

            # FIXED: Check for boundary BEFORE adding to windows (only if not skipped)
            window_size = len(self.constraint_windows[constraint_name][list(self.constraint_windows[constraint_name].keys())[0]])
            boundary_detected = False

            if not skip_boundaries:
                boundary_detected = self._check_boundary(constraint_name, current_values, window_size)

                if boundary_detected and window_size >= 5:  # Minimum window for solving
                    if self.debug_level >= 1:
                        self.log.info(f"BOUNDARY DETECTED for {constraint_name} at window size {window_size} - solving before adding new data")
                    await self._solve_temporal_constraint(constraint_name, constraint)

                    # FIXED: Clear constraint windows after boundary detection
                    self._clear_constraint_windows(constraint_name)

                    if self.debug_level >= 2:
                        self.log.info(f"Cleared windows for {constraint_name} after boundary detection")

            # Add current values to rolling windows
            constraint_windows = self.constraint_windows[constraint_name]
            for signal_name, value in current_values.items():
                constraint_windows[signal_name].append(value)

            # Get updated window size
            window_size = len(constraint_windows[list(constraint_windows.keys())[0]])

            # Solve if window is full
            if window_size >= constraint.max_window_size:
                if self.debug_level >= 2:
                    self.log.info(f"Solving {constraint_name}: window full (window={window_size})")
                await self._solve_temporal_constraint(constraint_name, constraint)

        # Update last signal values for next boundary check
        self.last_signal_values.update(current_values)

    def _clear_constraint_windows(self, constraint_name: str):
        """Clear all windows for a specific constraint"""
        if constraint_name in self.constraint_windows:
            constraint = self.constraints[constraint_name]
            for signal_name in self.constraint_windows[constraint_name]:
                self.constraint_windows[constraint_name][signal_name] = deque(maxlen=constraint.max_window_size)

    def _check_boundary(self, constraint_name: str, current_values: Dict[str, int],
                                window_size: int) -> bool:
        """FIXED boundary detection with protocol awareness"""

        # Don't check boundaries if window is too small
        if window_size < 2:
            return False

        # Check auto-boundary detection
        if constraint_name in self.auto_boundary_configs:
            config = self.auto_boundary_configs[constraint_name]
            transition_signal = config['transition_signal']
            from_val, to_val = config['transition_value']

            if transition_signal in current_values:
                constraint_windows = self.constraint_windows[constraint_name]
                if transition_signal in constraint_windows:
                    signal_window = list(constraint_windows[transition_signal])
                    if len(signal_window) >= 2:
                        prev_val = signal_window[-2]
                        curr_val = current_values[transition_signal]

                        if prev_val == from_val and curr_val == to_val:
                            if self.debug_level >= 2:
                                self.log.info(f"Boundary detected for {constraint_name}: {transition_signal} {from_val}→{to_val}")
                            return True

        # Check manual boundaries
        if constraint_name in self.boundary_constraints:
            current_cycle = self.constraint_cycle_counters[constraint_name]
            for boundary in self.boundary_constraints[constraint_name]:
                if current_cycle == boundary['cycle']:
                    if self.debug_level >= 2:
                        self.log.info(f"Manual boundary detected for {constraint_name} at cycle {current_cycle}")
                    return True

        # Protocol-specific boundary patterns
        boundary_detected = self._check_protocol_boundaries(constraint_name, current_values, window_size)

        return boundary_detected

    def _check_protocol_boundaries(self, constraint_name: str, current_values: Dict[str, int],
                                          window_size: int) -> bool:
        """Protocol-specific boundary detection"""

        constraint = self.constraints.get(constraint_name)
        protocol_hint = constraint.protocol_hint if constraint else None

        # APB boundary detection
        if protocol_hint == "apb" or "apb" in constraint_name.lower():
            return self._check_apb_boundaries(constraint_name, current_values, window_size)

        # AXI boundary detection
        elif protocol_hint == "axi" or "axi" in constraint_name.lower():
            return self._check_axi_boundaries(constraint_name, current_values, window_size)

        # GAXI boundary detection
        elif protocol_hint == "gaxi" or "gaxi" in constraint_name.lower():
            return self._check_gaxi_boundaries(constraint_name, current_values, window_size)

        return False

    def _check_apb_boundaries(self, constraint_name: str, current_values: Dict[str, int],
                                     window_size: int) -> bool:
        """FIXED APB boundary detection - looks for transaction completion"""
        if window_size < 2:
            return False

        constraint_windows = self.constraint_windows[constraint_name]

        # Primary APB boundary: PREADY falling edge (transaction completion)
        pready_signals = [name for name in current_values.keys() if 'pready' in name.lower()]

        for pready_signal in pready_signals:
            if pready_signal in constraint_windows:
                signal_window = list(constraint_windows[pready_signal])
                if len(signal_window) >= 2:
                    prev_ready = signal_window[-2] if len(signal_window) >= 2 else 0
                    curr_ready = current_values[pready_signal]

                    # PREADY 1→0 indicates transaction completion
                    if prev_ready == 1 and curr_ready == 0:
                        if self.debug_level >= 2:
                            self.log.info(f"APB boundary: {pready_signal} 1→0 for {constraint_name}")
                        return True

        # Secondary APB boundary: PSEL falling edge (after transaction)
        psel_signals = [name for name in current_values.keys() if 'psel' in name.lower()]

        for psel_signal in psel_signals:
            if psel_signal in constraint_windows:
                signal_window = list(constraint_windows[psel_signal])
                if len(signal_window) >= 2:
                    prev_sel = signal_window[-2] if len(signal_window) >= 2 else 0
                    curr_sel = current_values[psel_signal]

                    # PSEL 1→0 indicates transaction end
                    if prev_sel == 1 and curr_sel == 0:
                        if self.debug_level >= 2:
                            self.log.info(f"APB boundary: {psel_signal} 1→0 for {constraint_name}")
                        return True

        return False

    def _check_axi_boundaries(self, constraint_name: str, current_values: Dict[str, int],
                                     window_size: int) -> bool:
        """AXI boundary detection with handshake awareness"""
        if window_size < 2:
            return False

        constraint_windows = self.constraint_windows[constraint_name]

        # AXI boundary: valid signals falling after handshake completion
        valid_signals = [name for name in current_values.keys() if 'valid' in name.lower()]

        for valid_signal in valid_signals:
            if valid_signal in constraint_windows:
                signal_window = list(constraint_windows[valid_signal])
                if len(signal_window) >= 2:
                    prev_valid = signal_window[-2]
                    curr_valid = current_values[valid_signal]

                    # Valid 1→0 after handshake indicates completion
                    if prev_valid == 1 and curr_valid == 0:
                        if self.debug_level >= 2:
                            self.log.info(f"AXI boundary: {valid_signal} 1→0 for {constraint_name}")
                        return True

        return False

    def _check_gaxi_boundaries(self, constraint_name: str, current_values: Dict[str, int],
                                      window_size: int) -> bool:
        """GAXI boundary detection"""
        if window_size < 2:
            return False

        constraint_windows = self.constraint_windows[constraint_name]

        # GAXI boundary: similar to AXI with valid/ready handshake
        valid_signals = [name for name in current_values.keys() if 'valid' in name.lower()]

        for valid_signal in valid_signals:
            if valid_signal in constraint_windows:
                signal_window = list(constraint_windows[valid_signal])
                if len(signal_window) >= 2:
                    prev_valid = signal_window[-2]
                    curr_valid = current_values[valid_signal]

                    if prev_valid == 1 and curr_valid == 0:
                        if self.debug_level >= 2:
                            self.log.info(f"GAXI boundary: {valid_signal} 1→0 for {constraint_name}")
                        return True

        return False

    def _get_signal_value(self, dut_signal) -> int:
        """Get integer value from DUT signal"""
        try:
            if hasattr(dut_signal.value, 'integer'):
                return dut_signal.value.integer
            return int(dut_signal.value)
        except:
            return 0

    async def _solve_temporal_constraint(self, constraint_name: str, constraint: TemporalConstraint):
        """Constraint solving with modular WaveJSON generation"""

        if self.debug_level >= 2:
            self.log.info(f"Solving temporal constraint '{constraint_name}'...")

        # Get signal data from rolling windows
        windows = self.constraint_windows[constraint_name]
        signal_data = {}
        for signal_name, values in windows.items():
            signal_data[signal_name] = list(values)

        window_size = len(signal_data[list(signal_data.keys())[0]])

        if self.debug_level >= 2:
            # Debug: show signal values for constraint signals
            for event in constraint.events:
                signal_name = event.pattern.signal
                if signal_name in signal_data:
                    values = signal_data[signal_name]
                    self.log.info(f"  {signal_name}: {values}")

        # Create CP-SAT model
        model = cp_model.CpModel()

        # Create cycle variables for each event
        event_cycle_vars = {}
        for event in constraint.events:
            event_cycle_vars[event.name] = model.NewIntVar(0, window_size - 1, f"event_{event.name}_cycle")

        # Apply boundary constraints if they exist
        if constraint_name in self.boundary_constraints:
            for boundary in self.boundary_constraints[constraint_name]:
                cycle = boundary['cycle']
                reset_signals = boundary['reset_signals']

                if cycle < window_size:
                    self._apply_boundary_constraints_to_model(model, signal_data, cycle, reset_signals)

        # Apply auto-boundary detection if configured
        if constraint_name in self.auto_boundary_configs:
            self._apply_auto_boundary_detection(model, signal_data, constraint_name, window_size)

        # Find cycles where each event can occur
        for event in constraint.events:
            event_var = event_cycle_vars[event.name]
            signal_name = event.pattern.signal

            if signal_name not in signal_data:
                if self.debug_level >= 2:
                    self.log.info(f"Signal {signal_name} not found for event {event.name}")
                return

            values = signal_data[signal_name]
            valid_cycles = []

            if isinstance(event.pattern, SignalTransition):
                # Look for transition from_value → to_value
                from_val, to_val = event.pattern.from_value, event.pattern.to_value
                for cycle in range(1, window_size):
                    if values[cycle-1] == from_val and values[cycle] == to_val:
                        valid_cycles.append(cycle)
                        if self.debug_level >= 2:
                            self.log.info(f"    {event.name} transition {from_val}→{to_val} at cycle {cycle}")

            elif isinstance(event.pattern, SignalStatic):
                # Look for static value
                target_val = event.pattern.value
                for cycle in range(window_size):
                    if values[cycle] == target_val:
                        valid_cycles.append(cycle)

            if not valid_cycles:
                if self.debug_level >= 2:
                    self.log.info(f"No valid cycles found for event {event.name}")
                return

            # Constrain event to occur at one of the valid cycles
            model.AddAllowedAssignments([event_var], [[cycle] for cycle in valid_cycles])

        # Add temporal relationship constraints
        self._add_temporal_relationship_constraints(model, constraint, event_cycle_vars, window_size)

        # Solve the model
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 5.0

        # Collect solutions
        solution_collector = TemporalSolutionCollector(constraint_name, event_cycle_vars)
        status = solver.SearchForAllSolutions(model, solution_collector)

        if status in [cp_model.OPTIMAL, cp_model.FEASIBLE] and solution_collector.solutions:
            if self.debug_level >= 1:
                self.log.info(f"Found {len(solution_collector.solutions)} temporal solutions for '{constraint_name}'")

            # Create solution from first temporal solution
            temporal_solution = solution_collector.solutions[0]
            adjusted_signal_data = self._adjust_window_for_sequence(
                signal_data, temporal_solution, constraint.max_window_size, constraint
            )

            solution = await self._create_solution_result(
                constraint_name, constraint, adjusted_signal_data, temporal_solution
            )
            self.solutions.append(solution)
            self.satisfied_constraints.add(constraint_name)

        elif self.debug_level >= 2:
            status_name = solver.StatusName(status) if hasattr(solver, 'StatusName') else str(status)
            self.log.info(f"No temporal solutions found for '{constraint_name}' (status: {status_name})")

    def _add_temporal_relationship_constraints(self, model, constraint: TemporalConstraint,
                                             event_cycle_vars: Dict, window_size: int):
        """Add temporal relationship constraints to CP-SAT model"""
        if constraint.temporal_relation == TemporalRelation.SEQUENCE:
            # Events must occur in order
            for i in range(len(constraint.events) - 1):
                curr_event = constraint.events[i].name
                next_event = constraint.events[i + 1].name
                model.Add(event_cycle_vars[next_event] > event_cycle_vars[curr_event])

        elif constraint.temporal_relation == TemporalRelation.CONCURRENT:
            # All events must occur at the same time
            base_event = constraint.events[0].name
            for event in constraint.events[1:]:
                model.Add(event_cycle_vars[event.name] == event_cycle_vars[base_event])

        elif constraint.temporal_relation == TemporalRelation.WITHIN:
            # All events must occur within the specified window
            event_vars = list(event_cycle_vars.values())
            min_cycle = model.NewIntVar(0, window_size - 1, "min_cycle")
            max_cycle = model.NewIntVar(0, window_size - 1, "max_cycle")
            model.AddMinEquality(min_cycle, event_vars)
            model.AddMaxEquality(max_cycle, event_vars)
            model.Add(max_cycle - min_cycle <= constraint.max_sequence_duration)

        # Add sequence duration constraints
        if len(constraint.events) > 1:
            event_vars = list(event_cycle_vars.values())
            min_cycle = model.NewIntVar(0, window_size - 1, "seq_min")
            max_cycle = model.NewIntVar(0, window_size - 1, "seq_max")
            model.AddMinEquality(min_cycle, event_vars)
            model.AddMaxEquality(max_cycle, event_vars)

            duration = model.NewIntVar(0, window_size - 1, "duration")
            model.Add(duration == max_cycle - min_cycle)
            model.Add(duration >= constraint.min_sequence_duration - 1)
            model.Add(duration <= constraint.max_sequence_duration - 1)

    def _apply_boundary_constraints_to_model(self, model, signal_data, boundary_cycle, reset_signals):
        """Apply boundary constraints to the CP-SAT model"""
        for signal_name, reset_value in reset_signals.items():
            if signal_name in signal_data and boundary_cycle < len(signal_data[signal_name]):
                if self.debug_level >= 2:
                    actual_val = signal_data[signal_name][boundary_cycle]
                    self.log.info(f"Boundary constraint: {signal_name}[{boundary_cycle}] = {reset_value} (actual: {actual_val})")

    def _apply_auto_boundary_detection(self, model, signal_data, constraint_name, window_size):
        """Apply auto-detected boundary constraints"""
        config = self.auto_boundary_configs[constraint_name]
        transition_signal = config['transition_signal']
        from_val, to_val = config['transition_value']
        reset_signals = config['reset_signals']

        if transition_signal in signal_data:
            values = signal_data[transition_signal]

            for cycle in range(window_size - 1):
                if values[cycle] == from_val and values[cycle + 1] == to_val:
                    boundary_cycle = cycle + 2
                    if boundary_cycle < window_size:
                        self._apply_boundary_constraints_to_model(model, signal_data, boundary_cycle, reset_signals)
                        if self.debug_level >= 2:
                            self.log.info(f"Auto-boundary at cycle {boundary_cycle} after {transition_signal} {from_val}→{to_val}")

    def _adjust_window_for_sequence(self, signal_data: Dict[str, List[int]],
                                   temporal_solution: Dict, window_size: int,
                                   constraint: TemporalConstraint = None) -> Dict[str, List[int]]:
        """Adjust the signal window to show the complete sequence with context and post-match extension"""
        adjusted_data = {}
        data_length = len(signal_data[list(signal_data.keys())[0]])

        seq_start = temporal_solution['sequence_start']
        seq_end = temporal_solution['sequence_end']

        context_before = max(3, window_size // 4)
        context_after = max(3, window_size // 4)

        # Check for post-match cycles extension
        post_match_cycles = 0
        if constraint and hasattr(constraint, 'post_match_cycles'):
            post_match_cycles = constraint.post_match_cycles
            if self.debug_level >= 2:
                self.log.info(f"  Adding {post_match_cycles} post-match cycles for {constraint.name}")

        start_idx = max(0, seq_start - context_before)
        end_idx = min(data_length, seq_end + context_after + post_match_cycles + 1)

        # Ensure we don't exceed the original window size limit too much
        max_total_window = window_size + post_match_cycles + 5  # Allow some flexibility
        if end_idx - start_idx > max_total_window:
            end_idx = start_idx + max_total_window

        for signal_name, values in signal_data.items():
            adjusted_data[signal_name] = values[start_idx:end_idx]

        if self.debug_level >= 2:
            seq_duration = temporal_solution['sequence_duration']
            actual_window = end_idx - start_idx
            self.log.info(f"  Sequence window: start={seq_start}, end={seq_end}, duration={seq_duration}")
            self.log.info(f"  Adjusted window: [{start_idx}:{end_idx}] ({actual_window} cycles)")
            if post_match_cycles > 0:
                self.log.info(f"  Extended by {post_match_cycles} post-match cycles")

        return adjusted_data

    async def _create_solution_result(self, constraint_name: str, constraint: TemporalConstraint,
                                             signal_data: Dict[str, List[int]], temporal_solution: Dict) -> SolutionResult:
        """Create solution result with FIXED edge node application"""

        if self.debug_level >= 2:
            self.log.info(f"Creating solution for {constraint_name}:")
            for event_name, cycle in temporal_solution['event_timing'].items():
                self.log.info(f"  {event_name} at cycle {cycle}")

        # WaveJSON generation with multiple methods
        wavejson = None
        filename = f"{constraint_name}_{len([s for s in self.solutions if s.constraint_name == constraint_name])+1:03d}.json"

        # Method 1: Custom callback
        if constraint_name in self.wavejson_callbacks:
            try:
                wavejson = self.wavejson_callbacks[constraint_name](constraint, signal_data, temporal_solution)
            except Exception as e:
                self.log.error(f"Custom WaveJSON callback failed for {constraint_name}: {e}")

        # Method 2: Packet-based callback
        if not wavejson and constraint_name in self.packet_based_callbacks:
            try:
                packet_class, callback = self.packet_based_callbacks[constraint_name]
                # Create packet instance with field_config if available
                if constraint.field_config:
                    packet_obj = packet_class(field_config=constraint.field_config)
                else:
                    packet_obj = packet_class()
                wavejson = callback(packet_obj, signal_data, temporal_solution)
            except Exception as e:
                self.log.error(f"Packet-based WaveJSON callback failed for {constraint_name}: {e}")

        # Method 3: Modular WaveJSON generator
        if not wavejson and self.wavejson_generator:
            try:
                # Create temporal annotations
                annotations = []
                event_timing = temporal_solution.get('event_timing', {})
                for event_name, cycle in event_timing.items():
                    annotations.append(TemporalAnnotation(event_name, cycle))

                # Generate title and subtitle
                interface_name = "Protocol"
                if constraint.protocol_hint:
                    interface_name = constraint.protocol_hint.upper()
                elif constraint.signals_to_show and '_' in constraint.signals_to_show[0]:
                    interface_name = constraint.signals_to_show[0].split('_')[0].upper()

                title = f"{interface_name} {constraint_name.replace('_', ' ').title()} Sequence"
                seq_duration = temporal_solution.get('sequence_duration', 1)
                relation = constraint.temporal_relation.value
                subtitle = f"Modular: {len(constraint.events)} events, {relation}, {seq_duration} cycles | CP-SAT Solved"

                wavejson = self.wavejson_generator.generate_wavejson(
                    signal_data=signal_data,
                    title=title,
                    subtitle=subtitle,
                    temporal_annotations=annotations,
                    protocol_hint=constraint.protocol_hint
                )
            except Exception as e:
                self.log.error(f"WaveJSON generation failed for {constraint_name}: {e}")

        # FIXED: Ensure edge nodes are properly applied
        if wavejson and "edge" in wavejson and wavejson["edge"]:
            # Force the WaveJSON generator to re-apply node mappings
            if self.wavejson_generator:
                try:
                    # Create temporal annotations
                    annotations = []
                    event_timing = temporal_solution.get('event_timing', {})
                    for event_name, cycle in event_timing.items():
                        annotations.append(TemporalAnnotation(event_name, cycle))

                    # Re-generate edge annotations with proper node mappings
                    edges, node_mappings = self.wavejson_generator._generate_edge_annotations(
                        annotations, signal_data
                    )

                    if edges:
                        wavejson["edge"] = edges

                    if node_mappings:
                        # FIXED: Apply node mappings more carefully
                        wavejson["signal"] = self._apply_node_mappings_fixed(wavejson["signal"], node_mappings)

                        if self.debug_level >= 2:
                            self.log.info(f"Applied node mappings for {constraint_name}: {node_mappings}")

                except Exception as e:
                    self.log.error(f"Failed to apply edge nodes for {constraint_name}: {e}")

        # Save WaveJSON to file
        if wavejson:
            try:
                if self.wavejson_generator:
                    filename = self.wavejson_generator.save_wavejson(wavejson, filename)
                else:
                    import json
                    with open(filename, 'w') as f:
                        json.dump(wavejson, f, indent=2)
                    if self.debug_level >= 1:
                        self.log.info(f"Generated: {filename}")
            except Exception as e:
                self.log.error(f"Failed to save WaveJSON {filename}: {e}")

        return SolutionResult(
            constraint_name=constraint_name,
            filename=filename,
            window_data=signal_data,
            wavejson=wavejson or {},
            temporal_solution=temporal_solution,
            field_config=constraint.field_config,
            protocol_hint=constraint.protocol_hint,
            wavejson_generator=self.wavejson_generator
        )

    def _apply_node_mappings_fixed(self, signals: List[Any], node_mappings: Dict[str, str]) -> List[Any]:
        """FIXED node mapping application that handles both grouped and ungrouped signals"""

        def apply_to_signal_list(signal_list, indent=""):
            for i, item in enumerate(signal_list):
                if isinstance(item, dict) and 'name' in item:
                    # This is a signal object
                    display_name = item['name']

                    # Try to find matching node mapping
                    node_string = None

                    # Direct match by display name
                    if display_name in node_mappings:
                        node_string = node_mappings[display_name]
                    else:
                        # Try to find by partial matching
                        for full_name, nodes in node_mappings.items():
                            # Match if display name is in the full signal name or vice versa
                            if (display_name.lower() in full_name.lower() or
                                full_name.lower() in display_name.lower() or
                                full_name.split('_')[-1].lower() == display_name.lower()):
                                node_string = nodes
                                break

                    # Apply node string if found
                    if node_string:
                        item['node'] = node_string
                        if self.debug_level >= 2:
                            self.log.info(f"{indent}Applied nodes to '{display_name}': {node_string}")

                elif isinstance(item, list) and len(item) > 1:
                    # This is a signal group [group_name, signal1, signal2, ...]
                    group_name = item[0] if isinstance(item[0], str) else "Group"
                    if self.debug_level >= 2:
                        self.log.info(f"{indent}Processing group '{group_name}' with {len(item)-1} signals")

                    # Recursively process signals in the group
                    apply_to_signal_list(item[1:], indent + "  ")

        # Process the signal list
        apply_to_signal_list(signals)
        return signals

    def get_results(self) -> Dict:
        """Get final results"""
        failed_constraints = []
        for name, constraint in self.constraints.items():
            if constraint.required and name not in self.satisfied_constraints:
                failed_constraints.append(name)

        return {
            "solutions": self.solutions,
            "satisfied_constraints": list(self.satisfied_constraints),
            "failed_constraints": failed_constraints,
            "all_required_satisfied": len(failed_constraints) == 0,
            "wavejson_generator_stats": self.wavejson_generator.get_stats() if self.wavejson_generator else {},
            "protocol_configs": len(self.signal_field_configs),
            "boundary_configs": len(self.auto_boundary_configs)
        }

    def debug_status(self):
        """Print debug status"""
        self.log.info("Temporal Constraint Solver Status:")
        self.log.info(f"  Clock groups: {len(self.clock_groups)}")
        self.log.info(f"  Signal bindings: {len(self.signal_bindings)}")
        self.log.info(f"  Protocol configs: {len(self.signal_field_configs)}")
        self.log.info(f"  Temporal constraints: {len(self.constraints)}")
        self.log.info(f"  Solutions found: {len(self.solutions)}")

        for constraint_name, constraint in self.constraints.items():
            cycle_count = self.constraint_cycle_counters.get(constraint_name, 0)
            window_size = 0
            if self.constraint_windows.get(constraint_name) and self.signal_bindings:
                first_signal = list(self.signal_bindings.keys())[0]
                window_size = len(self.constraint_windows[constraint_name].get(first_signal, deque()))
            status = "✅" if constraint_name in self.satisfied_constraints else "❌"
            event_count = len(constraint.events)
            relation = constraint.temporal_relation.value
            protocol = constraint.protocol_hint or "generic"
            self.log.info(f"    {constraint_name}: {cycle_count} cycles, window={window_size}/{constraint.max_window_size}, {event_count} events ({relation}), protocol={protocol} {status}")

        # Boundary configuration display
        if self.auto_boundary_configs:
            self.log.info("Auto-boundary configurations:")
            for constraint_name, config in self.auto_boundary_configs.items():
                signal = config['transition_signal']
                transition = config['transition_value']
                reset_count = len(config['reset_signals'])
                self.log.info(f"    {constraint_name}: {signal} {transition[0]}→{transition[1]} (resets {reset_count} signals)")

        # WaveJSON generator status
        if self.wavejson_generator:
            stats = self.wavejson_generator.get_stats()
            self.log.info(f"WaveJSON Generator:")
            self.log.info(f"    Total signals: {stats['total_signals']}")
            self.log.info(f"    Interface groups: {stats['interface_groups']}")
            self.log.info(f"    Protocol configs: {stats.get('protocol_configs', 0)}")
            self.log.info(f"    FieldConfig signals: {stats.get('fieldconfig_signals', 0)}")


# Compatibility alias for backward compatibility
TemporalConstraintSolver = TemporalConstraintSolver
