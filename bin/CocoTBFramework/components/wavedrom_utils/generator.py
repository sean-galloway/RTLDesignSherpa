"""
WaveDrom generator for CocoTB
"""

import json
from typing import Dict, List, Optional, Tuple, Any
from cocotb.triggers import RisingEdge, FallingEdge, Edge

from .models import EdgeType, ArrowStyle, SignalEvent, SignalRelation

class WaveDromGenerator:
    def __init__(self, clock):
        """
        Initialize the WaveDrom generator with a clock signal

        Args:
            clock: Clock signal from DUT
        """
        self.clock = clock
        self.signals: Dict[str, Dict] = {}
        self.relations: List[SignalRelation] = []
        self.detected_relations: List[SignalRelation] = []
        self.current_cycle = 0
        self.event_history: List[tuple] = []  # [(cycle, signal, value, edge_type)]
        self.debug_points: List[dict] = []

    def add_signal(self, name: str, dut_path: str):
        """
        Add a signal to track during simulation

        Args:
            name: Display name for the signal
            dut_path: Path to signal in DUT hierarchy
        """
        self.signals[name] = {
            "path": dut_path,
            "values": [],
            "last_value": None
        }

    def add_relation(self, relation: SignalRelation):
        """
        Add a timing relationship between signals

        Args:
            relation: SignalRelation object defining the relationship
        """
        self.relations.append(relation)

    def _detect_edge(self, old_val, new_val, edge_type: EdgeType) -> bool:
        """
        Detect if an edge occurred based on old and new values

        Args:
            old_val: Previous signal value
            new_val: Current signal value
            edge_type: Type of edge to detect

        Returns:
            bool: True if specified edge detected
        """
        if edge_type == EdgeType.ANY_CHANGE:
            return old_val != new_val
        if edge_type == EdgeType.RISING:
            return old_val == 0 and new_val == 1
        if edge_type == EdgeType.FALLING:
            return old_val == 1 and new_val == 0
        return old_val != new_val

    async def sample(self):
        """Sample all signals and check for relationships"""
        await RisingEdge(self.clock)
        self.current_cycle += 1

        # Sample all signals and detect edges
        for name, signal in self.signals.items():
            new_value = eval(f"dut.{signal['path']}.value")
            old_value = signal["last_value"]

            if new_value != old_value:
                signal["values"].append((self.current_cycle, new_value))

                # Detect edges
                if old_value is not None:
                    if old_value == 0 and new_value == 1:
                        self.event_history.append((self.current_cycle, name, new_value, EdgeType.RISING))
                    elif old_value == 1 and new_value == 0:
                        self.event_history.append((self.current_cycle, name, new_value, EdgeType.FALLING))
                    self.event_history.append((self.current_cycle, name, new_value, EdgeType.ANY_CHANGE))

                signal["last_value"] = new_value

        # Process relationships
        self._process_relations()

    def _process_relations(self):
        """Process signal relationships and generate WaveDrom decorations"""
        for relation in self.relations:
            # Find matching cause events
            cause_events = [
                (cycle, sig, val, edge) for cycle, sig, val, edge in self.event_history
                if sig == relation.cause.signal
                and edge == relation.cause.edge_type
                and (relation.cause.value is None or val == relation.cause.value)
            ]

            # Find matching effect events
            effect_events = [
                (cycle, sig, val, edge) for cycle, sig, val, edge in self.event_history
                if sig == relation.effect.signal
                and edge == relation.effect.edge_type
                and (relation.effect.value is None or val == relation.effect.value)
            ]

            # Match pairs that satisfy timing constraints
            for c_cycle, _, _, _ in cause_events:
                if matching_effects := [
                    (e_cycle, e_sig)
                    for e_cycle, e_sig, _, _ in effect_events
                    if relation.min_cycles
                    <= (e_cycle - c_cycle)
                    <= (relation.max_cycles or float('inf'))
                ]:
                    relation.detected_pairs.append((c_cycle, matching_effects[0][0]))
                    if relation not in self.detected_relations:
                        self.detected_relations.append(relation)

    def add_debug_point(self, cycle: int, message: str, signals: Dict[str, Any]):
        """
        Add a debugging annotation

        Args:
            cycle: Clock cycle for the annotation
            message: Debug message
            signals: Dict of signal values at this debug point
        """
        self.debug_points.append({
            'cycle': cycle,
            'message': message,
            'signals': signals
        })

    def get_last_value(self, signal_name: str) -> Any:
        """
        Get the last recorded value of a signal

        Args:
            signal_name: Name of the signal

        Returns:
            Last recorded value
        """
        return self.signals.get(signal_name, {}).get("last_value")

    def cycles_since_event(self, event: SignalEvent) -> int:
        """
        Calculate cycles since a specific event

        Args:
            event: The event to check

        Returns:
            Number of cycles since last occurrence, or -1 if not found
        """
        matching_events = [
            (cycle, sig, val, edge) for cycle, sig, val, edge in self.event_history
            if sig == event.signal and edge == event.edge_type
            and (event.value is None or val == event.value)
        ]

        if not matching_events:
            return -1

        most_recent = max(matching_events, key=lambda x: x[0])
        return self.current_cycle - most_recent[0]

    def _generate_wave_string(self, values: List[Tuple[int, Any]]) -> Dict:
        """
        Generate WaveDrom wave string from sampled values

        Args:
            values: List of (cycle, value) tuples

        Returns:
            Dict with 'wave' string and optional 'data' list
        """
        if not values:
            return {"wave": "", "data": None}

        wave = []
        data = []
        last_cycle = 0

        for cycle, value in values:
            # Fill gaps with continuation
            if wave:
                wave.extend('.' * (cycle - last_cycle - 1))

            # Add transition
            if isinstance(value, (bool, int)):
                wave.append('1' if value else '0')
            elif isinstance(value, str) and len(value) == 1:
                wave.append(value)  # Use single characters directly
            else:
                wave.append('=')
                data.append(str(value))

            last_cycle = cycle

        return {
            "wave": ''.join(wave),
            "data": data or None
        }

    def generate(self, output_file: Optional[str] = None) -> Dict:
        """
        Generate WaveDrom JSON output

        Args:
            output_file: Optional path to save JSON output

        Returns:
            WaveDrom JSON configuration dictionary
        """
        signal_configs = []
        edges = []

        # Generate signal waves
        for name, signal in self.signals.items():
            wave_data = self._generate_wave_string(signal["values"])
            config = {
                "name": name,
                "wave": wave_data["wave"]
            }

            if wave_data["data"]:
                config["data"] = wave_data["data"]

            signal_configs.append(config)

        # Generate edges for detected relationships
        for relation in self.relations:
            if hasattr(relation, 'detected_pairs') and relation.detected_pairs:
                edges.extend(
                    {
                        "from": relation.cause.signal,
                        "to": relation.effect.signal,
                        "time": cause_cycle,
                        "style": relation.style.value,
                    }
                    for cause_cycle, effect_cycle in relation.detected_pairs
                )
        # Generate debug annotations
        for debug in self.debug_points:
            note = {
                "text": debug["message"],
                "time": debug["cycle"]
            }
            edges.append(note)

        wavedrom = {
            "signal": signal_configs,
            "edge": edges,
            "config": {"hscale": 1}
        }

        if output_file:
            with open(output_file, 'w') as f:
                json.dump(wavedrom, f, indent=2)

        return wavedrom

