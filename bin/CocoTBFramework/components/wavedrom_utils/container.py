"""
Container for managing multiple verification scenarios
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Callable, Any
import json

from .models import SignalRelation
from .generator import WaveDromGenerator

@dataclass
class ScenarioConfig:
    """Configuration for a verification scenario"""
    name: str
    description: str
    pre_cycles: int = 2   # Cycles to capture before first event
    post_cycles: int = 2  # Cycles to capture after last event
    relations: List[SignalRelation] = field(default_factory=list)
    debug_checks: List[Dict[str, Any]] = field(default_factory=list)

@dataclass
class WaveformContainer:
    """Container for multiple verification scenarios"""
    title: str
    clock_signal: str
    signal_groups: Dict[str, List[str]]
    scenarios: List[ScenarioConfig]

    def __post_init__(self):
        """Initialize after creation"""
        self.wave_gen = WaveDromGenerator(self.clock_signal)
        self._add_signals()

    def _add_signals(self):
        """Add all signals from groups to wave generator"""
        signals = set()
        for group in self.signal_groups.values():
            signals.update(group)
        for signal in signals:
            self.wave_gen.add_signal(signal, signal)  # Using signal name as path

    async def run_scenario(self, dut, scenario: ScenarioConfig):
        """
        Run a specific verification scenario

        Args:
            dut: CocoTB device under test
            scenario: Scenario configuration to run
        """
        print(f"Running scenario: {scenario.name}")

        # Initialize cycle counters
        start_cycle = self.wave_gen.current_cycle
        event_cycles = set()

        # Add relations for this scenario
        for relation in scenario.relations:
            self.wave_gen.add_relation(relation)

        # Run until we see all expected events plus post_cycles
        max_cycles = 1000  # Safety limit
        cycles_run = 0

        while cycles_run < max_cycles:
            await self.wave_gen.sample()
            cycles_run += 1

            # Check for events
            for relation in self.wave_gen.detected_relations:
                if relation in scenario.relations:
                    for pair in relation.detected_pairs:
                        event_cycles.add(pair[1])  # Add effect cycle

            # Run debug checks
            for check in scenario.debug_checks:
                if 'function' in check:
                    check_result = await check['function'](dut, self.wave_gen)
                    if check_result:
                        print(f"Debug check triggered: {check.get('description', 'unnamed check')}")
                        event_cycles.add(self.wave_gen.current_cycle)

            # Check if we're done - we've seen events and waited post_cycles after the last one
            if event_cycles and (self.wave_gen.current_cycle - max(event_cycles)) >= scenario.post_cycles:
                break

        # Safety check
        if cycles_run >= max_cycles:
            print("Warning: Scenario reached cycle limit without completion")

        print(f"Scenario completed after {self.wave_gen.current_cycle - start_cycle} cycles")

    async def run_all_scenarios(self, dut):
        """
        Run all scenarios in sequence

        Args:
            dut: CocoTB device under test
        """
        for scenario in self.scenarios:
            await self.run_scenario(dut, scenario)

    def generate_wavedrom(self, output_file: Optional[str] = None) -> Dict:
        """
        Generate WaveDrom JSON with all scenarios

        Args:
            output_file: Optional file to write JSON output

        Returns:
            WaveDrom JSON configuration object
        """
        wavedrom = self.wave_gen.generate()

        # Add signal groups
        wavedrom["groups"] = [
            {"name": name, "signals": signals}
            for name, signals in self.signal_groups.items()
        ]

        # Add title
        wavedrom["head"] = {"text": self.title}

        if output_file:
            with open(output_file, 'w') as f:
                json.dump(wavedrom, f, indent=2)

        return wavedrom

