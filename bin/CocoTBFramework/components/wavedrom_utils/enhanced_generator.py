"""
Enhanced WaveDrom generator with extended capabilities for CocoTB

This module extends the base WaveDrom generator with additional features
for pattern matching, statistical analysis, and enhanced visualization.
"""

import json
from typing import Dict, List, Optional, Tuple, Any, Set, Union, Callable
from dataclasses import dataclass, field
from enum import Enum, auto
import re
from datetime import datetime

from cocotb.triggers import RisingEdge, FallingEdge, Edge, Timer

from .models import EdgeType, ArrowStyle, SignalEvent, SignalRelation


class SignalAnalysisType(Enum):
    """Types of signal analysis to perform"""
    TOGGLE_RATE = auto()       # Signal toggle frequency
    PULSE_WIDTH = auto()       # Width of signal pulses
    PATTERN_MATCH = auto()     # Match specific bit patterns
    STATISTICS = auto()        # Statistical analysis of values
    DEPENDENCIES = auto()      # Identify signal dependencies
    TIMING = auto()            # Measure timing metrics


@dataclass
class EnhancedWaveDromConfig:
    """Configuration for enhanced WaveDrom generator"""
    title: str = "WaveDrom Analysis"
    hscale: float = 1.0
    skin: str = "default"
    include_time_scale: bool = True
    auto_save: bool = False
    auto_save_format: str = "json"
    highlight_violations: bool = True
    max_history_size: int = 10000
    statistical_analysis: bool = False
    include_html_wrapper: bool = False


class EnhancedWaveDromGenerator:
    """Enhanced WaveDrom generator with advanced analysis capabilities"""
    
    def __init__(self, clock, config: EnhancedWaveDromConfig = None):
        """
        Initialize enhanced WaveDrom generator
        
        Args:
            clock: Clock signal from DUT
            config: Optional configuration settings
        """
        self.clock = clock
        self.config = config or EnhancedWaveDromConfig()
        self.signals: Dict[str, Dict] = {}
        self.relations: List[SignalRelation] = []
        self.detected_relations: List[SignalRelation] = []
        self.current_cycle = 0
        self.event_history: List[tuple] = []  # [(cycle, signal, value, edge_type)]
        self.debug_points: List[dict] = []
        self.signal_statistics: Dict[str, Dict] = {}
        self.signal_patterns: Dict[str, List[Dict]] = {}
        self.annotations: List[Dict] = {}
        self.start_time = datetime.now()
    
    def add_signal(self, name: str, dut_path: str, clock_domain: str = None, 
                  analysis_types: List[SignalAnalysisType] = None):
        """
        Add a signal to track during simulation with enhanced analysis
        
        Args:
            name: Display name for the signal
            dut_path: Path to signal in DUT hierarchy
            clock_domain: Optional clock domain for the signal
            analysis_types: Optional list of analysis types to perform
        """
        self.signals[name] = {
            "path": dut_path,
            "values": [],
            "last_value": None,
            "clock_domain": clock_domain or "default",
            "analysis": analysis_types or [],
            "statistics": {
                "toggles": 0,
                "toggle_rate": 0.0,
                "time_high": 0,
                "time_low": 0,
                "min_pulse_width": float('inf'),
                "max_pulse_width": 0,
                "patterns": {}
            }
        }
        
        # Initialize statistics tracking if enabled
        if self.config.statistical_analysis:
            self.signal_statistics[name] = {
                "transitions": [],
                "high_cycles": 0,
                "low_cycles": 0,
                "last_transition": 0,
                "values": []
            }
    
    def add_pattern(self, signal_name: str, pattern_name: str, pattern: Union[str, int, List],
                   highlight_color: str = "red"):
        """
        Add a pattern to detect on a signal
        
        Args:
            signal_name: Name of the signal to monitor
            pattern_name: Name for this pattern
            pattern: Bit pattern as string, integer, or list of 0/1
            highlight_color: Color to use when highlighting pattern in output
        """
        if signal_name not in self.signals:
            raise ValueError(f"Signal {signal_name} not found. Add it first with add_signal().")
            
        if signal_name not in self.signal_patterns:
            self.signal_patterns[signal_name] = []
            
        # Convert pattern to binary string if needed
        if isinstance(pattern, int):
            pattern = bin(pattern)[2:]  # Convert to binary string without '0b' prefix
        elif isinstance(pattern, list):
            pattern = ''.join(str(bit) for bit in pattern)
            
        # Add the pattern
        self.signal_patterns[signal_name].append({
            "name": pattern_name,
            "pattern": pattern,
            "color": highlight_color,
            "occurrences": []  # Will store cycle numbers where pattern is found
        })
        
        # Add pattern to statistics tracking
        if signal_name in self.signal_statistics:
            self.signal_statistics[signal_name]["patterns"][pattern_name] = 0
    
    def add_annotation(self, cycle: int, text: str, signals: Dict[str, Any] = None,
                     style: Dict[str, str] = None):
        """
        Add a custom annotation to the waveform
        
        Args:
            cycle: Clock cycle for the annotation
            text: Annotation text
            signals: Optional dict of signal values to associate
            style: Optional style settings like color, fontSize, etc.
        """
        annotation = {
            "cycle": cycle,
            "text": text,
            "signals": signals or {},
            "style": style or {"color": "blue"}
        }
        
        cycle_str = str(cycle)
        if cycle_str not in self.annotations:
            self.annotations[cycle_str] = []
            
        self.annotations[cycle_str].append(annotation)
    
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
        if old_val is None:
            return False
            
        if edge_type == EdgeType.ANY_CHANGE:
            return old_val != new_val
        if edge_type == EdgeType.RISING:
            return old_val == 0 and new_val == 1
        if edge_type == EdgeType.FALLING:
            return old_val == 1 and new_val == 0
        if edge_type == EdgeType.BOTH:
            return (old_val == 0 and new_val == 1) or (old_val == 1 and new_val == 0)
            
        return old_val != new_val
    
    def _check_patterns(self, signal_name: str, value):
        """Check for pattern matches on a signal"""
        if signal_name not in self.signal_patterns:
            return
            
        # Convert value to binary string
        try:
            if hasattr(value, "integer"):
                value = value.integer
                
            if isinstance(value, int):
                bin_str = bin(value)[2:]  # Convert to binary without '0b' prefix
                
                # Check each pattern
                for pattern_data in self.signal_patterns[signal_name]:
                    pattern = pattern_data["pattern"]
                    if pattern in bin_str:
                        pattern_data["occurrences"].append(self.current_cycle)
                        
                        # Update statistics
                        if signal_name in self.signal_statistics:
                            stats = self.signal_statistics[signal_name]
                            pattern_name = pattern_data["name"]
                            if pattern_name in stats["patterns"]:
                                stats["patterns"][pattern_name] += 1
        except (TypeError, ValueError):
            # Skip pattern checking for this value
            pass
    
    async def sample(self):
        """
        Sample all signals and check for relationships
        
        Enhanced to track statistics and check for patterns
        """
        await RisingEdge(self.clock)
        self.current_cycle += 1
        
        # Check if we should truncate history to prevent memory issues
        if self.config.max_history_size > 0 and len(self.event_history) > self.config.max_history_size:
            # Keep the most recent events
            self.event_history = self.event_history[-self.config.max_history_size:]
        
        # Sample all signals and detect edges
        for name, signal in self.signals.items():
            try:
                new_value = eval(f"dut.{signal['path']}.value")
                old_value = signal["last_value"]
                
                # For statistics tracking
                if self.config.statistical_analysis:
                    stats = self.signal_statistics[name]
                    stats["values"].append(new_value)
                    
                    # Track binary signal statistics
                    try:
                        # Handle cocotb values with integer property
                        if hasattr(new_value, "integer"):
                            new_int = new_value.integer
                            is_binary = (new_int == 0 or new_int == 1)
                        else:
                            is_binary = (new_value == 0 or new_value == 1)
                            new_int = new_value
                            
                        if is_binary:
                            if new_int == 1:
                                stats["high_cycles"] += 1
                            else:
                                stats["low_cycles"] += 1
                                
                            # Check for toggle
                            if old_value is not None and old_value != new_value:
                                stats["transitions"].append(self.current_cycle)
                                
                                # Track pulse width
                                if len(stats["transitions"]) >= 2:
                                    pulse_width = stats["transitions"][-1] - stats["transitions"][-2]
                                    signal["statistics"]["min_pulse_width"] = min(
                                        signal["statistics"]["min_pulse_width"], 
                                        pulse_width
                                    )
                                    signal["statistics"]["max_pulse_width"] = max(
                                        signal["statistics"]["max_pulse_width"], 
                                        pulse_width
                                    )
                    except (TypeError, ValueError):
                        # Not a binary signal, skip binary statistics
                        pass
                
                if new_value != old_value:
                    signal["values"].append((self.current_cycle, new_value))
                    
                    # Check patterns
                    self._check_patterns(name, new_value)
                    
                    # Detect edges
                    if old_value is not None:
                        # Update toggle count for statistics
                        signal["statistics"]["toggles"] += 1
                        
                        # Record specific edge types
                        if old_value == 0 and new_value == 1:
                            self.event_history.append((self.current_cycle, name, new_value, EdgeType.RISING))
                        elif old_value == 1 and new_value == 0:
                            self.event_history.append((self.current_cycle, name, new_value, EdgeType.FALLING))
                        
                        # Always record any change
                        self.event_history.append((self.current_cycle, name, new_value, EdgeType.ANY_CHANGE))
                
                signal["last_value"] = new_value
            except Exception as e:
                # Skip this signal for this cycle if there's an error
                pass
        
        # Process relationships
        self._process_relations()
        
        # Auto-save if configured
        if self.config.auto_save and self.current_cycle % 100 == 0:
            self._auto_save()
    
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
                    # Check if this pair is already recorded
                    pair = (c_cycle, matching_effects[0][0])
                    if not hasattr(relation, 'detected_pairs'):
                        relation.detected_pairs = []
                        
                    if pair not in relation.detected_pairs:
                        relation.detected_pairs.append(pair)
                        
                        if relation not in self.detected_relations:
                            self.detected_relations.append(relation)
    
    def add_debug_point(self, cycle: int, message: str, signals: Dict[str, Any], 
                      category: str = "violation", severity: str = "warning"):
        """
        Add an enhanced debugging annotation
        
        Args:
            cycle: Clock cycle for the annotation
            message: Debug message
            signals: Dict of signal values at this debug point
            category: Category of debug point (e.g., "violation", "info")
            severity: Severity level ("info", "warning", "error")
        """
        self.debug_points.append({
            'cycle': cycle,
            'message': message,
            'signals': signals,
            'category': category,
            'severity': severity,
            'timestamp': datetime.now()
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
    
    def get_signal_statistics(self, signal_name: str = None) -> Dict:
        """
        Get statistics for one or all signals
        
        Args:
            signal_name: Optional signal name, or None for all signals
            
        Returns:
            Dictionary of signal statistics
        """
        if not self.config.statistical_analysis:
            return {}
            
        # Update statistics before returning
        self._update_statistics()
        
        if signal_name:
            if signal_name in self.signal_statistics:
                return self.signal_statistics[signal_name]
            return {}
            
        return self.signal_statistics
    
    def _update_statistics(self):
        """Update signal statistics based on collected data"""
        for name, stats in self.signal_statistics.items():
            if name in self.signals:
                signal = self.signals[name]
                
                # Calculate toggle rate (toggles per cycle)
                if self.current_cycle > 0:
                    toggle_rate = stats["transitions"].__len__() / self.current_cycle
                    signal["statistics"]["toggle_rate"] = toggle_rate
                
                # Calculate high/low percentages
                total_cycles = stats["high_cycles"] + stats["low_cycles"]
                if total_cycles > 0:
                    signal["statistics"]["time_high"] = stats["high_cycles"] / total_cycles * 100
                    signal["statistics"]["time_low"] = stats["low_cycles"] / total_cycles * 100
    
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
                if hasattr(value, "integer"):
                    value = value.integer
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
        Generate enhanced WaveDrom JSON output
        
        Args:
            output_file: Optional path to save JSON output
            
        Returns:
            WaveDrom JSON configuration dictionary
        """
        # Update statistics if enabled
        if self.config.statistical_analysis:
            self._update_statistics()
            
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
                
            # Add optional attributes
            if "clock_domain" in signal and signal["clock_domain"] != "default":
                config["node"] = signal["clock_domain"]
                
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
            
            # Add styling based on severity if highlighting is enabled
            if self.config.highlight_violations:
                if debug["severity"] == "error":
                    note["color"] = "red"
                elif debug["severity"] == "warning":
                    note["color"] = "orange"
                else:
                    note["color"] = "blue"
                    
            edges.append(note)
            
        # Add custom annotations
        for cycle_str, annotations in self.annotations.items():
            for annotation in annotations:
                note = {
                    "text": annotation["text"],
                    "time": annotation["cycle"]
                }
                
                # Add styling if provided
                if "style" in annotation and "color" in annotation["style"]:
                    note["color"] = annotation["style"]["color"]
                    
                edges.append(note)
                
        # Create the wavedrom configuration
        wavedrom = {
            "signal": signal_configs,
            "edge": edges,
            "config": {"hscale": self.config.hscale, "skin": self.config.skin}
        }
        
        # Add title and metadata
        if self.config.title:
            wavedrom["head"] = {"text": self.config.title}
            
        # Add time scale if enabled
        if self.config.include_time_scale:
            wavedrom["foot"] = {
                "text": f"Cycles: 0-{self.current_cycle}, " +
                       f"Simulation duration: {(datetime.now() - self.start_time).total_seconds():.2f}s"
            }
            
        # Generate HTML wrapper if requested
        if self.config.include_html_wrapper:
            html_output = self._generate_html(wavedrom)
            if output_file and output_file.endswith(".html"):
                with open(output_file, 'w') as f:
                    f.write(html_output)
                    
        # Write JSON output if requested
        if output_file and not output_file.endswith(".html"):
            with open(output_file, 'w') as f:
                json.dump(wavedrom, f, indent=2)
                
        return wavedrom
    
    def _generate_html(self, wavedrom_json: Dict) -> str:
        """Generate HTML with embedded WaveDrom JSON"""
        html = f"""<!DOCTYPE html>
<html>
<head>
    <title>{self.config.title}</title>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/2.6.8/skins/default.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/2.6.8/wavedrom.min.js"></script>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        .container {{ max-width: 1200px; margin: 0 auto; }}
        .stats {{ margin-top: 20px; }}
        table {{ border-collapse: collapse; width: 100%; margin-bottom: 20px; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #f2f2f2; }}
        tr:nth-child(even) {{ background-color: #f9f9f9; }}
    </style>
</head>
<body onload="WaveDrom.ProcessAll()">
    <div class="container">
        <h1>{self.config.title}</h1>
        <script type="WaveDrom">
{json.dumps(wavedrom_json, indent=4)}
        </script>
        
        <div class="stats">
            <h2>Signal Statistics</h2>
            <table>
                <tr>
                    <th>Signal</th>
                    <th>Toggle Rate</th>
                    <th>Time High (%)</th>
                    <th>Min Pulse Width</th>
                    <th>Max Pulse Width</th>
                </tr>
"""
        
        # Add signal statistics rows
        for name, signal in self.signals.items():
            stats = signal["statistics"]
            min_pulse = stats["min_pulse_width"]
            if min_pulse == float('inf'):
                min_pulse = "N/A"
                
            html += f"""                <tr>
                    <td>{name}</td>
                    <td>{stats["toggle_rate"]:.4f}</td>
                    <td>{stats["time_high"]:.1f}%</td>
                    <td>{min_pulse}</td>
                    <td>{stats["max_pulse_width"]}</td>
                </tr>
"""
        
        # Close the HTML
        html += """            </table>
        </div>
        
        <div class="debug">
            <h2>Debug Annotations</h2>
            <table>
                <tr>
                    <th>Cycle</th>
                    <th>Message</th>
                    <th>Category</th>
                    <th>Severity</th>
                </tr>
"""
        
        # Add debug annotations
        for debug in self.debug_points:
            html += f"""                <tr>
                    <td>{debug["cycle"]}</td>
                    <td>{debug["message"]}</td>
                    <td>{debug["category"]}</td>
                    <td>{debug["severity"]}</td>
                </tr>
"""
        
        # Finish the HTML
        html += """            </table>
        </div>
    </div>
</body>
</html>
"""
        return html
    
    def _auto_save(self):
        """Auto-save the current waveform state if configured"""
        if not self.config.auto_save:
            return
            
        # Generate filename with timestamp
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"wavedrom_{self.config.title.replace(' ', '_')}_{timestamp}"
        
        if self.config.auto_save_format == "html":
            filename += ".html"
        else:
            filename += ".json"
            
        # Generate output
        self.generate(filename)
