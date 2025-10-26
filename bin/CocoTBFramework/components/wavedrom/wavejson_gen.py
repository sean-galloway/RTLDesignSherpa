# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SignalType
# Purpose: WaveJSON Generator with FieldConfig Integration
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
WaveJSON Generator with FieldConfig Integration

Generates properly formatted WaveJSON from signal data for use with WaveDrom.
Supports temporal sequence annotations, protocol-aware formatting, and direct
integration with FieldConfig for automatic signal configuration.
"""

import json
from typing import Dict, List, Optional, Any, Tuple, Union
from dataclasses import dataclass
from enum import Enum

# Required imports - no conditionals
from ..shared.field_config import FieldConfig, FieldDefinition


class SignalType(Enum):
    """Signal type classification"""
    CLOCK = "clock"
    SINGLE_BIT = "single_bit"
    MULTI_BIT = "multi_bit"
    BUS = "bus"


@dataclass
class SignalConfig:
    """Configuration for a signal in the waveform"""
    name: str
    display_name: str
    signal_type: SignalType
    format_style: str = "hex"  # hex, bin, dec
    bit_width: int = 1
    group: Optional[str] = None
    field_definition: Optional['FieldDefinition'] = None  # Direct FieldConfig integration


@dataclass
class TemporalAnnotation:
    """Temporal event annotation for sequence marking"""
    name: str
    cycle: int
    description: str = ""
    signal_name: Optional[str] = None  # Signal this event is associated with


class WaveJSONGenerator:
    """
    WaveJSON generator with FieldConfig integration and protocol-aware formatting.

    Features:
    - Direct FieldConfig integration for automatic signal configuration
    - Protocol-specific signal grouping and interface organization
    - Temporal sequence annotations with correct edge nodes
    - Boundary detection integration
    - Automatic signal classification from FieldConfig
    - Multibit signal data synchronization
    - Compliant with WaveDrom specification
    """

    def __init__(self, debug_level: int = 1, default_field_config: Optional[FieldConfig] = None):
        """
        Initialize WaveJSON generator.

        Args:
            debug_level: Debug output level (0=none, 1=basic, 2=verbose)
            default_field_config: Default FieldConfig for signal configuration
        """
        self.debug_level = debug_level
        self.default_field_config = default_field_config
        self.signal_configs: Dict[str, SignalConfig] = {}
        self.interface_groups: Dict[str, List[str]] = {}
        self.protocol_configs: Dict[str, FieldConfig] = {}

        # Signal classification patterns with FieldConfig integration
        self.single_bit_patterns = [
            'clk', 'clock', 'sel', 'enable', 'ready', 'valid', 'write', 'err',
            'psel', 'penable', 'pready', 'pwrite', 'pslverr', 'reset', 'rst',
            'awvalid', 'awready', 'wvalid', 'wready', 'bvalid', 'bready',
            'arvalid', 'arready', 'rvalid', 'rready', 'last'
        ]

        self.multibit_patterns = [
            'addr', 'data', 'strb', 'prot', 'len', 'size', 'id', 'user',
            'paddr', 'pwdata', 'prdata', 'pstrb', 'pprot', 'awaddr', 'araddr',
            'wdata', 'rdata', 'awlen', 'arlen', 'awsize', 'arsize', 'resp',
            'bresp', 'rresp'
        ]

        self.clock_patterns = ['clk', 'clock']

    def set_protocol_config(self, protocol_name: str, field_config: FieldConfig):
        """Set FieldConfig for a specific protocol"""
        self.protocol_configs[protocol_name] = field_config
        if self.debug_level >= 1:
            print(f"Set FieldConfig for {protocol_name}: {len(field_config.field_names())} fields")

    def add_signal_config(self, signal_name: str, config: SignalConfig):
        """Add signal configuration"""
        self.signal_configs[signal_name] = config

    def add_interface_group(self, group_name: str, signal_names: List[str]):
        """Add interface group for signal organization"""
        self.interface_groups[group_name] = signal_names

    def configure_from_field_config(self, field_config: FieldConfig,
                                   interface_prefix: str = "",
                                   protocol_name: str = "default"):
        """
        Configure signals directly from a FieldConfig object.

        Args:
            field_config: FieldConfig object containing field definitions
            interface_prefix: Prefix to add to signal names
            protocol_name: Protocol name for grouping
        """
        configured_signals = []

        for field_name, field_def in field_config.items():
            # Create signal name with optional prefix
            signal_name = f"{interface_prefix}_{field_name}" if interface_prefix else field_name

            # Determine signal type from FieldConfig
            signal_type = self._classify_signal_from_field_def(field_def)

            # Create signal config with FieldConfig integration
            config = SignalConfig(
                name=signal_name,
                display_name=self._get_display_name_from_field_def(field_def, interface_prefix),
                signal_type=signal_type,
                format_style=self._get_format_style_from_field_def(field_def),
                bit_width=field_def.bits,
                field_definition=field_def
            )

            self.signal_configs[signal_name] = config
            configured_signals.append(signal_name)

            if self.debug_level >= 2:
                print(f"Configured from FieldConfig: {signal_name} -> {field_def.bits}b {field_def.format}")

        # Add interface group if we have a protocol name
        if protocol_name != "default" and configured_signals:
            group_name = f"{protocol_name.upper()} Interface"
            self.interface_groups[group_name] = configured_signals

        return configured_signals

    def configure_packet_signals(self, packet_obj, interface_prefix: str = ""):
        """
        Configure signals from a packet object (APBPacket, GAXIPacket, etc.).

        Args:
            packet_obj: Packet object with field_config attribute
            interface_prefix: Prefix for signal names
        """
        if hasattr(packet_obj, 'field_config') and packet_obj.field_config:
            protocol_name = packet_obj.__class__.__name__.replace('Packet', '').lower()
            return self.configure_from_field_config(
                packet_obj.field_config,
                interface_prefix,
                protocol_name
            )
        else:
            # Fallback to auto-configuration
            signal_names = []
            if hasattr(packet_obj, 'fields'):
                signal_names = list(packet_obj.fields.keys())
            return self.auto_configure_signals(signal_names, interface_prefix)

    def auto_configure_signals(self, signal_names: List[str], interface_prefix: str = ""):
        """
        Automatically configure signals based on naming patterns.

        Args:
            signal_names: List of signal names to configure
            interface_prefix: Prefix to remove from display names
        """
        for signal_name in signal_names:
            signal_type = self._classify_signal(signal_name)
            display_name = self._get_display_name(signal_name, interface_prefix)

            config = SignalConfig(
                name=signal_name,
                display_name=display_name,
                signal_type=signal_type,
                format_style=self._get_format_style(signal_name),
                bit_width=self._estimate_bit_width(signal_name)
            )

            self.signal_configs[signal_name] = config

    def generate_wavejson(self,
                         signal_data: Dict[str, List[int]],
                         title: str = "Digital Timing Diagram",
                         subtitle: str = "",
                         temporal_annotations: List[TemporalAnnotation] = None,
                         config_options: Dict[str, Any] = None,
                         protocol_hint: str = None,
                         signal_order: List[str] = None) -> Dict[str, Any]:
        """
        Generate complete WaveJSON from signal data with FieldConfig integration.

        Args:
            signal_data: Dictionary mapping signal names to value lists
            title: Diagram title
            subtitle: Diagram subtitle
            temporal_annotations: List of temporal event annotations
            config_options: Additional WaveDrom configuration options
            protocol_hint: Protocol hint for better formatting
            signal_order: Optional list specifying signal order (may include '|' for grouping)

        Returns:
            Complete WaveJSON dictionary
        """
        if not signal_data:
            raise ValueError("No signal data provided")

        window_size = len(next(iter(signal_data.values())))

        # Try to configure from protocol-specific FieldConfig if available
        if protocol_hint and protocol_hint in self.protocol_configs:
            unconfigured_signals = [name for name in signal_data.keys()
                                  if name not in self.signal_configs]
            if unconfigured_signals:
                self.configure_from_field_config(
                    self.protocol_configs[protocol_hint],
                    protocol_name=protocol_hint
                )

        # Auto-configure any remaining signals
        unconfigured_signals = [name for name in signal_data.keys()
                              if name not in self.signal_configs]
        if unconfigured_signals:
            self.auto_configure_signals(unconfigured_signals)

        # Generate signal array with formatting (respecting signal_order if provided)
        signals = self._generate_signal_array(signal_data, window_size, signal_order)

        # Create base WaveJSON structure
        wavejson = {
            "signal": signals,
            "head": {
                "text": title,
                "tick": 0,
                "every": 2
            }
        }

        # Add subtitle if provided
        if subtitle:
            wavejson["foot"] = {"text": subtitle}

        # Add configuration options
        default_config = {"hscale": 2}
        if config_options:
            default_config.update(config_options)
        wavejson["config"] = default_config

        # Add temporal annotations with edge nodes
        if temporal_annotations:
            edges, node_mappings = self._generate_edge_annotations(
                temporal_annotations, signal_data
            )
            if edges:
                wavejson["edge"] = edges
            if node_mappings:
                wavejson["signal"] = self._apply_node_mappings(wavejson["signal"], node_mappings)

        return wavejson

    def _classify_signal_from_field_def(self, field_def: 'FieldDefinition') -> SignalType:
        """Classify signal type from FieldDefinition"""
        # Check field name patterns first
        field_name_lower = field_def.name.lower()

        # Clock signals
        for pattern in self.clock_patterns:
            if pattern in field_name_lower:
                return SignalType.CLOCK

        # Single bit signals
        if field_def.bits == 1:
            return SignalType.SINGLE_BIT

        # Multi-bit signals
        if field_def.bits > 1:
            # Check if it's a bus (address, data) vs control multi-bit
            for pattern in ['addr', 'data']:
                if pattern in field_name_lower:
                    return SignalType.BUS
            return SignalType.MULTI_BIT

        return SignalType.SINGLE_BIT

    def _get_display_name_from_field_def(self, field_def: 'FieldDefinition',
                                        interface_prefix: str = "") -> str:
        """Get display name from FieldDefinition"""
        # Use description if available and meaningful
        if field_def.description and field_def.description != field_def.name:
            return field_def.description

        # Fall back to formatted field name
        return self._get_display_name(field_def.name, interface_prefix)

    def _get_format_style_from_field_def(self, field_def: 'FieldDefinition') -> str:
        """Get format style from FieldDefinition"""
        # Use the format from FieldDefinition if available
        if hasattr(field_def, 'format') and field_def.format:
            return field_def.format

        # Fall back to pattern-based detection
        return self._get_format_style(field_def.name)

    def _generate_signal_array(self, signal_data: Dict[str, List[int]],
                              window_size: int,
                              signal_order: List[str] = None) -> List[Any]:
        """
        Generate the signal array for WaveJSON with FieldConfig support.

        If signal_order is provided, signals are ordered and grouped according to that list.
        The '|' character in signal_order creates a visual separator.
        """
        signals = []

        # If signal_order is provided, use it for ordering and grouping
        if signal_order:
            for item in signal_order:
                # Handle grouping separator
                if item == '|':
                    # Add empty object for visual separator (WaveDrom convention)
                    signals.append({})
                    continue

                # Handle nested arrays for labeled groups: ['GroupName', 'sig1', 'sig2', ...]
                if isinstance(item, list):
                    if len(item) < 2:
                        continue  # Skip empty or malformed groups

                    group_label = item[0]
                    group_signals = []

                    # Process each signal in the group
                    for sig_name in item[1:]:
                        if sig_name not in signal_data:
                            continue

                        # Generate signal based on type
                        config = self.signal_configs.get(sig_name)
                        if config and config.signal_type == SignalType.CLOCK:
                            clock_wave = self._generate_clock_wave(window_size)
                            group_signals.append({
                                "name": config.display_name,
                                "wave": clock_wave
                            })
                        else:
                            signal_dict = self._generate_signal_dict(sig_name, signal_data[sig_name])
                            if signal_dict:
                                group_signals.append(signal_dict)

                    # Add labeled group if it has signals
                    if group_signals:
                        signals.append([group_label, *group_signals])
                    continue

                # Handle string signal names (backward compatibility)
                sig_name = item

                # Skip if signal not in data
                if sig_name not in signal_data:
                    continue

                # Generate signal based on type
                config = self.signal_configs.get(sig_name)
                if config and config.signal_type == SignalType.CLOCK:
                    # Clock signal
                    clock_wave = self._generate_clock_wave(window_size)
                    signals.append({
                        "name": config.display_name,
                        "wave": clock_wave
                    })
                else:
                    # Regular signal
                    signal_dict = self._generate_signal_dict(sig_name, signal_data[sig_name])
                    if signal_dict:
                        signals.append(signal_dict)

            return signals

        # Original behavior: auto-group by interface
        # Add clock signal first if present
        clock_signals = [name for name in signal_data.keys()
                        if self.signal_configs.get(name, SignalConfig("", "", SignalType.SINGLE_BIT)).signal_type == SignalType.CLOCK]

        for clock_name in clock_signals:
            clock_wave = self._generate_clock_wave(window_size)
            config = self.signal_configs[clock_name]
            signals.append({
                "name": config.display_name,
                "wave": clock_wave
            })

        # Group signals by interface with FieldConfig integration
        grouped_signals = self._group_signals_by_interface(signal_data)

        # Add grouped signals
        for group_name, group_signals in grouped_signals.items():
            if group_name == "_ungrouped":
                # Add ungrouped signals directly
                signals.extend(group_signals)
            else:
                # Add gap before interface group
                if signals:
                    signals.append({})

                # Add interface group with formatting
                signals.append([group_name, *group_signals])

        return signals

    def _group_signals_by_interface(self, signal_data: Dict[str, List[int]]) -> Dict[str, List[Dict]]:
        """Group signals by their interface with FieldConfig support"""
        groups = {"_ungrouped": []}

        # Process configured interface groups
        for group_name, signal_names in self.interface_groups.items():
            group_signals = []
            for signal_name in signal_names:
                if signal_name in signal_data:
                    signal_dict = self._generate_signal_dict(signal_name, signal_data[signal_name])
                    if signal_dict:
                        group_signals.append(signal_dict)

            if group_signals:
                groups[group_name] = group_signals

        # Process ungrouped signals
        grouped_signal_names = set()
        for signal_names in self.interface_groups.values():
            grouped_signal_names.update(signal_names)

        for signal_name, values in signal_data.items():
            config = self.signal_configs.get(signal_name)
            if (signal_name not in grouped_signal_names and
                config and config.signal_type != SignalType.CLOCK):

                signal_dict = self._generate_signal_dict(signal_name, values)
                if signal_dict:
                    groups["_ungrouped"].append(signal_dict)

        # Remove empty groups
        return {k: v for k, v in groups.items() if v}

    def _generate_signal_dict(self, signal_name: str, values: List[int]) -> Optional[Dict[str, Any]]:
        """Generate signal dictionary for a single signal with FieldConfig support"""
        config = self.signal_configs.get(signal_name)
        if not config or config.signal_type == SignalType.CLOCK:
            return None

        wave_str, data_values = self._values_to_wave_string(values, config)

        signal_dict = {
            "name": config.display_name,
            "wave": wave_str
        }

        # Add data values for multibit signals
        if config.signal_type in [SignalType.MULTI_BIT, SignalType.BUS] and data_values:
            signal_dict["data"] = data_values

        return signal_dict

    def _values_to_wave_string(self, values: List[int],
                              config: SignalConfig) -> Tuple[str, List[str]]:
        """
        Convert signal values to proper WaveDrom wave string with FieldConfig integration.

        Returns:
            Tuple of (wave_string, data_values)
        """
        if not values:
            return "", []

        wave = []
        data_values = []
        last_value = None
        state_counter = 2  # Start multibit states from '2'

        for value in values:
            if value == last_value:
                wave.append('.')  # Extend previous state
            else:
                if config.signal_type == SignalType.SINGLE_BIT:
                    # Handle undefined values
                    if value == -1:
                        wave.append('x')
                    else:
                        wave.append('1' if value else '0')

                elif config.signal_type in [SignalType.MULTI_BIT, SignalType.BUS]:
                    # Handle undefined values
                    if value == -1:
                        wave.append('x')
                    elif value == 0:
                        wave.append('0')  # Zero state
                    else:
                        # Use numbered states for non-zero values
                        if state_counter <= 9:
                            wave.append(str(state_counter))
                            state_counter += 1
                        else:
                            wave.append('=')  # Generic transition

                        # Add formatted data value using FieldConfig if available
                        data_values.append(self._format_data_value_with_fieldconfig(value, config))

                last_value = value

        return ''.join(wave), data_values

    def _format_data_value_with_fieldconfig(self, value: int, config: SignalConfig) -> str:
        """Format data value with FieldConfig integration"""
        if value == -1:
            return "X"

        # Use FieldConfig information if available
        if config.field_definition:
            field_def = config.field_definition

            # Mask value to field width for cleaner display
            mask = (1 << field_def.bits) - 1
            masked_value = value & mask

            # Check for encoding first
            if hasattr(field_def, 'encoding') and field_def.encoding and masked_value in field_def.encoding:
                return field_def.encoding[masked_value]

            # Use FieldConfig format
            if field_def.format == "bin":
                return f"0b{masked_value:0{field_def.bits}b}"
            elif field_def.format == "dec":
                return str(masked_value)
            else:  # hex
                width = (field_def.bits + 3) // 4
                return f"0x{masked_value:0{width}X}"

        # Fall back to original formatting
        return self._format_data_value(value, config)

    def _format_data_value(self, value: int, config: SignalConfig) -> str:
        """Format data value based on signal configuration (fallback)"""
        if value == -1:
            return "X"

        signal_lower = config.name.lower()

        if config.format_style == "bin":
            return f"0b{value:0{config.bit_width}b}"
        elif config.format_style == "dec":
            return str(value)
        else:  # hex (default)
            if 'addr' in signal_lower:
                return f"0x{value:08X}"
            elif 'data' in signal_lower and config.bit_width >= 16:
                return f"0x{value:08X}"
            elif config.bit_width >= 8:
                return f"0x{value:0{(config.bit_width + 3) // 4}X}"
            else:
                return f"0x{value:X}"

    def _generate_clock_wave(self, window_size: int) -> str:
        """Generate clock wave string"""
        if window_size == 0:
            return ""
        return "p" + "." * (window_size - 1)

    def _classify_signal(self, signal_name: str) -> SignalType:
        """Classify signal type based on name patterns (fallback)"""
        signal_lower = signal_name.lower()

        # Check clock patterns first
        for pattern in self.clock_patterns:
            if pattern in signal_lower:
                return SignalType.CLOCK

        # Check single bit patterns
        for pattern in self.single_bit_patterns:
            if pattern in signal_lower:
                return SignalType.SINGLE_BIT

        # Check multibit patterns
        for pattern in self.multibit_patterns:
            if pattern in signal_lower:
                return SignalType.MULTI_BIT

        # Default to single bit
        return SignalType.SINGLE_BIT

    def _get_display_name(self, signal_name: str, interface_prefix: str = "") -> str:
        """Get display name for signal (fallback)"""
        display_name = signal_name

        # IMPORTANT: Keep wr_/rd_ prefixes for clarity
        # Only remove the interface_prefix if explicitly specified
        if interface_prefix and signal_name.startswith(interface_prefix + "_"):
            display_name = signal_name[len(interface_prefix) + 1:]
        # Otherwise keep the full signal name (preserves wr_valid, rd_ready, etc.)

        return display_name

    def _get_format_style(self, signal_name: str) -> str:
        """Get format style based on signal name (fallback)"""
        signal_lower = signal_name.lower()

        if 'strb' in signal_lower or 'mask' in signal_lower:
            return "bin"
        elif 'count' in signal_lower or 'len' in signal_lower:
            return "dec"
        else:
            return "hex"

    def _estimate_bit_width(self, signal_name: str) -> int:
        """Estimate bit width based on signal name (fallback)"""
        signal_lower = signal_name.lower()

        if 'addr' in signal_lower:
            return 32
        elif 'data' in signal_lower:
            return 32
        elif 'strb' in signal_lower:
            return 4
        elif 'prot' in signal_lower:
            return 3
        elif 'len' in signal_lower:
            return 8
        elif 'size' in signal_lower:
            return 3
        else:
            return 1

    def _generate_edge_annotations(self, annotations: List[TemporalAnnotation],
                                          signal_data: Dict[str, List[int]]) -> Tuple[List[str], Dict[str, str]]:
        """
        Generate both edge annotations and node mappings for signals with improved positioning.

        Returns:
            Tuple of (edge_list, signal_node_mappings)
        """
        if not annotations:
            return [], {}

        edges = []
        signal_nodes = {}

        # Sort annotations by cycle
        sorted_annotations = sorted(annotations, key=lambda x: x.cycle)

        # NEW: Distribute nodes across different signals based on event names
        # This creates arrows BETWEEN signals showing causality
        wave_length = len(next(iter(signal_data.values()))) if signal_data else 0

        for i, annotation in enumerate(sorted_annotations):
            cycle = annotation.cycle
            if cycle >= wave_length:
                continue

            node_char = chr(ord('a') + i)

            # Try to place node on the signal specified in annotation first
            node_placed = False

            if annotation.signal_name and annotation.signal_name in signal_data:
                if annotation.signal_name not in signal_nodes:
                    signal_nodes[annotation.signal_name] = ['.'] * wave_length
                signal_nodes[annotation.signal_name][cycle] = node_char
                node_placed = True
            else:
                # Fallback: try to match signal name in event name
                event_name_lower = annotation.name.lower()

                for signal_name in signal_data.keys():
                    signal_lower = signal_name.lower()
                    # Match signal name in event name (e.g., "wr_valid" in "write_start")
                    if signal_lower in event_name_lower or any(part in event_name_lower for part in signal_lower.split('_')):
                        if signal_name not in signal_nodes:
                            signal_nodes[signal_name] = ['.'] * wave_length
                        signal_nodes[signal_name][cycle] = node_char
                        node_placed = True
                        break

            # Fallback: place on control signal if no match
            if not node_placed:
                control_patterns = ['valid', 'sel', 'enable', 'ready', 'penable', 'psel']
                for pattern in control_patterns:
                    for signal_name in signal_data.keys():
                        if pattern in signal_name.lower():
                            if signal_name not in signal_nodes:
                                signal_nodes[signal_name] = ['.'] * wave_length
                            signal_nodes[signal_name][cycle] = node_char
                            node_placed = True
                            break
                    if node_placed:
                        break

            # Last resort: first signal
            if not node_placed and signal_data:
                first_signal = list(signal_data.keys())[0]
                if first_signal not in signal_nodes:
                    signal_nodes[first_signal] = ['.'] * wave_length
                signal_nodes[first_signal][cycle] = node_char

        # Convert node lists to strings
        for sig_name in signal_nodes:
            if isinstance(signal_nodes[sig_name], list):
                signal_nodes[sig_name] = ''.join(signal_nodes[sig_name])

        # Create edge annotations - ONE meaningful arrow per constraint
        # Only create arrows if we have nodes placed on signals
        if len(sorted_annotations) >= 2 and signal_nodes:
            start_node = chr(ord('a'))
            end_node = chr(ord('a') + len(sorted_annotations) - 1)
            duration = sorted_annotations[-1].cycle - sorted_annotations[0].cycle + 1

            # Verify nodes were actually placed before creating edge
            nodes_placed = any(start_node in ''.join(nodes) for nodes in signal_nodes.values())

            if nodes_placed:
                # Determine arrow type based on constraint relationship and signals
                # Check if this looks like a handshake (valid/ready pattern)
                signal_names = list(signal_data.keys())
                has_valid = any('valid' in s.lower() for s in signal_names)
                has_ready = any('ready' in s.lower() for s in signal_names)

                # Check for APB protocol
                is_apb = any('psel' in s.lower() or 'penable' in s.lower() for s in signal_names)

                # Generate ONE primary arrow with appropriate type and label
                if has_valid and has_ready:
                    # GAXI/AXI handshake - use squiggly arrow for async relationship
                    label = sorted_annotations[0].description or sorted_annotations[0].name
                    label = label.replace('_', ' ').title()

                    # Special case: backpressure/blocking - use direct arrow for blocking period
                    if 'blocked' in label.lower() or 'ready_drops' in sorted_annotations[0].name.lower():
                        edges.append(f"{start_node}->{end_node} Write Blocked")
                    else:
                        edges.append(f"{start_node}~>{end_node} {label}")
                elif is_apb:
                    # APB protocol - use direct arrow for sequential relationship
                    if len(sorted_annotations) == 2:
                        # Simple setup -> access
                        edges.append(f"{start_node}->{end_node} Psel Active→Enable")
                    else:
                        # Multi-phase
                        edges.append(f"{start_node}<->{end_node} APB Sequence: {duration} cycles")
                else:
                    # Generic sequence - use bidirectional arrow with duration
                    edges.append(f"{start_node}<->{end_node} Sequence: {duration} cycles")

        if self.debug_level >= 2:
            for sig, nodes in signal_nodes.items():
                print(f"Generated nodes for {sig}: {nodes}")
            print(f"Generated edges: {edges}")

        return edges, signal_nodes

    def _apply_node_mappings(self, signals: List[Any], node_mappings: Dict[str, str]) -> List[Any]:
        """FIXED node mappings application with better signal matching"""

        def apply_to_signal_list(signal_list, indent=""):
            for item in signal_list:
                if isinstance(item, dict) and 'name' in item:
                    # This is a signal object
                    display_name = item['name']

                    # Try different matching strategies
                    node_string = None

                    # Strategy 1: Direct match
                    if display_name in node_mappings:
                        node_string = node_mappings[display_name]

                    # Strategy 2: Try to find by signal name patterns
                    if not node_string:
                        for full_name, nodes in node_mappings.items():
                            # Extract the signal part from full_name (e.g., "apb_psel" -> "psel")
                            signal_part = full_name.split('_')[-1] if '_' in full_name else full_name

                            # Match against display name (case insensitive)
                            if (signal_part.lower() == display_name.lower() or
                                display_name.lower() in signal_part.lower() or
                                signal_part.lower() in display_name.lower()):
                                node_string = nodes
                                break

                    # Strategy 3: Pattern matching for common signal names
                    if not node_string:
                        display_lower = display_name.lower()
                        for full_name, nodes in node_mappings.items():
                            full_lower = full_name.lower()
                            # Look for key signal patterns
                            if (('select' in display_lower and 'psel' in full_lower) or
                                ('enable' in display_lower and 'penable' in full_lower) or
                                ('ready' in display_lower and 'pready' in full_lower) or
                                ('write' in display_lower and 'pwrite' in full_lower) or
                                ('address' in display_lower and 'paddr' in full_lower) or
                                ('data' in display_lower and ('pwdata' in full_lower or 'prdata' in full_lower)) or
                                ('strobe' in display_lower and 'pstrb' in full_lower) or
                                ('protection' in display_lower and 'pprot' in full_lower) or
                                ('error' in display_lower and 'pslverr' in full_lower)):
                                node_string = nodes
                                break

                    # Apply the node string if found
                    if node_string:
                        item['node'] = node_string
                        if self.debug_level >= 2:
                            print(f"{indent}Applied nodes to '{display_name}': {node_string}")
                    elif self.debug_level >= 2:
                        print(f"{indent}No nodes found for '{display_name}' (available: {list(node_mappings.keys())})")

                elif isinstance(item, list) and len(item) > 1:
                    # This is a signal group - recursively process
                    if self.debug_level >= 2 and isinstance(item[0], str):
                        print(f"{indent}Processing group '{item[0]}'")
                    apply_to_signal_list(item[1:], indent + "  ")  # Skip group name

        apply_to_signal_list(signals)
        return signals

    def save_wavejson(self, wavejson: Dict[str, Any], filename: str) -> str:
        """
        Save WaveJSON to file.

        Returns:
            Full path to saved file
        """
        with open(filename, 'w') as f:
            json.dump(wavejson, f, indent=2)

        if self.debug_level >= 1:
            print(f"Generated WaveJSON: {filename}")

        return filename

    def validate_wavejson(self, wavejson: Dict[str, Any]) -> Tuple[bool, List[str]]:
        """
        Validate WaveJSON structure.

        Returns:
            Tuple of (is_valid, error_messages)
        """
        errors = []

        # Check required fields
        if "signal" not in wavejson:
            errors.append("Missing required 'signal' field")

        # Validate signal array
        if "signal" in wavejson:
            if not isinstance(wavejson["signal"], list):
                errors.append("'signal' must be an array")
            else:
                for i, signal in enumerate(wavejson["signal"]):
                    if isinstance(signal, dict):
                        if "name" not in signal:
                            errors.append(f"Signal {i} missing 'name' field")
                        if "wave" not in signal:
                            errors.append(f"Signal {i} missing 'wave' field")
                        # Check for valid wave characters
                        if "wave" in signal:
                            valid_chars = set('01.=x23456789p~|nlhPNHLzuU-')
                            wave_chars = set(signal["wave"])
                            invalid_chars = wave_chars - valid_chars
                            if invalid_chars:
                                errors.append(f"Signal {i} wave contains invalid characters: {invalid_chars}")
                    elif isinstance(signal, list):
                        if len(signal) < 1:
                            errors.append(f"Signal group {i} is empty")
                        elif not isinstance(signal[0], str):
                            errors.append(f"Signal group {i} first element must be group name")
                    elif signal != {}:  # Empty object is valid (gap)
                        errors.append(f"Signal {i} has invalid format")

        # Validate edges if present
        if "edge" in wavejson:
            if not isinstance(wavejson["edge"], list):
                errors.append("'edge' must be an array")
            else:
                for i, edge in enumerate(wavejson["edge"]):
                    if not isinstance(edge, str):
                        errors.append(f"Edge {i} must be a string")

        return len(errors) == 0, errors

    def get_stats(self) -> Dict[str, Any]:
        """Get generator statistics with FieldConfig integration info"""
        signal_types = {}
        fieldconfig_signals = 0

        for config in self.signal_configs.values():
            signal_type = config.signal_type.value
            signal_types[signal_type] = signal_types.get(signal_type, 0) + 1

            if config.field_definition is not None:
                fieldconfig_signals += 1

        return {
            "total_signals": len(self.signal_configs),
            "signal_types": signal_types,
            "interface_groups": len(self.interface_groups),
            "protocol_configs": len(self.protocol_configs),
            "fieldconfig_signals": fieldconfig_signals,
            "fieldconfig_available": True,
            "debug_level": self.debug_level
        }


# Helper functions for creating protocol-specific configurations

def create_apb_wavejson_generator(field_config: Optional[FieldConfig] = None) -> WaveJSONGenerator:
    """Create WaveJSON generator configured for APB protocol with FieldConfig integration"""
    generator = WaveJSONGenerator(debug_level=1, default_field_config=field_config)

    if field_config:
        # Configure directly from FieldConfig
        generator.configure_from_field_config(field_config, interface_prefix="apb", protocol_name="apb")
    else:
        # Fallback to manual configuration
        apb_signals = [
            "apb_psel", "apb_penable", "apb_pready", "apb_pwrite",
            "apb_paddr", "apb_pwdata", "apb_prdata", "apb_pstrb",
            "apb_pprot", "apb_pslverr"
        ]
        generator.add_interface_group("APB Interface", apb_signals)

    return generator


def create_axi_wavejson_generator(field_config: Optional[FieldConfig] = None) -> WaveJSONGenerator:
    """Create WaveJSON generator configured for AXI protocol with FieldConfig integration"""
    generator = WaveJSONGenerator(debug_level=1, default_field_config=field_config)

    if field_config:
        # Configure directly from FieldConfig
        generator.configure_from_field_config(field_config, interface_prefix="axi", protocol_name="axi")
    else:
        # Fallback to manual configuration
        axi_groups = {
            "AXI Write Address": ["axi_awvalid", "axi_awready", "axi_awaddr", "axi_awlen", "axi_awsize"],
            "AXI Write Data": ["axi_wvalid", "axi_wready", "axi_wdata", "axi_wstrb", "axi_wlast"],
            "AXI Write Response": ["axi_bvalid", "axi_bready", "axi_bresp"],
            "AXI Read Address": ["axi_arvalid", "axi_arready", "axi_araddr", "axi_arlen", "axi_arsize"],
            "AXI Read Data": ["axi_rvalid", "axi_rready", "axi_rdata", "axi_rresp", "axi_rlast"]
        }

        for group_name, signals in axi_groups.items():
            generator.add_interface_group(group_name, signals)

    return generator


def create_gaxi_wavejson_generator(field_config: Optional[FieldConfig] = None) -> WaveJSONGenerator:
    """Create WaveJSON generator configured for GAXI protocol with FieldConfig integration"""
    generator = WaveJSONGenerator(debug_level=1, default_field_config=field_config)

    if field_config:
        # Configure directly from FieldConfig
        generator.configure_from_field_config(field_config, interface_prefix="gaxi", protocol_name="gaxi")
    else:
        # Fallback to manual configuration
        gaxi_signals = [
            "gaxi_valid", "gaxi_ready", "gaxi_cmd", "gaxi_addr",
            "gaxi_data", "gaxi_strb", "gaxi_resp"
        ]
        generator.add_interface_group("GAXI Interface", gaxi_signals)

    return generator


def create_wavejson_from_packet(packet_obj,
                               signal_data: Dict[str, List[int]],
                               title: str = None,
                               interface_prefix: str = "") -> Dict[str, Any]:
    """
    Create WaveJSON directly from a packet object with FieldConfig integration.

    Args:
        packet_obj: Packet object (APBPacket, GAXIPacket, etc.)
        signal_data: Signal timing data
        title: Optional title (derived from packet if not provided)
        interface_prefix: Prefix for signal names

    Returns:
        Complete WaveJSON dictionary
    """
    generator = WaveJSONGenerator(debug_level=1)

    # Configure from packet
    generator.configure_packet_signals(packet_obj, interface_prefix)

    # Generate title if not provided
    if title is None:
        protocol_name = packet_obj.__class__.__name__.replace('Packet', '')
        title = f"{protocol_name} Transaction Timing"

    # Generate WaveJSON
    return generator.generate_wavejson(
        signal_data=signal_data,
        title=title,
        protocol_hint=packet_obj.__class__.__name__.replace('Packet', '').lower()
    )