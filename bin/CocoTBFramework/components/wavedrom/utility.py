# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: utility
# Purpose: Utility Functions with FieldConfig Integration
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Utility Functions with FieldConfig Integration

Provides utility functions for creating temporal events, patterns, and annotations
with FieldConfig support and protocol awareness.
"""

from typing import List, Dict, Any, Optional, Union
from dataclasses import dataclass

# Required imports - no conditionals
from .constraint_solver import SignalTransition, SignalStatic, TemporalEvent, TemporalAnnotation
from ..shared.field_config import FieldConfig, FieldDefinition
from .wavejson_gen import WaveJSONGenerator, create_wavejson_from_packet


def create_transition_pattern(signal_name: str, from_value: int, to_value: int) -> SignalTransition:
    """
    Create a signal transition pattern with validation.

    Args:
        signal_name: Name of the signal
        from_value: Initial value
        to_value: Final value

    Returns:
        SignalTransition object
    """
    return SignalTransition(signal_name, from_value, to_value)


def create_static_pattern(signal_name: str, value: int) -> SignalStatic:
    """
    Create a static signal pattern with validation.

    Args:
        signal_name: Name of the signal
        value: Static value

    Returns:
        SignalStatic object
    """
    return SignalStatic(signal_name, value)


def create_temporal_event(name: str, pattern: Union[SignalTransition, SignalStatic],
                         timing_tolerance: int = 0) -> TemporalEvent:
    """
    Create a temporal event.

    Args:
        name: Event name
        pattern: Signal pattern (transition or static)
        timing_tolerance: Timing tolerance in cycles

    Returns:
        TemporalEvent object
    """
    return TemporalEvent(name, pattern, timing_tolerance)


def create_temporal_annotations_from_solution(temporal_solution: Dict[str, Any]) -> List[TemporalAnnotation]:
    """
    Create temporal annotations from a temporal solution.

    Args:
        temporal_solution: Solution dictionary from constraint solver

    Returns:
        List of TemporalAnnotation objects
    """
    annotations = []
    event_timing = temporal_solution.get('event_timing', {})

    for event_name, cycle in event_timing.items():
        # Create descriptive annotation
        description = event_name.replace('_', ' ').title()
        annotations.append(TemporalAnnotation(event_name, cycle, description))

    return annotations


def create_fieldconfig_from_signals(signal_list: List[str],
                                   protocol_hint: str = "generic",
                                   data_width: int = 32,
                                   addr_width: int = 32) -> FieldConfig:
    """
    Create a FieldConfig from a list of signal names with protocol awareness.

    Args:
        signal_list: List of signal names
        protocol_hint: Protocol hint for better field configuration
        data_width: Default data width
        addr_width: Default address width

    Returns:
        FieldConfig object
    """
    config = FieldConfig()

    for signal_name in signal_list:
        # Extract field name (remove prefix)
        field_name = signal_name
        if '_' in signal_name:
            field_name = signal_name.split('_')[-1]

        # Determine field properties based on name and protocol
        field_def = _create_field_definition_from_signal(field_name, signal_name, protocol_hint, data_width, addr_width)

        if field_def:
            config.add_field(field_def)

    return config


def _create_field_definition_from_signal(field_name: str, full_signal_name: str,
                                        protocol_hint: str, data_width: int,
                                        addr_width: int) -> FieldDefinition:
    """Create FieldDefinition from signal name with protocol awareness"""
    signal_lower = field_name.lower()
    full_signal_lower = full_signal_name.lower()

    # Protocol-specific field definitions
    if protocol_hint.lower() == "apb":
        return _create_apb_field_definition(field_name, signal_lower, data_width, addr_width)
    elif protocol_hint.lower() == "axi":
        return _create_axi_field_definition(field_name, signal_lower, data_width, addr_width)
    elif protocol_hint.lower() == "gaxi":
        return _create_gaxi_field_definition(field_name, signal_lower, data_width, addr_width)
    else:
        return _create_generic_field_definition(field_name, signal_lower, data_width, addr_width)


def _create_apb_field_definition(field_name: str, signal_lower: str,
                                data_width: int, addr_width: int) -> FieldDefinition:
    """Create APB-specific field definition"""

    # APB control signals
    if signal_lower in ['psel', 'penable', 'pready', 'pwrite', 'pslverr']:
        return FieldDefinition(
            name=field_name,
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description=_get_apb_signal_description(signal_lower)
        )

    # APB address
    elif signal_lower in ['paddr']:
        return FieldDefinition(
            name=field_name,
            bits=addr_width,
            default=0,
            format="hex",
            display_width=8,
            description="Address"
        )

    # APB data
    elif signal_lower in ['pwdata', 'prdata']:
        data_type = "Write Data" if 'w' in signal_lower else "Read Data"
        return FieldDefinition(
            name=field_name,
            bits=data_width,
            default=0,
            format="hex",
            display_width=8,
            description=data_type
        )

    # APB strobe
    elif signal_lower in ['pstrb']:
        return FieldDefinition(
            name=field_name,
            bits=data_width // 8,
            default=0,
            format="bin",
            display_width=data_width // 8,
            description="Write Strobes"
        )

    # APB protection
    elif signal_lower in ['pprot']:
        return FieldDefinition(
            name=field_name,
            bits=3,
            default=0,
            format="hex",
            display_width=1,
            description="Protection Control"
        )

    else:
        return _create_generic_field_definition(field_name, signal_lower, data_width, addr_width)


def _create_axi_field_definition(field_name: str, signal_lower: str,
                                data_width: int, addr_width: int) -> FieldDefinition:
    """Create AXI-specific field definition"""

    # AXI handshake signals
    if 'valid' in signal_lower or 'ready' in signal_lower:
        return FieldDefinition(
            name=field_name,
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description=_get_axi_signal_description(signal_lower)
        )

    # AXI address signals
    elif 'addr' in signal_lower:
        return FieldDefinition(
            name=field_name,
            bits=addr_width,
            default=0,
            format="hex",
            display_width=8,
            description="Address"
        )

    # AXI data signals
    elif 'data' in signal_lower:
        return FieldDefinition(
            name=field_name,
            bits=data_width,
            default=0,
            format="hex",
            display_width=8,
            description="Data"
        )

    # AXI length signals
    elif 'len' in signal_lower:
        return FieldDefinition(
            name=field_name,
            bits=8,
            default=0,
            format="dec",
            display_width=3,
            description="Burst Length"
        )

    # AXI size signals
    elif 'size' in signal_lower:
        return FieldDefinition(
            name=field_name,
            bits=3,
            default=0,
            format="dec",
            display_width=1,
            description="Burst Size"
        )

    # AXI response signals
    elif 'resp' in signal_lower:
        encoding = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        return FieldDefinition(
            name=field_name,
            bits=2,
            default=0,
            format="hex",
            display_width=1,
            description="Response",
            encoding=encoding
        )

    # AXI strobe signals
    elif 'strb' in signal_lower:
        return FieldDefinition(
            name=field_name,
            bits=data_width // 8,
            default=0,
            format="bin",
            display_width=data_width // 8,
            description="Write Strobes"
        )

    # AXI last signal
    elif 'last' in signal_lower:
        return FieldDefinition(
            name=field_name,
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Last Transfer"
        )

    else:
        return _create_generic_field_definition(field_name, signal_lower, data_width, addr_width)


def _create_gaxi_field_definition(field_name: str, signal_lower: str,
                                 data_width: int, addr_width: int) -> FieldDefinition:
    """Create GAXI-specific field definition"""

    # GAXI handshake signals
    if signal_lower in ['valid', 'ready']:
        return FieldDefinition(
            name=field_name,
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description=f"GAXI {field_name.title()}"
        )

    # GAXI command
    elif signal_lower in ['cmd']:
        encoding = {0: "READ", 1: "WRITE"}
        return FieldDefinition(
            name=field_name,
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Command",
            encoding=encoding
        )

    # GAXI address
    elif signal_lower in ['addr']:
        return FieldDefinition(
            name=field_name,
            bits=addr_width,
            default=0,
            format="hex",
            display_width=8,
            description="Address"
        )

    # GAXI data
    elif signal_lower in ['data']:
        return FieldDefinition(
            name=field_name,
            bits=data_width,
            default=0,
            format="hex",
            display_width=8,
            description="Data"
        )

    # GAXI strobe
    elif signal_lower in ['strb']:
        return FieldDefinition(
            name=field_name,
            bits=data_width // 8,
            default=0,
            format="bin",
            display_width=data_width // 8,
            description="Byte Strobe"
        )

    # GAXI response
    elif signal_lower in ['resp', 'err']:
        return FieldDefinition(
            name=field_name,
            bits=1,
            default=0,
            format="dec",
            display_width=1,
            description="Error Response"
        )

    else:
        return _create_generic_field_definition(field_name, signal_lower, data_width, addr_width)


def _create_generic_field_definition(field_name: str, signal_lower: str,
                                    data_width: int, addr_width: int) -> FieldDefinition:
    """Create generic field definition"""

    # Determine bit width based on signal name patterns
    if 'clk' in signal_lower or 'clock' in signal_lower:
        bits = 1
        format_style = "dec"
        description = "Clock"
    elif 'reset' in signal_lower or 'rst' in signal_lower:
        bits = 1
        format_style = "dec"
        description = "Reset"
    elif 'addr' in signal_lower:
        bits = addr_width
        format_style = "hex"
        description = "Address"
    elif 'data' in signal_lower:
        bits = data_width
        format_style = "hex"
        description = "Data"
    elif 'strb' in signal_lower or 'mask' in signal_lower:
        bits = data_width // 8
        format_style = "bin"
        description = "Strobe/Mask"
    elif 'len' in signal_lower:
        bits = 8
        format_style = "dec"
        description = "Length"
    elif 'size' in signal_lower:
        bits = 3
        format_style = "dec"
        description = "Size"
    elif 'id' in signal_lower:
        bits = 4
        format_style = "hex"
        description = "ID"
    else:
        # Default to single bit
        bits = 1
        format_style = "dec"
        description = field_name.replace('_', ' ').title()

    return FieldDefinition(
        name=field_name,
        bits=bits,
        default=0,
        format=format_style,
        display_width=_calculate_display_width(bits, format_style),
        description=description
    )


def _get_apb_signal_description(signal_name: str) -> str:
    """Get APB signal description"""
    descriptions = {
        'psel': 'Peripheral Select',
        'penable': 'Enable',
        'pready': 'Ready',
        'pwrite': 'Write Enable (0=Read, 1=Write)',
        'pslverr': 'Slave Error'
    }
    return descriptions.get(signal_name, signal_name.replace('_', ' ').title())


def _get_axi_signal_description(signal_name: str) -> str:
    """Get AXI signal description"""
    if 'awvalid' in signal_name:
        return 'Write Address Valid'
    elif 'awready' in signal_name:
        return 'Write Address Ready'
    elif 'wvalid' in signal_name:
        return 'Write Data Valid'
    elif 'wready' in signal_name:
        return 'Write Data Ready'
    elif 'bvalid' in signal_name:
        return 'Write Response Valid'
    elif 'bready' in signal_name:
        return 'Write Response Ready'
    elif 'arvalid' in signal_name:
        return 'Read Address Valid'
    elif 'arready' in signal_name:
        return 'Read Address Ready'
    elif 'rvalid' in signal_name:
        return 'Read Data Valid'
    elif 'rready' in signal_name:
        return 'Read Data Ready'
    else:
        return signal_name.replace('_', ' ').title()


def _calculate_display_width(bits: int, format_style: str) -> int:
    """Calculate display width for a field"""
    if format_style == "bin":
        return bits
    elif format_style == "hex":
        return (bits + 3) // 4
    else:  # decimal
        return len(str(2**bits - 1))


def create_debug_constraint(signal: str,
                           name: str = None,
                           max_window: int = 30,
                           clock_group: str = "default",
                           signals_to_show: List[str] = None,
                           field_config: Optional[FieldConfig] = None):
    """
    Create debug constraint for signal activity with FieldConfig integration.

    Args:
        signal: Signal name to debug
        name: Constraint name (auto-generated if None)
        max_window: Maximum window size
        clock_group: Clock group name
        signals_to_show: Additional signals to show
        field_config: FieldConfig for configuration

    Returns:
        TemporalConstraint for debugging
    """
    from .constraint_solver import TemporalConstraint, TemporalRelation

    if name is None:
        name = f"debug_{signal.replace('_', '').lower()}"

    if signals_to_show is None:
        signals_to_show = [signal]

    # Create events for transitions
    events = [
        create_temporal_event("rising_edge", create_transition_pattern(signal, 0, 1)),
        create_temporal_event("falling_edge", create_transition_pattern(signal, 1, 0))
    ]

    return TemporalConstraint(
        name=name,
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=False,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        field_config=field_config,
        protocol_hint="debug"
    )


def create_wavejson_from_packet_and_signals(packet_obj,
                                                    signal_data: Dict[str, List[int]],
                                                    temporal_solution: Dict[str, Any] = None,
                                                    title: str = None,
                                                    interface_prefix: str = "") -> Dict[str, Any]:
    """
    Create WaveJSON from packet object and signal data with temporal annotations.

    Args:
        packet_obj: Packet object with FieldConfig
        signal_data: Signal timing data
        temporal_solution: Optional temporal solution for annotations
        title: Optional title
        interface_prefix: Signal name prefix

    Returns:
        Complete WaveJSON dictionary
    """
    # Create temporal annotations if solution provided
    annotations = []
    if temporal_solution:
        annotations = create_temporal_annotations_from_solution(temporal_solution)

    # Generate WaveJSON using the function
    generator = WaveJSONGenerator(debug_level=1)
    generator.configure_packet_signals(packet_obj, interface_prefix)

    # Generate title if not provided
    if title is None:
        protocol_name = packet_obj.__class__.__name__.replace('Packet', '')
        seq_info = ""
        if temporal_solution:
            duration = temporal_solution.get('sequence_duration', 0)
            seq_info = f" ({duration} cycles)"
        title = f"{protocol_name} Transaction{seq_info}"

    # Generate WaveJSON with annotations
    wavejson = generator.generate_wavejson(
        signal_data=signal_data,
        title=title,
        temporal_annotations=annotations,
        protocol_hint=packet_obj.__class__.__name__.replace('Packet', '').lower()
    )

    return wavejson


def create_protocol_specific_field_config(protocol_name: str,
                                         data_width: int = 32,
                                         addr_width: int = 32,
                                         **kwargs) -> FieldConfig:
    """
    Create protocol-specific FieldConfig with standard field definitions.

    Args:
        protocol_name: Protocol name (apb, axi, gaxi)
        data_width: Data width in bits
        addr_width: Address width in bits
        **kwargs: Additional protocol-specific parameters

    Returns:
        FieldConfig object
    """
    protocol_lower = protocol_name.lower()

    if protocol_lower == "apb":
        return _create_apb_field_config(data_width, addr_width, **kwargs)
    elif protocol_lower == "axi":
        return _create_axi_field_config(data_width, addr_width, **kwargs)
    elif protocol_lower == "gaxi":
        return _create_gaxi_field_config(data_width, addr_width, **kwargs)
    else:
        # Generic protocol
        return _create_generic_field_config(data_width, addr_width, **kwargs)


def _create_apb_field_config(data_width: int, addr_width: int, **kwargs) -> FieldConfig:
    """Create APB-specific FieldConfig"""
    config = FieldConfig()

    # APB control signals
    config.add_field(FieldDefinition(
        name="psel", bits=1, default=0, format="dec", description="psel"
    ))
    config.add_field(FieldDefinition(
        name="penable", bits=1, default=0, format="dec", description="penable"
    ))
    config.add_field(FieldDefinition(
        name="pready", bits=1, default=0, format="dec", description="pready"
    ))
    config.add_field(FieldDefinition(
        name="pwrite", bits=1, default=0, format="dec", description="pwrite",
        encoding={0: "READ", 1: "WRITE"}
    ))

    # APB address and data
    config.add_field(FieldDefinition(
        name="paddr", bits=addr_width, default=0, format="hex", description="paddr"
    ))
    config.add_field(FieldDefinition(
        name="pwdata", bits=data_width, default=0, format="hex", description="pwdata"
    ))
    config.add_field(FieldDefinition(
        name="prdata", bits=data_width, default=0, format="hex", description="prdata"
    ))

    # APB strobe and protection
    strb_width = data_width // 8
    config.add_field(FieldDefinition(
        name="pstrb", bits=strb_width, default=0, format="bin", description="pstrb"
    ))
    config.add_field(FieldDefinition(
        name="pprot", bits=3, default=0, format="hex", description="pprot"
    ))
    config.add_field(FieldDefinition(
        name="pslverr", bits=1, default=0, format="dec", description="pslverr"
    ))

    return config


def _create_axi_field_config(data_width: int, addr_width: int, **kwargs) -> FieldConfig:
    """Create AXI-specific FieldConfig"""
    config = FieldConfig()

    # AXI Write Address Channel
    config.add_field(FieldDefinition(
        name="awvalid", bits=1, default=0, format="dec", description="awvalid"
    ))
    config.add_field(FieldDefinition(
        name="awready", bits=1, default=0, format="dec", description="awready"
    ))
    config.add_field(FieldDefinition(
        name="awaddr", bits=addr_width, default=0, format="hex", description="awaddr"
    ))
    config.add_field(FieldDefinition(
        name="awlen", bits=8, default=0, format="dec", description="awlen"
    ))
    config.add_field(FieldDefinition(
        name="awsize", bits=3, default=0, format="dec", description="awsize"
    ))

    # AXI Write Data Channel
    config.add_field(FieldDefinition(
        name="wvalid", bits=1, default=0, format="dec", description="wvalid"
    ))
    config.add_field(FieldDefinition(
        name="wready", bits=1, default=0, format="dec", description="wready"
    ))
    config.add_field(FieldDefinition(
        name="wdata", bits=data_width, default=0, format="hex", description="wdata"
    ))
    config.add_field(FieldDefinition(
        name="wstrb", bits=data_width//8, default=0, format="bin", description="wstrb"
    ))
    config.add_field(FieldDefinition(
        name="wlast", bits=1, default=0, format="dec", description="wlast"
    ))

    # AXI Write Response Channel
    config.add_field(FieldDefinition(
        name="bvalid", bits=1, default=0, format="dec", description="bvalid"
    ))
    config.add_field(FieldDefinition(
        name="bready", bits=1, default=0, format="dec", description="bready"
    ))
    config.add_field(FieldDefinition(
        name="bresp", bits=2, default=0, format="hex", description="bresp",
        encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
    ))

    # AXI Read Address Channel
    config.add_field(FieldDefinition(
        name="arvalid", bits=1, default=0, format="dec", description="arvalid"
    ))
    config.add_field(FieldDefinition(
        name="arready", bits=1, default=0, format="dec", description="arready"
    ))
    config.add_field(FieldDefinition(
        name="araddr", bits=addr_width, default=0, format="hex", description="araddr"
    ))
    config.add_field(FieldDefinition(
        name="arlen", bits=8, default=0, format="dec", description="arlen"
    ))
    config.add_field(FieldDefinition(
        name="arsize", bits=3, default=0, format="dec", description="arsize"
    ))

    # AXI Read Data Channel
    config.add_field(FieldDefinition(
        name="rvalid", bits=1, default=0, format="dec", description="rvalid"
    ))
    config.add_field(FieldDefinition(
        name="rready", bits=1, default=0, format="dec", description="rready"
    ))
    config.add_field(FieldDefinition(
        name="rdata", bits=data_width, default=0, format="hex", description="rdata"
    ))
    config.add_field(FieldDefinition(
        name="rresp", bits=2, default=0, format="hex", description="rresp",
        encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
    ))
    config.add_field(FieldDefinition(
        name="rlast", bits=1, default=0, format="dec", description="rlast"
    ))

    return config


def _create_gaxi_field_config(data_width: int, addr_width: int, **kwargs) -> FieldConfig:
    """Create GAXI-specific FieldConfig"""
    config = FieldConfig()

    # GAXI handshake
    config.add_field(FieldDefinition(
        name="valid", bits=1, default=0, format="dec", description="valid"
    ))
    config.add_field(FieldDefinition(
        name="ready", bits=1, default=0, format="dec", description="ready"
    ))

    # GAXI command and address
    config.add_field(FieldDefinition(
        name="cmd", bits=1, default=0, format="dec", description="cmd",
        encoding={0: "READ", 1: "WRITE"}
    ))
    config.add_field(FieldDefinition(
        name="addr", bits=addr_width, default=0, format="hex", description="addr"
    ))

    # GAXI data and strobe
    config.add_field(FieldDefinition(
        name="data", bits=data_width, default=0, format="hex", description="data"
    ))
    config.add_field(FieldDefinition(
        name="strb", bits=data_width//8, default=0, format="bin", description="strb"
    ))

    # GAXI response
    config.add_field(FieldDefinition(
        name="resp", bits=1, default=0, format="dec", description="resp"
    ))

    return config


def _create_generic_field_config(data_width: int, addr_width: int, **kwargs) -> FieldConfig:
    """Create generic FieldConfig"""
    config = FieldConfig()

    # Basic fields
    config.add_field(FieldDefinition(
        name="data", bits=data_width, default=0, format="hex", description="data"
    ))

    return config


# Helper function that was missing but referenced in APB module
def get_apb_field_config(data_width: int = 32, addr_width: int = 32, strb_width: int = 4,
                        use_signal_names: bool = True) -> FieldConfig:
    """
    Get APB FieldConfig for signal configuration.

    Args:
        data_width: Data width in bits
        addr_width: Address width in bits
        strb_width: Strobe width in bits
        use_signal_names: If True, use actual signal names; if False, use descriptions
    """
    config = FieldConfig()

    # Configure field names vs descriptions based on preference
    if use_signal_names:
        # Use actual signal names for display
        signal_configs = [
            ("psel", 1, "dec", "psel"),
            ("penable", 1, "dec", "penable"),
            ("pready", 1, "dec", "pready"),
            ("pwrite", 1, "dec", "pwrite", {0: "READ", 1: "WRITE"}),
            ("paddr", addr_width, "hex", "paddr"),
            ("pwdata", data_width, "hex", "pwdata"),
            ("prdata", data_width, "hex", "prdata"),
            ("pstrb", strb_width, "bin", "pstrb"),
            ("pprot", 3, "hex", "pprot"),
            ("pslverr", 1, "dec", "pslverr")
        ]
    else:
        # Use descriptive names for display
        signal_configs = [
            ("psel", 1, "dec", "Peripheral Select"),
            ("penable", 1, "dec", "Enable"),
            ("pready", 1, "dec", "Ready"),
            ("pwrite", 1, "dec", "Write Enable", {0: "READ", 1: "WRITE"}),
            ("paddr", addr_width, "hex", "Address"),
            ("pwdata", data_width, "hex", "Write Data"),
            ("prdata", data_width, "hex", "Read Data"),
            ("pstrb", strb_width, "bin", "Write Strobes"),
            ("pprot", 3, "hex", "Protection Control"),
            ("pslverr", 1, "dec", "Slave Error")
        ]

    # Add fields to config
    for field_data in signal_configs:
        name, bits, format_type, description = field_data[:4]
        encoding = field_data[4] if len(field_data) > 4 else None

        config.add_field(FieldDefinition(
            name=name,
            bits=bits,
            default=0,
            format=format_type,
            description=description,
            encoding=encoding
        ))

    return config


# Export all utility functions
__all__ = [
    # Pattern creation
    'create_transition_pattern',
    'create_static_pattern',
    'create_temporal_event',

    # Annotation utilities
    'create_temporal_annotations_from_solution',

    # FieldConfig utilities
    'create_fieldconfig_from_signals',
    'create_protocol_specific_field_config',
    'get_apb_field_config',

    # Debug utilities
    'create_debug_constraint',

    # WaveJSON utilities
    'create_wavejson_from_packet_and_signals',
]
