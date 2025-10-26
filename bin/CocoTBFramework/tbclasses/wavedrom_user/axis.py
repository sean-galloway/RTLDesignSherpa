# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISPresets
# Purpose: AXI-Stream (AXIS) Constraints with Temporal Pattern Detection
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI-Stream (AXIS) Constraints with Temporal Pattern Detection

Provides constraint patterns, field configurations, and templates for AXI-Stream
protocol waveform generation using WaveDrom and temporal constraint solving.

AXI-Stream Protocol:
- Single channel with valid/ready handshake
- Data streaming with optional TLAST, TKEEP, TSTRB, TID, TDEST, TUSER
- No address phase (stream-oriented, not memory-mapped)
- Supports back-to-back transfers and backpressure

Key Features:
1. Stream handshake detection (tvalid/tready)
2. Packet boundary detection (TLAST)
3. Byte lane support (TKEEP/TSTRB)
4. ID/DEST routing support
5. Burst and throughput analysis

Usage Patterns:
- Simple stream: {tvalid, tready, tdata}
- Packet stream: {tvalid, tready, tdata, tlast}
- Full stream: {tvalid, tready, tdata, tkeep, tstrb, tlast, tid, tdest, tuser}
"""

from typing import List, Dict, Optional, Any
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraint, TemporalEvent, SignalTransition, SignalStatic, TemporalRelation,
    TemporalConstraintSolver
)
from CocoTBFramework.components.wavedrom.utility import (
    create_transition_pattern, create_static_pattern, create_temporal_event,
    create_debug_constraint
)

# Required imports
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator


# ==============================================================================
# AXI-Stream Field Configuration Generators
# ==============================================================================

def get_axis_field_config(data_width: int = 32,
                          id_width: int = 0,
                          dest_width: int = 0,
                          user_width: int = 0,
                          include_tkeep: bool = True,
                          include_tstrb: bool = False,
                          include_tlast: bool = True) -> FieldConfig:
    """
    Create AXI-Stream field configuration.

    AXI-Stream signals:
    - tvalid, tready (required handshake)
    - tdata (required)
    - tlast (optional, marks end of packet)
    - tkeep (optional, byte valid indicators)
    - tstrb (optional, byte strobe - deprecated, use tkeep)
    - tid (optional, stream ID for routing)
    - tdest (optional, destination routing)
    - tuser (optional, user-defined sideband)

    Args:
        data_width: Width of TDATA (8, 16, 32, 64, 128, 256, 512, 1024)
        id_width: Width of TID (0 = no ID, default: 0)
        dest_width: Width of TDEST (0 = no DEST, default: 0)
        user_width: Width of TUSER (0 = no USER, default: 0)
        include_tkeep: Include TKEEP signal (default: True)
        include_tstrb: Include TSTRB signal (default: False)
        include_tlast: Include TLAST signal (default: True)

    Returns:
        FieldConfig for AXI-Stream

    Example:
        # Simple stream
        config = get_axis_field_config(data_width=32, include_tlast=True)

        # Complex stream with routing
        config = get_axis_field_config(data_width=64, id_width=4, dest_width=4,
                                       user_width=8, include_tkeep=True, include_tlast=True)
    """
    config = FieldConfig()

    # Core handshake signals
    config.add_field(FieldDefinition('valid', 1, description='Valid signal'))
    config.add_field(FieldDefinition('ready', 1, description='Ready signal'))

    # Data signal
    config.add_field(FieldDefinition('data', data_width, format='hex', description=f'Data [{data_width-1}:0]'))

    # Optional byte lane signals
    if include_tkeep:
        keep_width = data_width // 8
        config.add_field(FieldDefinition('keep', keep_width, format='bin', description=f'Keep [{keep_width-1}:0]'))

    if include_tstrb:
        strb_width = data_width // 8
        config.add_field(FieldDefinition('strb', strb_width, format='bin', description=f'Strobe [{strb_width-1}:0]'))

    # Packet boundary
    if include_tlast:
        config.add_field(FieldDefinition('last', 1, format='bin', description='Last (end of packet)',
                                        encoding={0: 'Not Last', 1: 'Last'}))

    # Routing signals
    if id_width > 0:
        config.add_field(FieldDefinition('id', id_width, format='hex', description=f'ID [{id_width-1}:0]'))

    if dest_width > 0:
        config.add_field(FieldDefinition('dest', dest_width, format='hex', description=f'Dest [{dest_width-1}:0]'))

    # User sideband
    if user_width > 0:
        config.add_field(FieldDefinition('user', user_width, format='bin', description=f'User [{user_width-1}:0]'))

    return config


def create_axis_wavejson_generator(field_config: FieldConfig,
                                   signal_prefix: str = "axis_",
                                   group_name: str = "AXI-Stream") -> WaveJSONGenerator:
    """
    Create WaveJSON generator for AXI-Stream with field configuration.

    Args:
        field_config: AXI-Stream field configuration
        signal_prefix: Prefix for signal names (default: "axis_")
        group_name: Group name in waveform (default: "AXI-Stream")

    Returns:
        Configured WaveJSONGenerator
    """
    generator = WaveJSONGenerator()

    # Create signal names: axis_tvalid, axis_tready, axis_tdata, axis_tlast, etc.
    signal_names = []
    for field in field_config.fields():
        if field.name in ['valid', 'ready']:
            signal_names.append(f"{signal_prefix}t{field.name}")
        else:
            signal_names.append(f"{signal_prefix}t{field.name}")

    generator.add_interface_group(group_name, signal_names)
    generator.configure_from_field_config(field_config, protocol_name="axis")

    return generator


# ==============================================================================
# AXI-Stream Constraint Patterns
# ==============================================================================

def create_axis_handshake_constraint(signal_prefix: str = "axis_",
                                     max_window: int = 30,
                                     required: bool = True,
                                     clock_group: str = "default",
                                     field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create basic AXI-Stream handshake constraint.

    Detects: tvalid(0→1) → tready(0→1) sequence

    Args:
        signal_prefix: Prefix for signal names (default: "axis_")
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for stream handshake detection
    """
    tvalid_sig = f"{signal_prefix}tvalid"
    tready_sig = f"{signal_prefix}tready"

    events = [
        create_temporal_event("tvalid_start", create_transition_pattern(tvalid_sig, 0, 1)),
        create_temporal_event("tready_response", create_transition_pattern(tready_sig, 0, 1))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}t{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [tvalid_sig, tready_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}handshake",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axis"
    )


def create_axis_packet_constraint(signal_prefix: str = "axis_",
                                  max_window: int = 50,
                                  required: bool = True,
                                  clock_group: str = "default",
                                  field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI-Stream packet constraint (detects TLAST).

    Detects: tvalid=1, tready=1, tlast=1 (end of packet transfer)

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for packet end detection
    """
    tvalid_sig = f"{signal_prefix}tvalid"
    tready_sig = f"{signal_prefix}tready"
    tlast_sig = f"{signal_prefix}tlast"

    events = [
        create_temporal_event("tvalid_high", create_static_pattern(tvalid_sig, 1)),
        create_temporal_event("tready_high", create_static_pattern(tready_sig, 1)),
        create_temporal_event("tlast_assert", create_transition_pattern(tlast_sig, 0, 1))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}t{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [tvalid_sig, tready_sig, tlast_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}packet",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axis"
    )


def create_axis_back2back_constraint(signal_prefix: str = "axis_",
                                     max_window: int = 10,
                                     clock_group: str = "default",
                                     field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create constraint for back-to-back AXI-Stream transfers.

    Detects: Multiple tvalid/tready handshakes with no idle cycles

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum window for detection
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for back-to-back detection
    """
    tvalid_sig = f"{signal_prefix}tvalid"
    tready_sig = f"{signal_prefix}tready"

    events = [
        create_temporal_event("handshake", create_static_pattern(tvalid_sig, 1)),
        create_temporal_event("ready", create_static_pattern(tready_sig, 1))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}t{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [tvalid_sig, tready_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}back2back",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=False,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=2,
        max_sequence_duration=max_window - 2,
        field_config=field_config,
        protocol_hint="axis"
    )


def create_axis_stall_constraint(signal_prefix: str = "axis_",
                                 max_window: int = 50,
                                 clock_group: str = "default",
                                 field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create constraint for AXI-Stream stall condition (backpressure).

    Detects: tvalid=1, tready=0 (receiver applying backpressure)

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum stall duration to detect
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for stall detection
    """
    tvalid_sig = f"{signal_prefix}tvalid"
    tready_sig = f"{signal_prefix}tready"

    events = [
        create_temporal_event("tvalid_asserted", create_transition_pattern(tvalid_sig, 0, 1)),
        create_temporal_event("tready_low", create_static_pattern(tready_sig, 0))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}t{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [tvalid_sig, tready_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}stall",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=False,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axis"
    )


def create_axis_idle_constraint(signal_prefix: str = "axis_",
                                max_window: int = 20,
                                clock_group: str = "default",
                                field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create constraint for AXI-Stream idle state.

    Detects: Both tvalid and tready low (idle stream)

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum idle period to detect
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for idle detection
    """
    tvalid_sig = f"{signal_prefix}tvalid"
    tready_sig = f"{signal_prefix}tready"

    events = [
        create_temporal_event("tvalid_idle", create_static_pattern(tvalid_sig, 0)),
        create_temporal_event("tready_idle", create_static_pattern(tready_sig, 0))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}t{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [tvalid_sig, tready_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}idle",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=False,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 2,
        field_config=field_config,
        protocol_hint="axis"
    )


# ==============================================================================
# AXI-Stream Boundary Patterns
# ==============================================================================

def get_axis_boundary_pattern(signal_prefix: str = "axis_") -> Dict[str, int]:
    """
    Get AXI-Stream boundary reset pattern (idle state).

    Args:
        signal_prefix: Signal name prefix

    Returns:
        Dictionary of signal: value pairs for idle state
    """
    return {
        f"{signal_prefix}tvalid": 0,
        f"{signal_prefix}tready": 0
    }


def setup_axis_boundaries(wave_solver: TemporalConstraintSolver,
                          constraint_names: List[str],
                          signal_prefix: str = "axis_",
                          field_config: Optional[FieldConfig] = None):
    """
    Configure AXI-Stream transaction boundaries.

    Uses tvalid falling edge as transaction boundary trigger.

    Args:
        wave_solver: TemporalConstraintSolver instance
        constraint_names: Constraint names to configure
        signal_prefix: Signal name prefix
        field_config: Optional FieldConfig for protocol configuration
    """
    tvalid_sig = f"{signal_prefix}tvalid"

    for constraint_name in constraint_names:
        wave_solver.auto_detect_boundaries(
            constraint_name=constraint_name,
            transition_signal=tvalid_sig,
            transition_value=(1, 0),  # tvalid high→low (end of transfer)
            reset_signals=get_axis_boundary_pattern(signal_prefix)
        )

        if field_config and hasattr(wave_solver, 'configure_from_field_config'):
            wave_solver.configure_from_field_config(field_config, protocol_name="axis")


# ==============================================================================
# AXI-Stream Preset Configurations
# ==============================================================================

class AXISPresets:
    """Predefined AXI-Stream constraint configurations for common use cases"""

    @staticmethod
    def basic_handshake(signal_prefix: str = "axis_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Basic handshake detection preset.

        Use case: Verify stream transfers are occurring

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_axis_handshake_constraint(signal_prefix=signal_prefix, field_config=field_config)
        }

    @staticmethod
    def comprehensive(signal_prefix: str = "axis_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Comprehensive AXI-Stream analysis preset.

        Detects: handshakes, packets, back-to-back, stalls, idle periods

        Use case: Full stream behavior analysis

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_axis_handshake_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'packet': create_axis_packet_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'back2back': create_axis_back2back_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'stall': create_axis_stall_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'idle': create_axis_idle_constraint(signal_prefix=signal_prefix, field_config=field_config)
        }

    @staticmethod
    def performance(signal_prefix: str = "axis_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Performance analysis preset.

        Focus: Throughput, stalls, back-to-back efficiency

        Use case: Performance optimization

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_axis_handshake_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'back2back': create_axis_back2back_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'stall': create_axis_stall_constraint(signal_prefix=signal_prefix, max_window=100, field_config=field_config)
        }

    @staticmethod
    def debug(signal_prefix: str = "axis_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Debug preset with extended windows.

        Use case: Debugging stuck or misbehaving stream interfaces

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_axis_handshake_constraint(signal_prefix=signal_prefix, max_window=100, field_config=field_config),
            'stall': create_axis_stall_constraint(signal_prefix=signal_prefix, max_window=200, field_config=field_config),
            'idle': create_axis_idle_constraint(signal_prefix=signal_prefix, max_window=50, field_config=field_config)
        }


# ==============================================================================
# Convenience Functions for Quick Setup
# ==============================================================================

def setup_axis_constraints_with_boundaries(wave_solver: TemporalConstraintSolver,
                                           preset_name: str = "basic_handshake",
                                           signal_prefix: str = "axis_",
                                           data_width: int = 32,
                                           id_width: int = 0,
                                           dest_width: int = 0,
                                           user_width: int = 0,
                                           include_tkeep: bool = True,
                                           include_tlast: bool = True) -> int:
    """
    One-stop setup for AXI-Stream wavedrom with all configuration.

    Args:
        wave_solver: TemporalConstraintSolver instance
        preset_name: Preset name ("basic_handshake", "comprehensive", "performance", "debug")
        signal_prefix: Signal name prefix (default: "axis_")
        data_width: Width of TDATA
        id_width: Width of TID (0 = no ID)
        dest_width: Width of TDEST (0 = no DEST)
        user_width: Width of TUSER (0 = no USER)
        include_tkeep: Include TKEEP signal
        include_tlast: Include TLAST signal

    Returns:
        Number of constraints added

    Example:
        num_constraints = setup_axis_constraints_with_boundaries(
            wave_solver=wave_solver,
            preset_name="comprehensive",
            signal_prefix="axis_",
            data_width=64,
            include_tlast=True
        )
    """
    # Create field config
    field_config = get_axis_field_config(
        data_width=data_width,
        id_width=id_width,
        dest_width=dest_width,
        user_width=user_width,
        include_tkeep=include_tkeep,
        include_tlast=include_tlast
    )

    # Get preset constraints
    presets = AXISPresets()
    if not hasattr(presets, preset_name):
        raise ValueError(f"Unknown preset: {preset_name}. "
                        f"Available: basic_handshake, comprehensive, performance, debug")

    constraints_dict = getattr(presets, preset_name)(signal_prefix=signal_prefix, field_config=field_config)

    # Add constraints to solver
    constraint_names = []
    for name, constraint in constraints_dict.items():
        wave_solver.add_constraint(constraint)
        constraint_names.append(constraint.name)

    # Setup boundaries
    setup_axis_boundaries(wave_solver, constraint_names, signal_prefix, field_config)

    return len(constraints_dict)


# Export classes and functions
__all__ = [
    # Field config helpers
    'get_axis_field_config',
    'create_axis_wavejson_generator',

    # Constraint builders
    'create_axis_handshake_constraint',
    'create_axis_packet_constraint',
    'create_axis_back2back_constraint',
    'create_axis_stall_constraint',
    'create_axis_idle_constraint',

    # Boundary management
    'get_axis_boundary_pattern',
    'setup_axis_boundaries',

    # Preset class
    'AXISPresets',

    # Setup function
    'setup_axis_constraints_with_boundaries',
]
