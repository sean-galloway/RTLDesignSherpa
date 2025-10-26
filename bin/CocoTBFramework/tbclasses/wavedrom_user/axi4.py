# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4Presets
# Purpose: AXI4 Constraints with Temporal Pattern Detection
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Constraints with Temporal Pattern Detection

Provides constraint patterns, field configurations, and templates for AXI4
protocol waveform generation using WaveDrom and temporal constraint solving.

AXI4 Protocol:
- 5 independent channels: AW (Write Address), W (Write Data), B (Write Response),
  AR (Read Address), R (Read Data)
- Each channel has valid/ready handshake
- Supports bursts, out-of-order transactions, and multiple outstanding requests

Key Features:
1. Per-channel constraint patterns (AW, W, B, AR, R)
2. Burst sequence detection (address → data → response)
3. ID-based transaction tracking
4. Protocol compliance checking

Usage Patterns:
- Write transaction: AW handshake → W data transfers → B response
- Read transaction: AR handshake → R data transfers
- Burst analysis: Detect WLAST/RLAST signals
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
from CocoTBFramework.components.axi4.axi4_field_configs import get_axi4_field_configs


# ==============================================================================
# AXI4 Field Configuration Generators (Channel-Specific)
# ==============================================================================

def get_axi4_channel_field_config(channel: str,
                                   id_width: int = 8,
                                   addr_width: int = 32,
                                   data_width: int = 32,
                                   user_width: int = 0) -> FieldConfig:
    """
    Create AXI4 field configuration for a specific channel.

    Args:
        channel: Channel name ('AW', 'W', 'B', 'AR', 'R')
        id_width: Width of ID fields (default: 8)
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)
        user_width: Width of user fields (0 = no user signals, default: 0)

    Returns:
        FieldConfig for specified channel

    Example:
        aw_config = get_axi4_channel_field_config('AW', id_width=4, addr_width=32)
    """
    configs = get_axi4_field_configs(id_width, addr_width, data_width, user_width, [channel])
    return configs[channel]


def create_axi4_wavejson_generator(channel: str,
                                   field_config: FieldConfig,
                                   signal_prefix: str = "m_axi_",
                                   group_name: Optional[str] = None) -> WaveJSONGenerator:
    """
    Create WaveJSON generator for AXI4 channel with field configuration.

    Args:
        channel: Channel name ('AW', 'W', 'B', 'AR', 'R')
        field_config: Channel field configuration
        signal_prefix: Prefix for signal names (default: "m_axi_")
        group_name: Group name in waveform (default: "AXI4 {channel}")

    Returns:
        Configured WaveJSONGenerator
    """
    generator = WaveJSONGenerator()

    if group_name is None:
        group_name = f"AXI4 {channel}"

    # Map channel to signal prefix
    channel_prefix_map = {
        'AW': 'aw', 'W': 'w', 'B': 'b',
        'AR': 'ar', 'R': 'r'
    }
    ch_prefix = channel_prefix_map.get(channel, channel.lower())

    # Create signal names: m_axi_awvalid, m_axi_awready, m_axi_awid, etc.
    signal_names = [f"{signal_prefix}{ch_prefix}valid", f"{signal_prefix}{ch_prefix}ready"]
    for field in field_config.fields():
        if field.name not in ['valid', 'ready']:
            signal_names.append(f"{signal_prefix}{ch_prefix}{field.name}")

    generator.add_interface_group(group_name, signal_names)
    generator.configure_from_field_config(field_config, protocol_name=f"axi4_{channel.lower()}")

    return generator


# ==============================================================================
# AXI4 Channel Constraint Patterns
# ==============================================================================

def create_axi4_aw_handshake_constraint(signal_prefix: str = "m_axi_",
                                        max_window: int = 30,
                                        required: bool = True,
                                        clock_group: str = "default",
                                        field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4 Write Address (AW) handshake constraint.

    Detects: awvalid(0→1) → awready(0→1) sequence

    Args:
        signal_prefix: Prefix for signal names (default: "m_axi_")
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for AW handshake detection
    """
    awvalid_sig = f"{signal_prefix}awvalid"
    awready_sig = f"{signal_prefix}awready"

    events = [
        create_temporal_event("awvalid_start", create_transition_pattern(awvalid_sig, 0, 1)),
        create_temporal_event("awready_response", create_transition_pattern(awready_sig, 0, 1))
    ]

    # Generate signal list from field config
    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}aw{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [awvalid_sig, awready_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}aw_handshake",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axi4_aw"
    )


def create_axi4_w_handshake_constraint(signal_prefix: str = "m_axi_",
                                       max_window: int = 30,
                                       required: bool = True,
                                       clock_group: str = "default",
                                       field_config: Optional[FieldConfig] = None,
                                       detect_last: bool = True) -> TemporalConstraint:
    """
    Create AXI4 Write Data (W) handshake constraint.

    Detects: wvalid(0→1) → wready(0→1) sequence, optionally with WLAST

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding
        detect_last: Whether to require WLAST=1 (default: True)

    Returns:
        TemporalConstraint for W handshake detection
    """
    wvalid_sig = f"{signal_prefix}wvalid"
    wready_sig = f"{signal_prefix}wready"
    wlast_sig = f"{signal_prefix}wlast"

    events = [
        create_temporal_event("wvalid_start", create_transition_pattern(wvalid_sig, 0, 1)),
        create_temporal_event("wready_response", create_transition_pattern(wready_sig, 0, 1))
    ]

    if detect_last:
        events.append(create_temporal_event("wlast_assert", create_static_pattern(wlast_sig, 1)))

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}w{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [wvalid_sig, wready_sig, wlast_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}w_handshake",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axi4_w"
    )


def create_axi4_b_handshake_constraint(signal_prefix: str = "m_axi_",
                                       max_window: int = 30,
                                       required: bool = True,
                                       clock_group: str = "default",
                                       field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4 Write Response (B) handshake constraint.

    Detects: bvalid(0→1) → bready(0→1) sequence

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for B handshake detection
    """
    bvalid_sig = f"{signal_prefix}bvalid"
    bready_sig = f"{signal_prefix}bready"

    events = [
        create_temporal_event("bvalid_start", create_transition_pattern(bvalid_sig, 0, 1)),
        create_temporal_event("bready_response", create_transition_pattern(bready_sig, 0, 1))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}b{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [bvalid_sig, bready_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}b_handshake",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axi4_b"
    )


def create_axi4_ar_handshake_constraint(signal_prefix: str = "m_axi_",
                                        max_window: int = 30,
                                        required: bool = True,
                                        clock_group: str = "default",
                                        field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4 Read Address (AR) handshake constraint.

    Detects: arvalid(0→1) → arready(0→1) sequence

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for AR handshake detection
    """
    arvalid_sig = f"{signal_prefix}arvalid"
    arready_sig = f"{signal_prefix}arready"

    events = [
        create_temporal_event("arvalid_start", create_transition_pattern(arvalid_sig, 0, 1)),
        create_temporal_event("arready_response", create_transition_pattern(arready_sig, 0, 1))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}ar{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [arvalid_sig, arready_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}ar_handshake",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axi4_ar"
    )


def create_axi4_r_handshake_constraint(signal_prefix: str = "m_axi_",
                                       max_window: int = 30,
                                       required: bool = True,
                                       clock_group: str = "default",
                                       field_config: Optional[FieldConfig] = None,
                                       detect_last: bool = True) -> TemporalConstraint:
    """
    Create AXI4 Read Data (R) handshake constraint.

    Detects: rvalid(0→1) → rready(0→1) sequence, optionally with RLAST

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding
        detect_last: Whether to require RLAST=1 (default: True)

    Returns:
        TemporalConstraint for R handshake detection
    """
    rvalid_sig = f"{signal_prefix}rvalid"
    rready_sig = f"{signal_prefix}rready"
    rlast_sig = f"{signal_prefix}rlast"

    events = [
        create_temporal_event("rvalid_start", create_transition_pattern(rvalid_sig, 0, 1)),
        create_temporal_event("rready_response", create_transition_pattern(rready_sig, 0, 1))
    ]

    if detect_last:
        events.append(create_temporal_event("rlast_assert", create_static_pattern(rlast_sig, 1)))

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}r{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [rvalid_sig, rready_sig, rlast_sig]

    return TemporalConstraint(
        name=f"{signal_prefix}r_handshake",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=signals_to_show,
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="axi4_r"
    )


# ==============================================================================
# AXI4 Boundary Patterns
# ==============================================================================

def get_axi4_boundary_pattern(channel: str, signal_prefix: str = "m_axi_") -> Dict[str, int]:
    """
    Get AXI4 boundary reset pattern for specific channel.

    Args:
        channel: Channel name ('AW', 'W', 'B', 'AR', 'R')
        signal_prefix: Signal name prefix

    Returns:
        Dictionary of signal: value pairs for idle state
    """
    ch_prefix = channel.lower()
    return {
        f"{signal_prefix}{ch_prefix}valid": 0,
        f"{signal_prefix}{ch_prefix}ready": 0
    }


def setup_axi4_boundaries(wave_solver: TemporalConstraintSolver,
                          constraint_names: List[str],
                          channel: str,
                          signal_prefix: str = "m_axi_",
                          field_config: Optional[FieldConfig] = None):
    """
    Configure AXI4 channel transaction boundaries.

    Uses valid falling edge as transaction boundary trigger.

    Args:
        wave_solver: TemporalConstraintSolver instance
        constraint_names: Constraint names to configure
        channel: Channel name ('AW', 'W', 'B', 'AR', 'R')
        signal_prefix: Signal name prefix
        field_config: Optional FieldConfig for protocol configuration
    """
    ch_prefix = channel.lower()
    valid_sig = f"{signal_prefix}{ch_prefix}valid"

    for constraint_name in constraint_names:
        wave_solver.auto_detect_boundaries(
            constraint_name=constraint_name,
            transition_signal=valid_sig,
            transition_value=(1, 0),  # Valid high→low (end of transaction)
            reset_signals=get_axi4_boundary_pattern(channel, signal_prefix)
        )

        if field_config and hasattr(wave_solver, 'configure_from_field_config'):
            wave_solver.configure_from_field_config(field_config, protocol_name=f"axi4_{ch_prefix}")


# ==============================================================================
# AXI4 Preset Configurations
# ==============================================================================

class AXI4Presets:
    """Predefined AXI4 constraint configurations for common use cases"""

    @staticmethod
    def write_basic(signal_prefix: str = "m_axi_",
                    aw_config: Optional[FieldConfig] = None,
                    w_config: Optional[FieldConfig] = None,
                    b_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Basic write transaction preset (AW + W + B channels).

        Use case: Verify write transactions are occurring

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'aw_handshake': create_axi4_aw_handshake_constraint(signal_prefix, field_config=aw_config),
            'w_handshake': create_axi4_w_handshake_constraint(signal_prefix, field_config=w_config),
            'b_handshake': create_axi4_b_handshake_constraint(signal_prefix, field_config=b_config)
        }

    @staticmethod
    def read_basic(signal_prefix: str = "m_axi_",
                   ar_config: Optional[FieldConfig] = None,
                   r_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Basic read transaction preset (AR + R channels).

        Use case: Verify read transactions are occurring

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'ar_handshake': create_axi4_ar_handshake_constraint(signal_prefix, field_config=ar_config),
            'r_handshake': create_axi4_r_handshake_constraint(signal_prefix, field_config=r_config)
        }

    @staticmethod
    def comprehensive(signal_prefix: str = "m_axi_",
                      aw_config: Optional[FieldConfig] = None,
                      w_config: Optional[FieldConfig] = None,
                      b_config: Optional[FieldConfig] = None,
                      ar_config: Optional[FieldConfig] = None,
                      r_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Comprehensive AXI4 analysis preset (all 5 channels).

        Use case: Full AXI4 protocol behavior analysis

        Returns:
            Dict of constraint_name: constraint
        """
        constraints = {}
        constraints.update(AXI4Presets.write_basic(signal_prefix, aw_config, w_config, b_config))
        constraints.update(AXI4Presets.read_basic(signal_prefix, ar_config, r_config))
        return constraints

    @staticmethod
    def debug(signal_prefix: str = "m_axi_",
              aw_config: Optional[FieldConfig] = None,
              w_config: Optional[FieldConfig] = None,
              b_config: Optional[FieldConfig] = None,
              ar_config: Optional[FieldConfig] = None,
              r_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Debug preset with extended windows.

        Use case: Debugging stuck or misbehaving AXI4 interfaces

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'aw_handshake': create_axi4_aw_handshake_constraint(signal_prefix, max_window=100, field_config=aw_config),
            'w_handshake': create_axi4_w_handshake_constraint(signal_prefix, max_window=100, field_config=w_config),
            'b_handshake': create_axi4_b_handshake_constraint(signal_prefix, max_window=100, field_config=b_config),
            'ar_handshake': create_axi4_ar_handshake_constraint(signal_prefix, max_window=100, field_config=ar_config),
            'r_handshake': create_axi4_r_handshake_constraint(signal_prefix, max_window=100, field_config=r_config)
        }


# ==============================================================================
# Convenience Functions for Quick Setup
# ==============================================================================

def setup_axi4_constraints_with_boundaries(wave_solver: TemporalConstraintSolver,
                                           preset_name: str = "comprehensive",
                                           signal_prefix: str = "m_axi_",
                                           id_width: int = 8,
                                           addr_width: int = 32,
                                           data_width: int = 32,
                                           user_width: int = 0) -> int:
    """
    One-stop setup for AXI4 wavedrom with all configuration.

    Args:
        wave_solver: TemporalConstraintSolver instance
        preset_name: Preset name ("write_basic", "read_basic", "comprehensive", "debug")
        signal_prefix: Signal name prefix (default: "m_axi_")
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields (0 = no user signals)

    Returns:
        Number of constraints added

    Example:
        num_constraints = setup_axi4_constraints_with_boundaries(
            wave_solver=wave_solver,
            preset_name="comprehensive",
            signal_prefix="m_axi_",
            data_width=64
        )
    """
    # Create field configs for all channels
    field_configs = get_axi4_field_configs(id_width, addr_width, data_width, user_width)

    # Get preset constraints
    presets = AXI4Presets()
    if preset_name == "write_basic":
        constraints_dict = presets.write_basic(
            signal_prefix,
            aw_config=field_configs['AW'],
            w_config=field_configs['W'],
            b_config=field_configs['B']
        )
    elif preset_name == "read_basic":
        constraints_dict = presets.read_basic(
            signal_prefix,
            ar_config=field_configs['AR'],
            r_config=field_configs['R']
        )
    elif preset_name == "comprehensive":
        constraints_dict = presets.comprehensive(
            signal_prefix,
            aw_config=field_configs['AW'],
            w_config=field_configs['W'],
            b_config=field_configs['B'],
            ar_config=field_configs['AR'],
            r_config=field_configs['R']
        )
    elif preset_name == "debug":
        constraints_dict = presets.debug(
            signal_prefix,
            aw_config=field_configs['AW'],
            w_config=field_configs['W'],
            b_config=field_configs['B'],
            ar_config=field_configs['AR'],
            r_config=field_configs['R']
        )
    else:
        raise ValueError(f"Unknown preset: {preset_name}. "
                        f"Available: write_basic, read_basic, comprehensive, debug")

    # Add constraints to solver
    for name, constraint in constraints_dict.items():
        wave_solver.add_constraint(constraint)

    # Setup boundaries per channel
    channel_map = {
        'aw_handshake': ('AW', field_configs['AW']),
        'w_handshake': ('W', field_configs['W']),
        'b_handshake': ('B', field_configs['B']),
        'ar_handshake': ('AR', field_configs['AR']),
        'r_handshake': ('R', field_configs['R'])
    }

    for constraint_name, (channel, config) in channel_map.items():
        if constraint_name in constraints_dict:
            setup_axi4_boundaries(wave_solver, [constraint_name], channel, signal_prefix, config)

    return len(constraints_dict)


# Export classes and functions
__all__ = [
    # Field config helpers
    'get_axi4_channel_field_config',
    'create_axi4_wavejson_generator',

    # Constraint builders
    'create_axi4_aw_handshake_constraint',
    'create_axi4_w_handshake_constraint',
    'create_axi4_b_handshake_constraint',
    'create_axi4_ar_handshake_constraint',
    'create_axi4_r_handshake_constraint',

    # Boundary management
    'get_axi4_boundary_pattern',
    'setup_axi4_boundaries',

    # Preset class
    'AXI4Presets',

    # Setup function
    'setup_axi4_constraints_with_boundaries',
]
