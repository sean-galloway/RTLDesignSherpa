# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4Presets
# Purpose: AXI4-Lite Constraints with Temporal Pattern Detection
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4-Lite Constraints with Temporal Pattern Detection

Provides constraint patterns, field configurations, and templates for AXI4-Lite
protocol waveform generation using WaveDrom and temporal constraint solving.

AXI4-Lite Protocol:
- Simplified subset of AXI4 (no bursts, single outstanding transaction)
- 5 channels: AW (Write Address), W (Write Data), B (Write Response),
  AR (Read Address), R (Read Data)
- Each channel has valid/ready handshake
- No ID signals, no AWLEN/ARLEN, no burst support

Key Features:
1. Per-channel constraint patterns (AW, W, B, AR, R)
2. Simple transaction detection (single beat only)
3. Protocol compliance checking
4. Lower complexity than full AXI4

Usage Patterns:
- Write transaction: AW handshake → W data → B response
- Read transaction: AR handshake → R data
- No burst support (simpler than AXI4)
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
# AXI4-Lite Field Configuration Generators (Channel-Specific)
# ==============================================================================

def get_axil4_channel_field_config(channel: str,
                                    addr_width: int = 32,
                                    data_width: int = 32) -> FieldConfig:
    """
    Create AXI4-Lite field configuration for a specific channel.

    AXI4-Lite is simpler than AXI4:
    - No ID signals
    - No burst support (LEN, SIZE, BURST removed)
    - No LOCK, CACHE, QOS, REGION signals
    - Only PROT remains

    Args:
        channel: Channel name ('AW', 'W', 'B', 'AR', 'R')
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)

    Returns:
        FieldConfig for specified channel

    Example:
        aw_config = get_axil4_channel_field_config('AW', addr_width=32)
    """
    config = FieldConfig()

    if channel == 'AW':
        # Write Address Channel
        config.add_field(FieldDefinition('addr', addr_width, format='hex', description='Write Address'))
        config.add_field(FieldDefinition('prot', 3, format='bin', description='Protection Type'))

    elif channel == 'W':
        # Write Data Channel
        strb_width = data_width // 8
        config.add_field(FieldDefinition('data', data_width, format='hex', description='Write Data'))
        config.add_field(FieldDefinition('strb', strb_width, format='bin', description='Write Strobe'))

    elif channel == 'B':
        # Write Response Channel
        config.add_field(FieldDefinition('resp', 2, format='dec', description='Write Response',
                                        encoding={0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}))

    elif channel == 'AR':
        # Read Address Channel
        config.add_field(FieldDefinition('addr', addr_width, format='hex', description='Read Address'))
        config.add_field(FieldDefinition('prot', 3, format='bin', description='Protection Type'))

    elif channel == 'R':
        # Read Data Channel
        config.add_field(FieldDefinition('data', data_width, format='hex', description='Read Data'))
        config.add_field(FieldDefinition('resp', 2, format='dec', description='Read Response',
                                        encoding={0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}))

    else:
        raise ValueError(f"Unknown AXI4-Lite channel: {channel}")

    return config


def create_axil4_wavejson_generator(channel: str,
                                     field_config: FieldConfig,
                                     signal_prefix: str = "m_axil_",
                                     group_name: Optional[str] = None) -> WaveJSONGenerator:
    """
    Create WaveJSON generator for AXI4-Lite channel with field configuration.

    Args:
        channel: Channel name ('AW', 'W', 'B', 'AR', 'R')
        field_config: Channel field configuration
        signal_prefix: Prefix for signal names (default: "m_axil_")
        group_name: Group name in waveform (default: "AXI4-Lite {channel}")

    Returns:
        Configured WaveJSONGenerator
    """
    generator = WaveJSONGenerator()

    if group_name is None:
        group_name = f"AXI4-Lite {channel}"

    # Map channel to signal prefix
    channel_prefix_map = {
        'AW': 'aw', 'W': 'w', 'B': 'b',
        'AR': 'ar', 'R': 'r'
    }
    ch_prefix = channel_prefix_map.get(channel, channel.lower())

    # Create signal names: m_axil_awvalid, m_axil_awready, m_axil_awaddr, etc.
    signal_names = [f"{signal_prefix}{ch_prefix}valid", f"{signal_prefix}{ch_prefix}ready"]
    for field in field_config.fields():
        if field.name not in ['valid', 'ready']:
            signal_names.append(f"{signal_prefix}{ch_prefix}{field.name}")

    generator.add_interface_group(group_name, signal_names)
    generator.configure_from_field_config(field_config, protocol_name=f"axil4_{channel.lower()}")

    return generator


# ==============================================================================
# AXI4-Lite Channel Constraint Patterns
# ==============================================================================

def create_axil4_aw_handshake_constraint(signal_prefix: str = "m_axil_",
                                         max_window: int = 30,
                                         required: bool = True,
                                         clock_group: str = "default",
                                         field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4-Lite Write Address (AW) handshake constraint.

    Detects: awvalid(0→1) → awready(0→1) sequence

    Args:
        signal_prefix: Prefix for signal names (default: "m_axil_")
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
        protocol_hint="axil4_aw"
    )


def create_axil4_w_handshake_constraint(signal_prefix: str = "m_axil_",
                                        max_window: int = 30,
                                        required: bool = True,
                                        clock_group: str = "default",
                                        field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4-Lite Write Data (W) handshake constraint.

    Detects: wvalid(0→1) → wready(0→1) sequence

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for W handshake detection
    """
    wvalid_sig = f"{signal_prefix}wvalid"
    wready_sig = f"{signal_prefix}wready"

    events = [
        create_temporal_event("wvalid_start", create_transition_pattern(wvalid_sig, 0, 1)),
        create_temporal_event("wready_response", create_transition_pattern(wready_sig, 0, 1))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}w{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [wvalid_sig, wready_sig]

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
        protocol_hint="axil4_w"
    )


def create_axil4_b_handshake_constraint(signal_prefix: str = "m_axil_",
                                        max_window: int = 30,
                                        required: bool = True,
                                        clock_group: str = "default",
                                        field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4-Lite Write Response (B) handshake constraint.

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
        protocol_hint="axil4_b"
    )


def create_axil4_ar_handshake_constraint(signal_prefix: str = "m_axil_",
                                         max_window: int = 30,
                                         required: bool = True,
                                         clock_group: str = "default",
                                         field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4-Lite Read Address (AR) handshake constraint.

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
        protocol_hint="axil4_ar"
    )


def create_axil4_r_handshake_constraint(signal_prefix: str = "m_axil_",
                                        max_window: int = 30,
                                        required: bool = True,
                                        clock_group: str = "default",
                                        field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create AXI4-Lite Read Data (R) handshake constraint.

    Detects: rvalid(0→1) → rready(0→1) sequence

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum cycles for pattern match
        required: Whether this constraint must be satisfied
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for R handshake detection
    """
    rvalid_sig = f"{signal_prefix}rvalid"
    rready_sig = f"{signal_prefix}rready"

    events = [
        create_temporal_event("rvalid_start", create_transition_pattern(rvalid_sig, 0, 1)),
        create_temporal_event("rready_response", create_transition_pattern(rready_sig, 0, 1))
    ]

    signals_to_show = []
    if field_config:
        signals_to_show = [f"{signal_prefix}r{f.name}" for f in field_config.fields()]
    else:
        signals_to_show = [rvalid_sig, rready_sig]

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
        protocol_hint="axil4_r"
    )


# ==============================================================================
# AXI4-Lite Boundary Patterns
# ==============================================================================

def get_axil4_boundary_pattern(channel: str, signal_prefix: str = "m_axil_") -> Dict[str, int]:
    """
    Get AXI4-Lite boundary reset pattern for specific channel.

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


def setup_axil4_boundaries(wave_solver: TemporalConstraintSolver,
                           constraint_names: List[str],
                           channel: str,
                           signal_prefix: str = "m_axil_",
                           field_config: Optional[FieldConfig] = None):
    """
    Configure AXI4-Lite channel transaction boundaries.

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
            transition_value=(1, 0),
            reset_signals=get_axil4_boundary_pattern(channel, signal_prefix)
        )

        if field_config and hasattr(wave_solver, 'configure_from_field_config'):
            wave_solver.configure_from_field_config(field_config, protocol_name=f"axil4_{ch_prefix}")


# ==============================================================================
# AXI4-Lite Preset Configurations
# ==============================================================================

class AXIL4Presets:
    """Predefined AXI4-Lite constraint configurations for common use cases"""

    @staticmethod
    def write_basic(signal_prefix: str = "m_axil_",
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
            'aw_handshake': create_axil4_aw_handshake_constraint(signal_prefix, field_config=aw_config),
            'w_handshake': create_axil4_w_handshake_constraint(signal_prefix, field_config=w_config),
            'b_handshake': create_axil4_b_handshake_constraint(signal_prefix, field_config=b_config)
        }

    @staticmethod
    def read_basic(signal_prefix: str = "m_axil_",
                   ar_config: Optional[FieldConfig] = None,
                   r_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Basic read transaction preset (AR + R channels).

        Use case: Verify read transactions are occurring

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'ar_handshake': create_axil4_ar_handshake_constraint(signal_prefix, field_config=ar_config),
            'r_handshake': create_axil4_r_handshake_constraint(signal_prefix, field_config=r_config)
        }

    @staticmethod
    def comprehensive(signal_prefix: str = "m_axil_",
                      aw_config: Optional[FieldConfig] = None,
                      w_config: Optional[FieldConfig] = None,
                      b_config: Optional[FieldConfig] = None,
                      ar_config: Optional[FieldConfig] = None,
                      r_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Comprehensive AXI4-Lite analysis preset (all 5 channels).

        Use case: Full AXI4-Lite protocol behavior analysis

        Returns:
            Dict of constraint_name: constraint
        """
        constraints = {}
        constraints.update(AXIL4Presets.write_basic(signal_prefix, aw_config, w_config, b_config))
        constraints.update(AXIL4Presets.read_basic(signal_prefix, ar_config, r_config))
        return constraints

    @staticmethod
    def debug(signal_prefix: str = "m_axil_",
              aw_config: Optional[FieldConfig] = None,
              w_config: Optional[FieldConfig] = None,
              b_config: Optional[FieldConfig] = None,
              ar_config: Optional[FieldConfig] = None,
              r_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Debug preset with extended windows.

        Use case: Debugging stuck or misbehaving AXI4-Lite interfaces

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'aw_handshake': create_axil4_aw_handshake_constraint(signal_prefix, max_window=100, field_config=aw_config),
            'w_handshake': create_axil4_w_handshake_constraint(signal_prefix, max_window=100, field_config=w_config),
            'b_handshake': create_axil4_b_handshake_constraint(signal_prefix, max_window=100, field_config=b_config),
            'ar_handshake': create_axil4_ar_handshake_constraint(signal_prefix, max_window=100, field_config=ar_config),
            'r_handshake': create_axil4_r_handshake_constraint(signal_prefix, max_window=100, field_config=r_config)
        }


# ==============================================================================
# Convenience Functions for Quick Setup
# ==============================================================================

def setup_axil4_constraints_with_boundaries(wave_solver: TemporalConstraintSolver,
                                            preset_name: str = "comprehensive",
                                            signal_prefix: str = "m_axil_",
                                            addr_width: int = 32,
                                            data_width: int = 32) -> int:
    """
    One-stop setup for AXI4-Lite wavedrom with all configuration.

    Args:
        wave_solver: TemporalConstraintSolver instance
        preset_name: Preset name ("write_basic", "read_basic", "comprehensive", "debug")
        signal_prefix: Signal name prefix (default: "m_axil_")
        addr_width: Width of address fields
        data_width: Width of data fields

    Returns:
        Number of constraints added

    Example:
        num_constraints = setup_axil4_constraints_with_boundaries(
            wave_solver=wave_solver,
            preset_name="comprehensive",
            signal_prefix="m_axil_",
            data_width=64
        )
    """
    # Create field configs for all channels
    field_configs = {
        'AW': get_axil4_channel_field_config('AW', addr_width, data_width),
        'W': get_axil4_channel_field_config('W', addr_width, data_width),
        'B': get_axil4_channel_field_config('B', addr_width, data_width),
        'AR': get_axil4_channel_field_config('AR', addr_width, data_width),
        'R': get_axil4_channel_field_config('R', addr_width, data_width)
    }

    # Get preset constraints
    presets = AXIL4Presets()
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
            setup_axil4_boundaries(wave_solver, [constraint_name], channel, signal_prefix, config)

    return len(constraints_dict)


# Export classes and functions
__all__ = [
    # Field config helpers
    'get_axil4_channel_field_config',
    'create_axil4_wavejson_generator',

    # Constraint builders
    'create_axil4_aw_handshake_constraint',
    'create_axil4_w_handshake_constraint',
    'create_axil4_b_handshake_constraint',
    'create_axil4_ar_handshake_constraint',
    'create_axil4_r_handshake_constraint',

    # Boundary management
    'get_axil4_boundary_pattern',
    'setup_axil4_boundaries',

    # Preset class
    'AXIL4Presets',

    # Setup function
    'setup_axil4_constraints_with_boundaries',
]
