# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXIPresets
# Purpose: GAXI Constraints with Temporal Pattern Detection
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
GAXI Constraints with Temporal Pattern Detection

Provides constraint patterns, field configurations, and templates for GAXI
protocol waveform generation using WaveDrom and temporal constraint solving.

GAXI Protocol:
- Simple valid/ready handshake protocol
- Flexible data payload (configurable field widths)
- Used as basis for APB, AXI4, and custom protocols

Key Features:
1. Handshake pattern detection (valid→ready sequences)
2. Configurable data field widths
3. Multi-signal format support (addr, ctrl, data0, data1, etc.)
4. Templates for common use cases

Usage Patterns:
- Single data field: {valid, ready, data}
- Multi-field: {valid, ready, addr, ctrl, data0, data1}
- Custom: Define your own field configuration
"""

from typing import List, Dict, Optional, Any, Tuple
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraint, TemporalEvent, SignalTransition, SignalStatic, TemporalRelation,
    TemporalConstraintSolver
)
from CocoTBFramework.components.wavedrom.utility import (
    create_transition_pattern, create_static_pattern, create_temporal_event,
    create_debug_constraint, create_protocol_specific_field_config
)

# Required imports
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


# ==============================================================================
# GAXI Field Configuration Generators
# ==============================================================================

def get_gaxi_field_config(data_width: int = 32,
                          addr_width: int = 0,
                          ctrl_width: int = 0,
                          num_data_fields: int = 1,
                          **extra_fields) -> FieldConfig:
    """
    Create GAXI field configuration for various interface patterns.

    Supports multiple patterns:
    1. Simple: {valid, ready, data}
    2. With address: {valid, ready, addr, data}
    3. Multi-field: {valid, ready, addr, ctrl, data0, data1, ...}
    4. Custom: Add extra_fields for protocol-specific extensions

    Args:
        data_width: Width of each data field (default: 32)
        addr_width: Width of address field (0 = no address, default: 0)
        ctrl_width: Width of control field (0 = no control, default: 0)
        num_data_fields: Number of data fields (default: 1 → data, 2 → data0/data1)
        **extra_fields: Additional field definitions {name: width}

    Returns:
        FieldConfig with GAXI signal definitions

    Examples:
        # Simple data-only
        config = get_gaxi_field_config(data_width=32)
        # → {valid, ready, data[31:0]}

        # With address
        config = get_gaxi_field_config(data_width=32, addr_width=16)
        # → {valid, ready, addr[15:0], data[31:0]}

        # Multi-field like APB
        config = get_gaxi_field_config(data_width=32, addr_width=16,
                                       ctrl_width=4, num_data_fields=2)
        # → {valid, ready, addr[15:0], ctrl[3:0], data0[31:0], data1[31:0]}

        # Custom protocol
        config = get_gaxi_field_config(data_width=8, prot_width=3, user_width=4)
        # → {valid, ready, data[7:0], prot[2:0], user[3:0]}
    """
    fields = {}

    # Core handshake signals (always present)
    fields['valid'] = FieldDefinition('valid', 1,
                                      description='Valid signal')
    fields['ready'] = FieldDefinition('ready', 1,
                                      description='Ready signal')

    # Optional address field
    if addr_width > 0:
        fields['addr'] = FieldDefinition('addr', addr_width,
                                        description=f'Address [{addr_width-1}:0]')

    # Optional control field
    if ctrl_width > 0:
        fields['ctrl'] = FieldDefinition('ctrl', ctrl_width,
                                        description=f'Control [{ctrl_width-1}:0]')

    # Data field(s)
    if num_data_fields == 1:
        fields['data'] = FieldDefinition('data', data_width,
                                        description=f'Data [{data_width-1}:0]')
    else:
        for i in range(num_data_fields):
            fields[f'data{i}'] = FieldDefinition(f'data{i}', data_width,
                                                description=f'Data{i} [{data_width-1}:0]')

    # Add any extra protocol-specific fields
    for field_name, field_width in extra_fields.items():
        if isinstance(field_width, int):
            fields[field_name] = FieldDefinition(field_name, field_width,
                                                description=f'{field_name} [{field_width-1}:0]')

    # Create FieldConfig and add all fields
    config = FieldConfig(lsb_first=True)  # LSB-first for compatibility
    for field_name, field_def in fields.items():
        config.add_field(field_def)

    return config


def create_gaxi_wavejson_generator(field_config: FieldConfig,
                                   signal_prefix: str = "gaxi_",
                                   group_name: str = "GAXI") -> WaveJSONGenerator:
    """
    Create WaveJSON generator for GAXI protocol with field configuration.

    Args:
        field_config: GAXI field configuration
        signal_prefix: Prefix for signal names (default: "gaxi_")
        group_name: Group name in waveform display (default: "GAXI")

    Returns:
        Configured WaveJSONGenerator
    """
    generator = WaveJSONGenerator()

    # Add GAXI interface group with all signals from field config
    signal_names = [f"{signal_prefix}{field.name}" for field in field_config.fields()]
    generator.add_interface_group(group_name, signal_names)

    # Configure field config for data formatting
    generator.configure_from_field_config(field_config, protocol_name="gaxi")

    return generator


# ==============================================================================
# GAXI Constraint Patterns
# ==============================================================================

def create_gaxi_handshake_constraint(signal_prefix: str = "gaxi_",
                                    max_window: int = 30,
                                    required: bool = True,
                                    clock_group: str = "default",
                                    field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create basic GAXI valid→ready handshake constraint.

    Detects: valid(0→1) → ready(0→1) sequence with both signals high

    Args:
        signal_prefix: Prefix for signal names (default: "gaxi_")
        max_window: Maximum cycles for pattern match (default: 30)
        required: Whether this constraint must be satisfied (default: True)
        clock_group: Clock group name (default: "default")
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for handshake detection
    """
    valid_sig = f"{signal_prefix}valid"
    ready_sig = f"{signal_prefix}ready"

    events = [
        create_temporal_event("valid_start", create_transition_pattern(valid_sig, 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern(ready_sig, 0, 1))
    ]

    return TemporalConstraint(
        name=f"{signal_prefix}handshake",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=[f"{signal_prefix}{f.name}" for f in field_config.fields()] if field_config else [valid_sig, ready_sig],
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="gaxi"
    )


def create_gaxi_back2back_constraint(signal_prefix: str = "gaxi_",
                                     max_window: int = 10,
                                     clock_group: str = "default",
                                     field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create constraint for back-to-back GAXI transactions.

    Detects: Multiple valid/ready handshakes with no idle cycles

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum window for detection
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for back-to-back detection
    """
    valid_sig = f"{signal_prefix}valid"
    ready_sig = f"{signal_prefix}ready"

    events = [
        create_temporal_event("handshake", create_static_pattern(valid_sig, 1)),
        create_temporal_event("ready", create_static_pattern(ready_sig, 1))
    ]

    return TemporalConstraint(
        name=f"{signal_prefix}back2back",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=False,
        clock_group=clock_group,
        signals_to_show=[f"{signal_prefix}{f.name}" for f in field_config.fields()] if field_config else [valid_sig, ready_sig],
        min_sequence_duration=2,
        max_sequence_duration=max_window - 2,
        field_config=field_config,
        protocol_hint="gaxi"
    )


def create_gaxi_stall_constraint(signal_prefix: str = "gaxi_",
                                max_window: int = 50,
                                clock_group: str = "default",
                                field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create constraint for GAXI stall condition (valid but no ready).

    Detects: valid=1, ready=0 (backpressure scenario)

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum stall duration to detect
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for stall detection
    """
    valid_sig = f"{signal_prefix}valid"
    ready_sig = f"{signal_prefix}ready"

    events = [
        create_temporal_event("valid_asserted", create_transition_pattern(valid_sig, 0, 1)),
        create_temporal_event("ready_low", create_static_pattern(ready_sig, 0))
    ]

    return TemporalConstraint(
        name=f"{signal_prefix}stall",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=False,
        clock_group=clock_group,
        signals_to_show=[f"{signal_prefix}{f.name}" for f in field_config.fields()] if field_config else [valid_sig, ready_sig],
        min_sequence_duration=1,
        max_sequence_duration=max_window - 5,
        field_config=field_config,
        protocol_hint="gaxi"
    )


def create_gaxi_idle_constraint(signal_prefix: str = "gaxi_",
                               max_window: int = 20,
                               clock_group: str = "default",
                               field_config: Optional[FieldConfig] = None) -> TemporalConstraint:
    """
    Create constraint for GAXI idle state.

    Detects: Both valid and ready low (idle bus)

    Args:
        signal_prefix: Prefix for signal names
        max_window: Maximum idle period to detect
        clock_group: Clock group name
        field_config: Optional FieldConfig for packet decoding

    Returns:
        TemporalConstraint for idle detection
    """
    valid_sig = f"{signal_prefix}valid"
    ready_sig = f"{signal_prefix}ready"

    events = [
        create_temporal_event("valid_idle", create_static_pattern(valid_sig, 0)),
        create_temporal_event("ready_idle", create_static_pattern(ready_sig, 0))
    ]

    return TemporalConstraint(
        name=f"{signal_prefix}idle",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=False,
        clock_group=clock_group,
        signals_to_show=[f"{signal_prefix}{f.name}" for f in field_config.fields()] if field_config else [valid_sig, ready_sig],
        min_sequence_duration=1,
        max_sequence_duration=max_window - 2,
        field_config=field_config,
        protocol_hint="gaxi"
    )


# ==============================================================================
# GAXI Boundary Patterns
# ==============================================================================

def get_gaxi_boundary_pattern(signal_prefix: str = "gaxi_") -> Dict[str, int]:
    """
    Get GAXI boundary reset pattern (idle state).

    Args:
        signal_prefix: Signal name prefix

    Returns:
        Dictionary of signal: value pairs for idle state
    """
    return {
        f"{signal_prefix}valid": 0,
        f"{signal_prefix}ready": 0
    }


def setup_gaxi_boundaries(wave_solver: TemporalConstraintSolver,
                         constraint_names: List[str],
                         signal_prefix: str = "gaxi_",
                         field_config: Optional[FieldConfig] = None):
    """
    Configure GAXI transaction boundaries.

    Uses valid falling edge as transaction boundary trigger.

    Args:
        wave_solver: TemporalConstraintSolver instance
        constraint_names: Constraint names to configure
        signal_prefix: Signal name prefix
        field_config: Optional FieldConfig for protocol configuration
    """
    valid_sig = f"{signal_prefix}valid"

    for constraint_name in constraint_names:
        # Auto-boundary on valid falling edge
        wave_solver.auto_detect_boundaries(
            constraint_name=constraint_name,
            transition_signal=valid_sig,
            transition_value=(1, 0),  # Valid high→low (end of transaction)
            reset_signals=get_gaxi_boundary_pattern(signal_prefix)
        )

        # Configure protocol FieldConfig if available
        if field_config and hasattr(wave_solver, 'configure_from_field_config'):
            wave_solver.configure_from_field_config(field_config, protocol_name="gaxi")


# ==============================================================================
# GAXI Preset Configurations
# ==============================================================================

class GAXIPresets:
    """Predefined GAXI constraint configurations for common use cases"""

    @staticmethod
    def basic_handshake(signal_prefix: str = "gaxi_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Basic handshake detection preset.

        Use case: Verify valid/ready handshakes are occurring

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_gaxi_handshake_constraint(signal_prefix=signal_prefix, field_config=field_config)
        }

    @staticmethod
    def comprehensive(signal_prefix: str = "gaxi_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Comprehensive GAXI analysis preset.

        Detects: handshakes, back-to-back, stalls, idle periods

        Use case: Full protocol behavior analysis

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_gaxi_handshake_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'back2back': create_gaxi_back2back_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'stall': create_gaxi_stall_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'idle': create_gaxi_idle_constraint(signal_prefix=signal_prefix, field_config=field_config)
        }

    @staticmethod
    def performance(signal_prefix: str = "gaxi_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Performance analysis preset.

        Focus: Throughput, stalls, back-to-back efficiency

        Use case: Performance optimization

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_gaxi_handshake_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'back2back': create_gaxi_back2back_constraint(signal_prefix=signal_prefix, field_config=field_config),
            'stall': create_gaxi_stall_constraint(signal_prefix=signal_prefix, max_window=100, field_config=field_config)
        }

    @staticmethod
    def debug(signal_prefix: str = "gaxi_", field_config: Optional[FieldConfig] = None) -> Dict[str, Any]:
        """
        Debug preset with extended windows.

        Use case: Debugging stuck or misbehaving interfaces

        Returns:
            Dict of constraint_name: constraint
        """
        return {
            'handshake': create_gaxi_handshake_constraint(signal_prefix=signal_prefix, max_window=100, field_config=field_config),
            'stall': create_gaxi_stall_constraint(signal_prefix=signal_prefix, max_window=200, field_config=field_config),
            'idle': create_gaxi_idle_constraint(signal_prefix=signal_prefix, max_window=50, field_config=field_config)
        }


# ==============================================================================
# Convenience Functions for Quick Setup
# ==============================================================================

def setup_gaxi_constraints_with_boundaries(wave_solver: TemporalConstraintSolver,
                                          preset_name: str = "basic_handshake",
                                          signal_prefix: str = "gaxi_",
                                          max_cycles: int = 30,
                                          clock_group: str = "default",
                                          field_config: Optional[FieldConfig] = None,
                                          enable_packet_callbacks: bool = True,
                                          use_signal_names: bool = True,
                                          post_match_cycles: int = 2,
                                          context_cycles_before: Optional[int] = None,
                                          context_cycles_after: Optional[int] = None) -> int:
    """
    One-stop setup for GAXI wavedrom with all configuration.

    Args:
        wave_solver: TemporalConstraintSolver instance
        preset_name: Preset name ("basic_handshake", "comprehensive", "performance", "debug")
        signal_prefix: Signal name prefix (default: "gaxi_")
        max_cycles: Maximum window for constraints
        clock_group: Clock group name
        field_config: Optional FieldConfig for data formatting
        enable_packet_callbacks: Enable packet-based annotation
        use_signal_names: Use actual signal names (not event names)
        post_match_cycles: Extra cycles after match
        context_cycles_before: Dead/setup cycles before match (None = auto: ~25% of window)
        context_cycles_after: Dead/setup cycles after match (None = auto: ~25% of window)

    Returns:
        Number of constraints added

    Example:
        # In testbench __init__:
        self.gaxi_field_config = get_gaxi_field_config(data_width=32, addr_width=16)
        self.wave_generator = create_gaxi_wavejson_generator(self.gaxi_field_config)
        self.wave_solver = TemporalConstraintSolver()

        # Setup constraints
        num_constraints = setup_gaxi_constraints_with_boundaries(
            wave_solver=self.wave_solver,
            preset_name="comprehensive",
            signal_prefix="cmd_",
            field_config=self.gaxi_field_config
        )

        # In test:
        await self.wave_solver.start_sampling()
        # ... run test ...
        await self.wave_solver.stop_sampling()
        results = self.wave_solver.get_results()
    """
    # Get preset constraints
    presets = GAXIPresets()
    if not hasattr(presets, preset_name):
        raise ValueError(f"Unknown preset: {preset_name}. "
                        f"Available: basic_handshake, comprehensive, performance, debug")

    constraints_dict = getattr(presets, preset_name)(signal_prefix=signal_prefix, field_config=field_config)

    # Add each constraint to solver with context cycle configuration
    constraint_names = []
    for name, constraint in constraints_dict.items():
        # Apply context cycles if specified
        if context_cycles_before is not None:
            constraint.context_cycles_before = context_cycles_before
        if context_cycles_after is not None:
            constraint.context_cycles_after = context_cycles_after

        wave_solver.add_constraint(constraint)
        constraint_names.append(constraint.name)

    # Setup boundaries
    setup_gaxi_boundaries(wave_solver, constraint_names, signal_prefix, field_config)

    # Configure packet callbacks if enabled
    if enable_packet_callbacks and field_config:
        # Packet callback integration can be added here if needed
        pass

    return len(constraints_dict)


def create_gaxi_signals_list(signal_prefix: str = "gaxi_",
                             include_addr: bool = False,
                             include_ctrl: bool = False,
                             num_data_fields: int = 1) -> List[str]:
    """
    Generate signal list for GAXI waveform display.

    Args:
        signal_prefix: Signal name prefix
        include_addr: Include address signal
        include_ctrl: Include control signal
        num_data_fields: Number of data fields

    Returns:
        List of signal names for waveform

    Example:
        signals = create_gaxi_signals_list(signal_prefix="cmd_",
                                          include_addr=True,
                                          num_data_fields=2)
        # → ["cmd_valid", "cmd_ready", "cmd_addr", "cmd_data0", "cmd_data1"]
    """
    signals = [f"{signal_prefix}valid", f"{signal_prefix}ready"]

    if include_addr:
        signals.append(f"{signal_prefix}addr")

    if include_ctrl:
        signals.append(f"{signal_prefix}ctrl")

    if num_data_fields == 1:
        signals.append(f"{signal_prefix}data")
    else:
        for i in range(num_data_fields):
            signals.append(f"{signal_prefix}data{i}")

    return signals


# ==============================================================================
# Template Classes for Common Patterns
# ==============================================================================

class GAXIWaveDromTemplate:
    """
    Dead-simple GAXI wavedrom with automatic signal binding.

    Uses SignalResolver methodology for automatic signal discovery with
    manual override capability.
    """

    def __init__(self, dut,
                 signal_prefix: str = "gaxi_",
                 data_width: int = 32,
                 addr_width: int = 0,
                 ctrl_width: int = 0,
                 num_data_fields: int = 1,
                 preset: str = "comprehensive",
                 bus_name: str = '',
                 pkt_prefix: str = '',
                 signal_map: Optional[Dict[str, str]] = None,
                 clock_signal = None,
                 context_cycles_before: Optional[int] = None,
                 context_cycles_after: Optional[int] = None):
        """
        Initialize GAXI wavedrom with automatic signal binding.

        Args:
            dut: CocoTB DUT handle
            signal_prefix: Signal prefix (e.g., 'wr_', 'cmd_')
            data_width: Data field width
            addr_width: Address field width (0 = no address)
            ctrl_width: Control field width (0 = no control)
            num_data_fields: Number of data fields
            preset: Constraint preset ('comprehensive', 'basic_handshake', 'performance', 'debug')
            bus_name: Bus/channel name if signals have additional prefix
            pkt_prefix: Packet field prefix
            signal_map: Manual signal override (e.g., {'valid': 'my_valid_signal', 'ready': 'my_ready', 'data': 'my_data'})
            clock_signal: Clock signal (auto-detected if None)
            context_cycles_before: Dead/setup cycles before match (None = auto: ~25% of window)
            context_cycles_after: Dead/setup cycles after match (None = auto: ~25% of window)

        Example:
            # Automatic discovery (most common):
            gaxi_wave = GAXIWaveDromTemplate(dut, signal_prefix="wr_", data_width=32)

            # Manual override for non-standard naming:
            gaxi_wave = GAXIWaveDromTemplate(
                dut,
                signal_prefix="",
                data_width=32,
                signal_map={'valid': 'weird_valid', 'ready': 'custom_ready', 'data': 'pkt_data'}
            )
        """
        self.dut = dut
        self.signal_prefix = signal_prefix
        self.context_cycles_before = context_cycles_before
        self.context_cycles_after = context_cycles_after

        # Create field configuration
        self.field_config = get_gaxi_field_config(
            data_width=data_width,
            addr_width=addr_width,
            ctrl_width=ctrl_width,
            num_data_fields=num_data_fields
        )

        # Create wave generator
        self.wave_generator = create_gaxi_wavejson_generator(
            self.field_config,
            signal_prefix=signal_prefix
        )

        # Create constraint solver
        self.wave_solver = TemporalConstraintSolver(
            dut=dut,
            log=dut._log,
            wavejson_generator=self.wave_generator,
            default_field_config=self.field_config
        )

        # Auto-detect clock if not provided
        if clock_signal is None:
            clock_signal = (getattr(dut, 'axi_aclk', None) or
                          getattr(dut, 'i_clk', None) or
                          getattr(dut, 'clk', None))

        if clock_signal is None:
            raise ValueError("Could not auto-detect clock signal. Please provide clock_signal parameter.")

        # Add clock group
        self.wave_solver.add_clock_group('default', clock_signal)

        # 🎯 AUTO-BIND ALL SIGNALS (The magic!)
        self.num_signals = self.wave_solver.auto_bind_signals(
            protocol_type='gaxi',
            signal_prefix=signal_prefix,
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            field_config=self.field_config,
            signal_map=signal_map
        )

        # Setup constraints with boundaries
        self.num_constraints = setup_gaxi_constraints_with_boundaries(
            wave_solver=self.wave_solver,
            preset_name=preset,
            signal_prefix=signal_prefix,
            field_config=self.field_config,
            context_cycles_before=context_cycles_before,
            context_cycles_after=context_cycles_after
        )

        dut._log.info(f"✓ GAXI wavedrom configured: {self.num_signals} signals, {self.num_constraints} constraints")

    async def start_sampling(self):
        """Start wavedrom sampling"""
        if self.wave_solver:
            await self.wave_solver.start_sampling()

    async def stop_sampling(self):
        """Stop wavedrom sampling and get results"""
        if self.wave_solver:
            await self.wave_solver.stop_sampling()
            return self.wave_solver.get_results()
        return None

    def get_status(self):
        """Get wavedrom status"""
        if self.wave_solver:
            self.wave_solver.debug_status()
