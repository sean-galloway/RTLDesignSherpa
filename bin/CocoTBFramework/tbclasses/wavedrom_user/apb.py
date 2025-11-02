# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBConstraints
# Purpose: APB Constraints with Improved Sequence Detection and Edge Annotations
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Constraints with Improved Sequence Detection and Edge Annotations

Improvements:
1. Extended sequences to capture PREADY falling edge (transaction completion)
2. Better signal naming (defaults to actual signal names)
3. Enhanced edge annotation positioning
4. Full WaveDrom arrow type support
"""

from typing import List, Dict, Optional, Any
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraint, TemporalEvent, SignalTransition, SignalStatic, TemporalRelation,
    TemporalConstraintSolver
)
from CocoTBFramework.components.wavedrom.utility import (
    create_transition_pattern, create_static_pattern, create_temporal_event,
    create_debug_constraint, create_protocol_specific_field_config,
    get_apb_field_config
)

# Required imports - no conditionals
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.wavedrom.wavejson_gen import (
    WaveJSONGenerator, create_apb_wavejson_generator
)

# Import APB packet for integration
from CocoTBFramework.components.apb.apb_packet import APBPacket


# APB-specific boundary utilities with FieldConfig integration

def get_apb_boundary_pattern():
    """Get the APB boundary reset pattern - all control signals idle"""
    return {
        'apb_psel': 0,
        'apb_penable': 0,
        'apb_pready': 0
    }

def setup_apb_boundaries(wave_solver: TemporalConstraintSolver,
                                 constraint_names: List[str],
                                 field_config: Optional['FieldConfig'] = None):
    """
    Set up APB transaction boundaries with FieldConfig integration.
    Uses PSEL falling edge as boundary trigger for more reliable detection.

    Args:
        wave_solver: TemporalConstraintSolver instance
        constraint_names: List of constraint names to configure boundaries for
        field_config: Optional FieldConfig for configuration
    """
    for constraint_name in constraint_names:
        # Auto-boundary detection for APB transactions
        # Use PSEL falling edge - more reliable than PREADY
        wave_solver.auto_detect_boundaries(
            constraint_name=constraint_name,
            transition_signal='apb_psel',
            transition_value=(1, 0),  # PSEL high to low transition (end of transaction)
            reset_signals=get_apb_boundary_pattern()
        )

        # Configure protocol-specific FieldConfig if available
        if field_config and hasattr(wave_solver, 'configure_protocol_field_config'):
            wave_solver.configure_protocol_field_config("apb", field_config)

def create_apb_signals_list() -> List[str]:
    """
    Get APB signals for waveform display with clock, reset, and grouping.

    Returns clock/reset as individual signals, APB protocol signals in labeled group.
    """
    return [
        "apb_pclk",      # Clock (individual)
        "apb_presetn",   # Reset (individual)
        ["APB", "apb_psel", "apb_penable", "apb_pwrite", "apb_pready",
         "apb_paddr", "apb_pwdata", "apb_prdata", "apb_pstrb", "apb_pprot", "apb_pslverr"]
    ]


# APB-specific constraint builder functions with improved sequences

def create_apb_write_sequence_constraint(max_window: int = 25,  # Increased for completion
                                                 required: bool = True,
                                                 clock_group: str = "default",
                                                 field_config: Optional['FieldConfig'] = None,
                                                 post_match_cycles: int = 2) -> TemporalConstraint:
    """
    Create APB write sequence constraint - SIMPLIFIED for better detection.

    Core sequence: PSEL(0→1) → PWRITE=1 → PENABLE(0→1) → PREADY(0→1)
    Extended with post_match_cycles to capture transaction completion.
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("apb_psel", 0, 1)),
        create_temporal_event("write_type", create_static_pattern("apb_pwrite", 1)),
        create_temporal_event("enable_start", create_transition_pattern("apb_penable", 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern("apb_pready", 0, 1))
        # Post-match extension will capture PREADY and PSEL falling edges
    ]

    constraint = TemporalConstraint(
        name="apb_write_sequence",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_apb_signals_list(),
        min_sequence_duration=3,  # Core APB sequence
        max_sequence_duration=15,  # Reduced from 20
        field_config=field_config,
        protocol_hint="apb"
    )

    # Add post-match extension and disable boundary detection
    constraint.post_match_cycles = post_match_cycles
    constraint.skip_boundary_detection = True  # Prevent early termination
    return constraint


def create_apb_read_sequence_constraint(max_window: int = 25,  # Increased for completion
                                               required: bool = True,
                                               clock_group: str = "default",
                                               field_config: Optional['FieldConfig'] = None,
                                               post_match_cycles: int = 2) -> TemporalConstraint:
    """
    Create APB read sequence constraint - SIMPLIFIED for better detection.

    Core sequence: PSEL(0→1) → PWRITE=0 → PENABLE(0→1) → PREADY(0→1)
    Extended with post_match_cycles to capture transaction completion.
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("apb_psel", 0, 1)),
        create_temporal_event("read_type", create_static_pattern("apb_pwrite", 0)),
        create_temporal_event("enable_start", create_transition_pattern("apb_penable", 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern("apb_pready", 0, 1))
        # Post-match extension will capture PREADY and PSEL falling edges
    ]

    constraint = TemporalConstraint(
        name="apb_read_sequence",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_apb_signals_list(),
        min_sequence_duration=3,  # Core APB sequence
        max_sequence_duration=15,  # Reduced from 20
        field_config=field_config,
        protocol_hint="apb"
    )

    # Add post-match extension and disable boundary detection
    constraint.post_match_cycles = post_match_cycles
    constraint.skip_boundary_detection = True  # Prevent early termination
    return constraint


def create_apb_complete_transaction_constraint(max_window: int = 30,  # Increased window
                                                       required: bool = False,
                                                       clock_group: str = "default",
                                                       field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
    """
    Create APB complete transaction constraint with full transaction lifecycle.

    Complete sequence: PSEL(0→1) → PENABLE(0→1) → PREADY(0→1) → PREADY(1→0) → PSEL(1→0) → PENABLE(1→0)
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("apb_psel", 0, 1)),
        create_temporal_event("enable_start", create_transition_pattern("apb_penable", 0, 1)),
        create_temporal_event("ready_start", create_transition_pattern("apb_pready", 0, 1)),
        create_temporal_event("ready_end", create_transition_pattern("apb_pready", 1, 0)),
        create_temporal_event("psel_end", create_transition_pattern("apb_psel", 1, 0)),
        create_temporal_event("enable_end", create_transition_pattern("apb_penable", 1, 0))  # ADDED: Full reset
    ]

    return TemporalConstraint(
        name="apb_complete_transaction",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_apb_signals_list(),
        min_sequence_duration=5,  # Increased for full sequence
        max_sequence_duration=25,
        field_config=field_config,
        protocol_hint="apb"
    )


def check_apb_protocol_compliance(window_data: Dict[str, List[int]]) -> bool:
    """APB protocol compliance check with validation"""
    if "apb_psel" not in window_data or "apb_penable" not in window_data:
        return False

    psel_values = window_data["apb_psel"]
    penable_values = window_data["apb_penable"]

    # Look for proper setup->access sequence
    for i in range(len(psel_values) - 1):
        if psel_values[i] == 1 and penable_values[i] == 0:  # Setup phase
            if i + 1 < len(penable_values) and penable_values[i + 1] == 1:  # Access phase
                return True

    return False


class APBConstraints:
    """APB constraints with improved sequences and edge annotations"""

    @staticmethod
    def write_transaction(max_cycles: int = 25,  # Increased
                         required: bool = True,
                         clock_group: str = "default",
                         field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB write transaction with complete sequence"""
        return create_apb_write_sequence_constraint(max_cycles, required, clock_group, field_config)

    @staticmethod
    def read_transaction(max_cycles: int = 25,  # Increased
                        required: bool = True,
                        clock_group: str = "default",
                        field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB read transaction with complete sequence"""
        return create_apb_read_sequence_constraint(max_cycles, required, clock_group, field_config)

    @staticmethod
    def complete_transaction(max_cycles: int = 30,  # Increased
                           required: bool = False,
                           clock_group: str = "default",
                           field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """Complete APB transaction with full lifecycle"""
        return create_apb_complete_transaction_constraint(max_cycles, required, clock_group, field_config)

    @staticmethod
    def write_completion(max_cycles: int = 20,
                        required: bool = False,
                        clock_group: str = "default",
                        field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB write completion with specific write type check"""
        events = [
            create_temporal_event("psel_active", create_static_pattern("apb_psel", 1)),
            create_temporal_event("write_type", create_static_pattern("apb_pwrite", 1)),
            create_temporal_event("enable_active", create_static_pattern("apb_penable", 1)),
            create_temporal_event("ready_response", create_transition_pattern("apb_pready", 0, 1))
        ]

        return TemporalConstraint(
            name="apb_write_completion",
            events=events,
            temporal_relation=TemporalRelation.CONCURRENT,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            field_config=field_config,
            protocol_hint="apb"
        )

    @staticmethod
    def read_completion(max_cycles: int = 20,
                       required: bool = False,
                       clock_group: str = "default",
                       field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB read completion with specific read type check"""
        events = [
            create_temporal_event("psel_active", create_static_pattern("apb_psel", 1)),
            create_temporal_event("read_type", create_static_pattern("apb_pwrite", 0)),
            create_temporal_event("enable_active", create_static_pattern("apb_penable", 1)),
            create_temporal_event("ready_response", create_transition_pattern("apb_pready", 0, 1))
        ]

        return TemporalConstraint(
            name="apb_read_completion",
            events=events,
            temporal_relation=TemporalRelation.CONCURRENT,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            field_config=field_config,
            protocol_hint="apb"
        )

    @staticmethod
    def setup_phase(max_cycles: int = 15,
                   required: bool = False,
                   clock_group: str = "default",
                   field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB setup phase: PSEL=1 AND PENABLE=0"""
        events = [
            create_temporal_event("psel_start", create_transition_pattern("apb_psel", 0, 1)),
            create_temporal_event("enable_low", create_static_pattern("apb_penable", 0))
        ]

        return TemporalConstraint(
            name="apb_setup",
            events=events,
            temporal_relation=TemporalRelation.CONCURRENT,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            max_matches=2,
            field_config=field_config,
            protocol_hint="apb"
        )

    @staticmethod
    def access_phase(max_cycles: int = 15,
                    required: bool = False,
                    clock_group: str = "default",
                    field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB access phase: PSEL=1 AND PENABLE=1"""
        events = [
            create_temporal_event("psel_active", create_static_pattern("apb_psel", 1)),
            create_temporal_event("enable_start", create_transition_pattern("apb_penable", 0, 1))
        ]

        return TemporalConstraint(
            name="apb_access",
            events=events,
            temporal_relation=TemporalRelation.CONCURRENT,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            max_matches=2,
            field_config=field_config,
            protocol_hint="apb"
        )

    @staticmethod
    def error_transaction(max_cycles: int = 25,
                         required: bool = False,
                         clock_group: str = "default",
                         field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB error transaction: PSLVERR goes high"""
        events = [
            create_temporal_event("error_response", create_transition_pattern("apb_pslverr", 0, 1))
        ]

        return TemporalConstraint(
            name="apb_error",
            events=events,
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            field_config=field_config,
            protocol_hint="apb"
        )

    @staticmethod
    def back_to_back_writes(max_cycles: int = 40,
                           required: bool = False,
                           clock_group: str = "default",
                           field_config: Optional['FieldConfig'] = None,
                           post_match_cycles: int = 3) -> TemporalConstraint:
        """Two consecutive APB write transactions - matched by seeing two PSEL cycles"""
        events = [
            # First transaction
            create_temporal_event("psel1_rise", create_transition_pattern("apb_psel", 0, 1)),
            create_temporal_event("psel1_fall", create_transition_pattern("apb_psel", 1, 0)),
            # Second transaction
            create_temporal_event("psel2_rise", create_transition_pattern("apb_psel", 0, 1)),
        ]

        constraint = TemporalConstraint(
            name="apb_back_to_back_writes",
            events=events,
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            min_sequence_duration=4,
            field_config=field_config,
            protocol_hint="apb"
        )
        constraint.post_match_cycles = post_match_cycles
        constraint.skip_boundary_detection = True
        return constraint

    @staticmethod
    def back_to_back_reads(max_cycles: int = 40,
                          required: bool = False,
                          clock_group: str = "default",
                          field_config: Optional['FieldConfig'] = None,
                          post_match_cycles: int = 3) -> TemporalConstraint:
        """Two consecutive APB read transactions - matched by seeing two PSEL cycles"""
        events = [
            # First transaction
            create_temporal_event("psel1_rise", create_transition_pattern("apb_psel", 0, 1)),
            create_temporal_event("psel1_fall", create_transition_pattern("apb_psel", 1, 0)),
            # Second transaction
            create_temporal_event("psel2_rise", create_transition_pattern("apb_psel", 0, 1)),
        ]

        constraint = TemporalConstraint(
            name="apb_back_to_back_reads",
            events=events,
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            min_sequence_duration=4,
            field_config=field_config,
            protocol_hint="apb"
        )
        constraint.post_match_cycles = post_match_cycles
        constraint.skip_boundary_detection = True
        return constraint

    @staticmethod
    def write_to_read(max_cycles: int = 40,
                     required: bool = False,
                     clock_group: str = "default",
                     field_config: Optional['FieldConfig'] = None,
                     post_match_cycles: int = 3) -> TemporalConstraint:
        """Write transaction followed by read transaction"""
        events = [
            # First transaction
            create_temporal_event("psel1_rise", create_transition_pattern("apb_psel", 0, 1)),
            create_temporal_event("psel1_fall", create_transition_pattern("apb_psel", 1, 0)),
            # Second transaction
            create_temporal_event("psel2_rise", create_transition_pattern("apb_psel", 0, 1)),
        ]

        constraint = TemporalConstraint(
            name="apb_write_to_read",
            events=events,
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            min_sequence_duration=4,
            field_config=field_config,
            protocol_hint="apb"
        )
        constraint.post_match_cycles = post_match_cycles
        constraint.skip_boundary_detection = True
        return constraint

    @staticmethod
    def read_to_write(max_cycles: int = 40,
                     required: bool = False,
                     clock_group: str = "default",
                     field_config: Optional['FieldConfig'] = None,
                     post_match_cycles: int = 3) -> TemporalConstraint:
        """Read transaction followed by write transaction"""
        events = [
            # First transaction
            create_temporal_event("psel1_rise", create_transition_pattern("apb_psel", 0, 1)),
            create_temporal_event("psel1_fall", create_transition_pattern("apb_psel", 1, 0)),
            # Second transaction
            create_temporal_event("psel2_rise", create_transition_pattern("apb_psel", 0, 1)),
        ]

        constraint = TemporalConstraint(
            name="apb_read_to_write",
            events=events,
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            min_sequence_duration=4,
            field_config=field_config,
            protocol_hint="apb"
        )
        constraint.post_match_cycles = post_match_cycles
        constraint.skip_boundary_detection = True
        return constraint

    @staticmethod
    def wait_state_sequence(max_cycles: int = 30,
                           required: bool = False,
                           clock_group: str = "default",
                           field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """APB wait state sequence: PENABLE=1 but PREADY stays 0"""
        events = [
            create_temporal_event("enable_start", create_transition_pattern("apb_penable", 0, 1)),
            create_temporal_event("ready_wait", create_static_pattern("apb_pready", 0)),
            create_temporal_event("ready_response", create_transition_pattern("apb_pready", 0, 1))
        ]

        return TemporalConstraint(
            name="apb_wait_state",
            events=events,
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=create_apb_signals_list(),
            min_sequence_duration=3,
            max_sequence_duration=20,
            field_config=field_config,
            protocol_hint="apb"
        )


class APBDebug:
    """Debug constraints for APB troubleshooting with FieldConfig integration"""

    @staticmethod
    def psel_activity(max_cycles: int = 30,
                     required: bool = False,
                     clock_group: str = "default",
                     field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """Debug constraint for PSEL transitions"""
        return create_debug_constraint("apb_psel", "debug_psel_activity", max_cycles, clock_group, field_config)

    @staticmethod
    def pready_activity(max_cycles: int = 30,
                       required: bool = False,
                       clock_group: str = "default",
                       field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """Debug constraint for PREADY transitions"""
        return create_debug_constraint("apb_pready", "debug_pready_activity", max_cycles, clock_group, field_config)

    @staticmethod
    def penable_activity(max_cycles: int = 30,
                        required: bool = False,
                        clock_group: str = "default",
                        field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """Debug constraint for PENABLE transitions"""
        return create_debug_constraint("apb_penable", "debug_penable_activity", max_cycles, clock_group, field_config)

    @staticmethod
    def write_data_changes(max_cycles: int = 25,
                          required: bool = False,
                          clock_group: str = "default",
                          field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """Debug constraint for write data activity"""
        events = [
            create_temporal_event("write_type", create_static_pattern("apb_pwrite", 1)),
            create_temporal_event("psel_active", create_static_pattern("apb_psel", 1))
        ]

        return TemporalConstraint(
            name="debug_write_data",
            events=events,
            temporal_relation=TemporalRelation.CONCURRENT,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=[
                "apb_psel", "apb_penable", "apb_pready", "apb_pwrite",
                "apb_paddr", "apb_pwdata", "apb_pstrb"
            ],
            max_matches=3,
            field_config=field_config,
            protocol_hint="apb"
        )

    @staticmethod
    def read_data_capture(max_cycles: int = 25,
                         required: bool = False,
                         clock_group: str = "default",
                         field_config: Optional['FieldConfig'] = None) -> TemporalConstraint:
        """Debug constraint for read data capture"""
        events = [
            create_temporal_event("read_type", create_static_pattern("apb_pwrite", 0)),
            create_temporal_event("ready_response", create_transition_pattern("apb_pready", 0, 1))
        ]

        return TemporalConstraint(
            name="debug_read_data",
            events=events,
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=max_cycles,
            required=required,
            clock_group=clock_group,
            signals_to_show=[
                "apb_psel", "apb_penable", "apb_pready", "apb_pwrite",
                "apb_paddr", "apb_prdata", "apb_pprot", "apb_pslverr"
            ],
            max_matches=3,
            field_config=field_config,
            protocol_hint="apb"
        )


class APBPresets:
    """Preset constraint collections with improved sequences"""

    @staticmethod
    def basic_rw_test(max_cycles: int = 25,  # Increased
                     clock_group: str = "default",
                     field_config: Optional['FieldConfig'] = None) -> List[TemporalConstraint]:
        """Basic read/write test with complete sequences"""
        return [
            APBConstraints.write_transaction(max_cycles=max_cycles, required=True, clock_group=clock_group, field_config=field_config),
            APBConstraints.read_transaction(max_cycles=max_cycles, required=True, clock_group=clock_group, field_config=field_config),
        ]

    @staticmethod
    def setup_boundaries_for_basic_rw(wave_solver: TemporalConstraintSolver, field_config: Optional['FieldConfig'] = None):
        """Set up boundaries for basic read/write test"""
        constraint_names = ['apb_write_sequence', 'apb_read_sequence']
        setup_apb_boundaries(wave_solver, constraint_names, field_config)

    @staticmethod
    def comprehensive_test(max_cycles: int = 25,  # Increased
                          clock_group: str = "default",
                          field_config: Optional['FieldConfig'] = None) -> List[TemporalConstraint]:
        """Comprehensive test with detailed sequence analysis"""
        return [
            # Required basic transactions
            APBConstraints.write_transaction(max_cycles=max_cycles, required=True, clock_group=clock_group, field_config=field_config),
            APBConstraints.read_transaction(max_cycles=max_cycles, required=True, clock_group=clock_group, field_config=field_config),

            # Phase analysis (optional)
            APBConstraints.setup_phase(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBConstraints.access_phase(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),

            # Completion analysis (optional)
            APBConstraints.write_completion(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBConstraints.read_completion(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),

            # Complete transaction sequences (optional)
            APBConstraints.complete_transaction(max_cycles=max_cycles+5, required=False, clock_group=clock_group, field_config=field_config),

            # Error handling
            APBConstraints.error_transaction(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config)
        ]

    @staticmethod
    def setup_boundaries_for_comprehensive(wave_solver: TemporalConstraintSolver, field_config: Optional['FieldConfig'] = None):
        """Set up boundaries for comprehensive test"""
        constraint_names = [
            'apb_write_sequence', 'apb_read_sequence', 'apb_setup', 'apb_access',
            'apb_write_completion', 'apb_read_completion', 'apb_complete_transaction',
            'apb_error'
        ]
        setup_apb_boundaries(wave_solver, constraint_names, field_config)

    @staticmethod
    def debug_test(max_cycles: int = 30,
                  clock_group: str = "default",
                  field_config: Optional['FieldConfig'] = None) -> List[TemporalConstraint]:
        """Debug-focused constraints for troubleshooting"""
        return [
            # Basic activity detection
            APBDebug.psel_activity(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBDebug.pready_activity(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBDebug.penable_activity(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),

            # Data activity
            APBDebug.write_data_changes(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBDebug.read_data_capture(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config)
        ]

    @staticmethod
    def setup_boundaries_for_debug(wave_solver: TemporalConstraintSolver, field_config: Optional['FieldConfig'] = None):
        """Set up boundaries for debug test"""
        constraint_names = [
            'debug_psel_activity', 'debug_pready_activity', 'debug_penable_activity',
            'debug_write_data', 'debug_read_data'
        ]
        setup_apb_boundaries(wave_solver, constraint_names, field_config)

    @staticmethod
    def timing_analysis_test(max_cycles: int = 30,  # Increased
                           clock_group: str = "default",
                           field_config: Optional['FieldConfig'] = None) -> List[TemporalConstraint]:
        """Timing and protocol compliance analysis"""
        return [
            # Complete transaction sequences for timing analysis
            APBConstraints.write_transaction(max_cycles=max_cycles, required=True, clock_group=clock_group, field_config=field_config),
            APBConstraints.read_transaction(max_cycles=max_cycles, required=True, clock_group=clock_group, field_config=field_config),

            # Protocol phase sequences
            APBConstraints.setup_phase(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBConstraints.access_phase(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),

            # Wait state analysis
            APBConstraints.wait_state_sequence(max_cycles=max_cycles+5, required=False, clock_group=clock_group, field_config=field_config),

            # Complete sequences with termination
            APBConstraints.complete_transaction(max_cycles=max_cycles+5, required=False, clock_group=clock_group, field_config=field_config)
        ]

    @staticmethod
    def setup_boundaries_for_timing_analysis(wave_solver: TemporalConstraintSolver, field_config: Optional['FieldConfig'] = None):
        """Set up boundaries for timing analysis test"""
        constraint_names = [
            'apb_write_sequence', 'apb_read_sequence', 'apb_setup', 'apb_access',
            'apb_wait_state', 'apb_complete_transaction'
        ]
        setup_apb_boundaries(wave_solver, constraint_names, field_config)

    @staticmethod
    def error_focused_test(max_cycles: int = 25,  # Increased
                          clock_group: str = "default",
                          field_config: Optional['FieldConfig'] = None) -> List[TemporalConstraint]:
        """Error conditions and edge cases focus"""
        return [
            # Basic transactions (may or may not complete)
            APBConstraints.write_transaction(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBConstraints.read_transaction(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),

            # Error detection
            APBConstraints.error_transaction(max_cycles=max_cycles, required=True, clock_group=clock_group, field_config=field_config),

            # Wait states (might indicate problems)
            APBConstraints.wait_state_sequence(max_cycles=max_cycles+10, required=False, clock_group=clock_group, field_config=field_config)
        ]

    @staticmethod
    def setup_boundaries_for_error_focused(wave_solver: TemporalConstraintSolver, field_config: Optional['FieldConfig'] = None):
        """Set up boundaries for error focused test"""
        constraint_names = [
            'apb_write_sequence', 'apb_read_sequence', 'apb_error', 'apb_wait_state'
        ]
        setup_apb_boundaries(wave_solver, constraint_names, field_config)


# Helper function with improvements
def setup_apb_constraints_with_boundaries(wave_solver: TemporalConstraintSolver,
                                                  preset_name: str = "basic_rw",
                                                  max_cycles: int = 30,  # Increased default for post-match
                                                  clock_group: str = "default",
                                                  data_width: int = 32,
                                                  addr_width: int = 32,
                                                  enable_packet_callbacks: bool = True,
                                                  use_signal_names: bool = True,
                                                  post_match_cycles: int = 2,
                                                  error_required: bool = True):
    """
    Helper function to set up APB constraints with post-match extension.

    Args:
        wave_solver: TemporalConstraintSolver instance
        preset_name: Name of preset ('basic_rw', 'comprehensive', 'debug', 'timing', 'error')
        max_cycles: Maximum cycles for constraints
        clock_group: Clock group name
        data_width: APB data width
        addr_width: APB address width
        enable_packet_callbacks: Whether to enable APB packet-based callbacks
        use_signal_names: Whether to use signal names (True) vs descriptions (False)
        post_match_cycles: Extra cycles to include after sequence match (default: 2)
        error_required: Whether error scenario is required (False for master tests)

    Returns:
        Number of constraints added
    """

    # Create FieldConfig for APB with signal name preference
    field_config = get_apb_field_config(data_width, addr_width, data_width // 8, use_signal_names)

    # Configure protocol-specific FieldConfig in solver
    if field_config and hasattr(wave_solver, 'configure_protocol_field_config'):
        wave_solver.configure_protocol_field_config("apb", field_config)

    # Set up packet-based WaveJSON callbacks if enabled
    if enable_packet_callbacks and hasattr(wave_solver, 'add_packet_based_callback'):
        def apb_packet_callback(packet_obj, signal_data, temporal_solution):
            """APB packet-based WaveJSON callback"""
            try:
                from CocoTBFramework.components.wavedrom.utility import create_wavejson_from_packet_and_signals
                return create_wavejson_from_packet_and_signals(
                    packet_obj, signal_data, temporal_solution,
                    title=f"APB {packet_obj.direction} Transaction",
                    interface_prefix="apb"
                )
            except Exception as e:
                print(f"APB packet callback failed: {e}")
                return None

        # Register packet callbacks for write and read sequences
        wave_solver.add_packet_based_callback("apb_write_sequence", APBPacket, apb_packet_callback)
        wave_solver.add_packet_based_callback("apb_read_sequence", APBPacket, apb_packet_callback)

    # Add constraints based on preset
    if preset_name == "basic_rw":
        constraints = [
            create_apb_write_sequence_constraint(max_cycles, True, clock_group, field_config, post_match_cycles),
            create_apb_read_sequence_constraint(max_cycles, True, clock_group, field_config, post_match_cycles)
        ]
        for constraint in constraints:
            wave_solver.add_constraint(constraint)
        # Skip boundary setup for main sequences to avoid early termination
        # setup_apb_boundaries(wave_solver, ['apb_write_sequence', 'apb_read_sequence'], field_config)

    elif preset_name == "comprehensive":
        # User-requested 7 focused scenarios: basic write/read, back-to-back writes/reads,
        # write-to-read, read-to-write, and error
        constraints = [
            # 1. Basic write
            create_apb_write_sequence_constraint(max_cycles, True, clock_group, field_config, post_match_cycles),
            # 2. Basic read
            create_apb_read_sequence_constraint(max_cycles, True, clock_group, field_config, post_match_cycles),
            # 3. Back-to-back writes
            APBConstraints.back_to_back_writes(max_cycles=max_cycles+10, required=True, clock_group=clock_group, field_config=field_config, post_match_cycles=post_match_cycles),
            # 4. Back-to-back reads
            APBConstraints.back_to_back_reads(max_cycles=max_cycles+10, required=True, clock_group=clock_group, field_config=field_config, post_match_cycles=post_match_cycles),
            # 5. Write-to-read transition
            APBConstraints.write_to_read(max_cycles=max_cycles+10, required=True, clock_group=clock_group, field_config=field_config, post_match_cycles=post_match_cycles),
            # 6. Read-to-write transition
            APBConstraints.read_to_write(max_cycles=max_cycles+10, required=True, clock_group=clock_group, field_config=field_config, post_match_cycles=post_match_cycles),
            # 7. Error response (optional for master tests since they don't control errors)
            APBConstraints.error_transaction(max_cycles=max_cycles, required=error_required, clock_group=clock_group, field_config=field_config)
        ]
        for constraint in constraints:
            wave_solver.add_constraint(constraint)
        # Set boundaries only for single-transaction constraints
        # Multi-transaction constraints span across PSEL edges, so don't use auto-boundary
        single_txn_constraints = [
            'apb_write_sequence', 'apb_read_sequence', 'apb_error'
        ]
        setup_apb_boundaries(wave_solver, single_txn_constraints, field_config)

    elif preset_name == "debug":
        constraints = APBPresets.debug_test(max_cycles, clock_group, field_config)
        for constraint in constraints:
            wave_solver.add_constraint(constraint)
        APBPresets.setup_boundaries_for_debug(wave_solver, field_config)

    elif preset_name == "timing":
        constraints = [
            # Main sequences with post-match extension
            create_apb_write_sequence_constraint(max_cycles, True, clock_group, field_config, post_match_cycles),
            create_apb_read_sequence_constraint(max_cycles, True, clock_group, field_config, post_match_cycles),

            # Other timing constraints
            APBConstraints.setup_phase(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBConstraints.access_phase(max_cycles=max_cycles, required=False, clock_group=clock_group, field_config=field_config),
            APBConstraints.wait_state_sequence(max_cycles=max_cycles+5, required=False, clock_group=clock_group, field_config=field_config),
            APBConstraints.complete_transaction(max_cycles=max_cycles+5, required=False, clock_group=clock_group, field_config=field_config)
        ]
        for constraint in constraints:
            wave_solver.add_constraint(constraint)
        # Boundaries only for non-main sequences
        timing_constraints = ['apb_setup', 'apb_access', 'apb_wait_state', 'apb_complete_transaction']
        setup_apb_boundaries(wave_solver, timing_constraints, field_config)

    elif preset_name == "error":
        constraints = APBPresets.error_focused_test(max_cycles, clock_group, field_config)
        for constraint in constraints:
            wave_solver.add_constraint(constraint)
        APBPresets.setup_boundaries_for_error_focused(wave_solver, field_config)

    else:
        raise ValueError(f"Unknown preset: {preset_name}. Available: basic_rw, comprehensive, debug, timing, error")

    return len(constraints)


class APBWaveDromTemplate:
    """
    Dead-simple APB wavedrom with automatic signal binding.

    Uses SignalResolver methodology for automatic signal discovery with
    manual override capability.
    """

    def __init__(self, dut,
                 signal_prefix: str = "apb_",
                 data_width: int = 32,
                 addr_width: int = 32,
                 preset: str = "comprehensive",
                 bus_name: str = '',
                 signal_map: Optional[Dict[str, str]] = None,
                 clock_signal = None):
        """
        Initialize APB wavedrom with automatic signal binding.

        Args:
            dut: CocoTB DUT handle
            signal_prefix: Signal prefix (e.g., 'apb_', 's_apb_', '')
            data_width: APB data width (default: 32)
            addr_width: APB address width (default: 32)
            preset: Constraint preset ('basic_rw', 'comprehensive', 'debug', 'timing', 'error')
            bus_name: Bus/channel name if signals have additional prefix
            signal_map: Manual signal override (e.g., {'psel': 'my_psel', 'penable': 'my_penable', ...})
            clock_signal: Clock signal (auto-detected if None)

        Example:
            # Automatic discovery (most common):
            apb_wave = APBWaveDromTemplate(dut, signal_prefix="apb_", data_width=32, addr_width=32)

            # Manual override for non-standard naming:
            apb_wave = APBWaveDromTemplate(
                dut,
                signal_prefix="",
                signal_map={
                    'psel': 'custom_psel',
                    'penable': 'custom_penable',
                    'pwrite': 'wr_en',
                    'pready': 'slave_ready',
                    'paddr': 'address',
                    'pwdata': 'write_data',
                    'prdata': 'read_data'
                }
            )
        """
        self.dut = dut
        self.signal_prefix = signal_prefix

        # Create field configuration
        self.field_config = get_apb_field_config(
            data_width=data_width,
            addr_width=addr_width,
            strb_width=data_width // 8,
            use_signal_names=True
        )

        # Create wave generator
        self.wave_generator = create_apb_wavejson_generator(
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
            clock_signal = (getattr(dut, 'pclk', None) or
                          getattr(dut, 'apb_pclk', None) or
                          getattr(dut, 'i_clk', None) or
                          getattr(dut, 'clk', None))

        if clock_signal is None:
            raise ValueError("Could not auto-detect clock signal. Please provide clock_signal parameter.")

        # Add clock group
        self.wave_solver.add_clock_group('default', clock_signal)

        # 🎯 AUTO-BIND ALL SIGNALS (The magic!)
        self.num_signals = self.wave_solver.auto_bind_signals(
            protocol_type='apb',
            signal_prefix=signal_prefix,
            bus_name=bus_name,
            field_config=self.field_config,
            signal_map=signal_map
        )

        # Setup constraints with boundaries
        self.num_constraints = setup_apb_constraints_with_boundaries(
            wave_solver=self.wave_solver,
            preset_name=preset,
            data_width=data_width,
            addr_width=addr_width
        )

        dut._log.info(f"✓ APB wavedrom configured: {self.num_signals} signals, {self.num_constraints} constraints")

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


# Export classes and functions
__all__ = [
    # Signal lists and utilities
    'create_apb_signals_list',
    'get_apb_boundary_pattern',

    # Constraint builders
    'create_apb_write_sequence_constraint',
    'create_apb_read_sequence_constraint',
    'create_apb_complete_transaction_constraint',
    'check_apb_protocol_compliance',

    # Boundary management
    'setup_apb_boundaries',

    # Constraint classes
    'APBConstraints',
    'APBDebug',
    'APBPresets',

    # Setup function
    'setup_apb_constraints_with_boundaries',

    # Template class (NEW)
    'APBWaveDromTemplate',
]
