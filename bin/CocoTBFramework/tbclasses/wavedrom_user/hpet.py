# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETConstraints
# Purpose: HPET Constraints for Wavedrom Timing Diagram Generation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-06

"""
HPET (High Precision Event Timer) Constraints for WaveDrom Generation

This module provides temporal constraints for capturing HPET timing behaviors:
1. APB register access (write config, read counter)
2. Timer fire events (one-shot and periodic)
3. Interrupt generation and clearing
4. CDC crossing between APB (pclk) and HPET (hpet_clk) domains

Signal Hierarchy:
- External: APB interface, timer_irq outputs
- Internal: main_counter, timer_comparator, timer_match, timer_fire
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
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


# =============================================================================
# HPET Signal Lists for Waveform Display
# =============================================================================

def create_hpet_apb_signals_list() -> List:
    """
    APB domain signals for HPET register access waveforms.
    Shows APB transaction with internal register effects.
    """
    return [
        "pclk",           # APB clock
        "presetn",        # APB reset
        {},               # Visual separator
        ["APB",
            "s_apb_PSEL",
            "s_apb_PENABLE",
            "s_apb_PREADY",
            "s_apb_PWRITE",
            "s_apb_PADDR",
            "s_apb_PWDATA",
            "s_apb_PRDATA"
        ],
        {},
        ["Internal",
            "hpet_enable",
            "counter_rdata"
        ]
    ]


def create_hpet_timer_signals_list(timer_id: int = 0) -> List:
    """
    HPET clock domain signals for timer operation waveforms.
    Shows timer comparator match and fire behavior.

    Args:
        timer_id: Timer index (0, 1, 2, ...)
    """
    return [
        "hpet_clk",       # HPET high-speed clock
        "hpet_resetn",    # HPET reset
        {},
        ["Counter",
            "hpet_enable",
            "r_main_counter"
        ],
        {},
        [f"Timer{timer_id}",
            f"timer_enable[{timer_id}]",
            f"timer_type[{timer_id}]",
            f"r_timer_comparator[{timer_id}]",
            f"w_timer_match[{timer_id}]",
            f"w_timer_fire[{timer_id}]"
        ],
        {},
        ["Interrupt",
            f"r_interrupt_status[{timer_id}]",
            f"timer_irq[{timer_id}]"
        ]
    ]


def create_hpet_cdc_signals_list() -> List:
    """
    Dual clock domain signals for CDC waveforms.
    Shows APB domain and HPET domain interaction.
    """
    return [
        {"name": "pclk", "wave": "p", "period": 1.0},      # APB clock (slower)
        {"name": "hpet_clk", "wave": "p", "period": 0.5},  # HPET clock (faster)
        {},
        "presetn",
        "hpet_resetn",
        {},
        ["APB Domain",
            "s_apb_PSEL",
            "s_apb_PENABLE",
            "s_apb_PREADY",
            "s_apb_PWRITE",
            "s_apb_PADDR",
            "s_apb_PWDATA"
        ],
        {},
        ["HPET Domain",
            "hpet_enable",
            "r_main_counter",
            "timer_irq"
        ]
    ]


def create_hpet_interrupt_signals_list(num_timers: int = 3) -> List:
    """
    Interrupt-focused signals for interrupt generation and clearing.

    Args:
        num_timers: Number of timers (2, 3, or 8)
    """
    signals = [
        "hpet_clk",
        "hpet_resetn",
        {},
        ["Counter",
            "hpet_enable",
            "r_main_counter"
        ],
        {}
    ]

    # Add timer signals for each timer
    for i in range(min(num_timers, 3)):  # Show up to 3 timers
        signals.append([f"Timer{i}",
            f"w_timer_fire[{i}]",
            f"r_interrupt_status[{i}]",
            f"timer_int_clear[{i}]",
            f"timer_irq[{i}]"
        ])

    return signals


# =============================================================================
# HPET Boundary Pattern
# =============================================================================

def get_hpet_apb_boundary_pattern():
    """APB transaction boundary pattern - all control signals idle"""
    return {
        's_apb_PSEL': 0,
        's_apb_PENABLE': 0,
        's_apb_PREADY': 0
    }


def get_hpet_timer_boundary_pattern():
    """Timer fire boundary pattern - no active fires"""
    return {
        'w_timer_fire': 0
    }


# =============================================================================
# HPET Constraint Builder Functions
# =============================================================================

def create_hpet_config_write_constraint(max_window: int = 20,
                                        required: bool = True,
                                        clock_group: str = "apb") -> TemporalConstraint:
    """
    HPET configuration write via APB.
    Captures: APB write transaction -> hpet_enable changes
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("s_apb_PSEL", 0, 1)),
        create_temporal_event("write_type", create_static_pattern("s_apb_PWRITE", 1)),
        create_temporal_event("enable_start", create_transition_pattern("s_apb_PENABLE", 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern("s_apb_PREADY", 0, 1))
    ]

    constraint = TemporalConstraint(
        name="hpet_config_write",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_hpet_apb_signals_list(),
        min_sequence_duration=3,
        max_sequence_duration=15,
        protocol_hint="apb"
    )
    constraint.post_match_cycles = 2
    return constraint


def create_hpet_counter_read_constraint(max_window: int = 20,
                                        required: bool = True,
                                        clock_group: str = "apb") -> TemporalConstraint:
    """
    HPET counter read via APB.
    Captures: APB read transaction -> counter_rdata captured
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("s_apb_PSEL", 0, 1)),
        create_temporal_event("read_type", create_static_pattern("s_apb_PWRITE", 0)),
        create_temporal_event("enable_start", create_transition_pattern("s_apb_PENABLE", 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern("s_apb_PREADY", 0, 1))
    ]

    constraint = TemporalConstraint(
        name="hpet_counter_read",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_hpet_apb_signals_list(),
        min_sequence_duration=3,
        max_sequence_duration=15,
        protocol_hint="apb"
    )
    constraint.post_match_cycles = 2
    return constraint


def create_hpet_timer_fire_constraint(timer_id: int = 0,
                                      max_window: int = 30,
                                      required: bool = True,
                                      clock_group: str = "hpet") -> TemporalConstraint:
    """
    One-shot timer fire event.
    Captures: counter approaching comparator -> match -> fire -> interrupt
    """
    events = [
        create_temporal_event("timer_enabled", create_static_pattern(f"timer_enable[{timer_id}]", 1)),
        create_temporal_event("match_rise", create_transition_pattern(f"w_timer_match[{timer_id}]", 0, 1)),
        create_temporal_event("fire_pulse", create_transition_pattern(f"w_timer_fire[{timer_id}]", 0, 1)),
        create_temporal_event("irq_assert", create_transition_pattern(f"timer_irq[{timer_id}]", 0, 1))
    ]

    return TemporalConstraint(
        name=f"hpet_timer{timer_id}_fire",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_hpet_timer_signals_list(timer_id),
        min_sequence_duration=2,
        max_sequence_duration=20,
        protocol_hint="hpet"
    )


def create_hpet_periodic_timer_constraint(timer_id: int = 0,
                                          max_window: int = 50,
                                          required: bool = False,
                                          clock_group: str = "hpet") -> TemporalConstraint:
    """
    Periodic timer - multiple fire events with comparator reload.
    Captures: fire -> comparator advances -> fire again
    """
    events = [
        create_temporal_event("timer_periodic", create_static_pattern(f"timer_type[{timer_id}]", 1)),
        create_temporal_event("first_fire", create_transition_pattern(f"w_timer_fire[{timer_id}]", 0, 1)),
        create_temporal_event("fire_fall", create_transition_pattern(f"w_timer_fire[{timer_id}]", 1, 0)),
        create_temporal_event("second_fire", create_transition_pattern(f"w_timer_fire[{timer_id}]", 0, 1))
    ]

    return TemporalConstraint(
        name=f"hpet_timer{timer_id}_periodic",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_hpet_timer_signals_list(timer_id),
        min_sequence_duration=5,
        max_sequence_duration=40,
        protocol_hint="hpet"
    )


def create_hpet_interrupt_clear_constraint(timer_id: int = 0,
                                           max_window: int = 25,
                                           required: bool = True,
                                           clock_group: str = "hpet") -> TemporalConstraint:
    """
    Interrupt clear (W1C) sequence.
    Captures: interrupt active -> clear pulse -> interrupt deasserts
    """
    events = [
        create_temporal_event("irq_active", create_static_pattern(f"timer_irq[{timer_id}]", 1)),
        create_temporal_event("clear_pulse", create_transition_pattern(f"timer_int_clear[{timer_id}]", 0, 1)),
        create_temporal_event("irq_deassert", create_transition_pattern(f"timer_irq[{timer_id}]", 1, 0))
    ]

    return TemporalConstraint(
        name=f"hpet_timer{timer_id}_int_clear",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_hpet_interrupt_signals_list(),
        min_sequence_duration=2,
        max_sequence_duration=15,
        protocol_hint="hpet"
    )


def create_hpet_timer_setup_constraint(timer_id: int = 0,
                                       max_window: int = 40,
                                       required: bool = False,
                                       clock_group: str = "apb") -> TemporalConstraint:
    """
    Timer setup sequence via APB.
    Captures: Write to TIMER_CONFIG -> Write to TIMER_COMPARATOR
    """
    events = [
        # First APB write (timer config)
        create_temporal_event("psel1_rise", create_transition_pattern("s_apb_PSEL", 0, 1)),
        create_temporal_event("psel1_fall", create_transition_pattern("s_apb_PSEL", 1, 0)),
        # Second APB write (comparator)
        create_temporal_event("psel2_rise", create_transition_pattern("s_apb_PSEL", 0, 1)),
    ]

    constraint = TemporalConstraint(
        name=f"hpet_timer{timer_id}_setup",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_hpet_apb_signals_list(),
        min_sequence_duration=4,
        protocol_hint="apb"
    )
    constraint.post_match_cycles = 3
    constraint.skip_boundary_detection = True
    return constraint


# =============================================================================
# HPETConstraints Class - Main API
# =============================================================================

class HPETConstraints:
    """HPET constraints for wavedrom timing diagram generation"""

    @staticmethod
    def config_write(max_cycles: int = 20,
                     required: bool = True,
                     clock_group: str = "apb") -> TemporalConstraint:
        """APB write to HPET configuration register"""
        return create_hpet_config_write_constraint(max_cycles, required, clock_group)

    @staticmethod
    def counter_read(max_cycles: int = 20,
                     required: bool = True,
                     clock_group: str = "apb") -> TemporalConstraint:
        """APB read of HPET main counter"""
        return create_hpet_counter_read_constraint(max_cycles, required, clock_group)

    @staticmethod
    def timer_fire(timer_id: int = 0,
                   max_cycles: int = 30,
                   required: bool = True,
                   clock_group: str = "hpet") -> TemporalConstraint:
        """One-shot timer fire event"""
        return create_hpet_timer_fire_constraint(timer_id, max_cycles, required, clock_group)

    @staticmethod
    def periodic_timer(timer_id: int = 0,
                       max_cycles: int = 50,
                       required: bool = False,
                       clock_group: str = "hpet") -> TemporalConstraint:
        """Periodic timer with multiple fires"""
        return create_hpet_periodic_timer_constraint(timer_id, max_cycles, required, clock_group)

    @staticmethod
    def interrupt_clear(timer_id: int = 0,
                        max_cycles: int = 25,
                        required: bool = True,
                        clock_group: str = "hpet") -> TemporalConstraint:
        """Interrupt clear (W1C) sequence"""
        return create_hpet_interrupt_clear_constraint(timer_id, max_cycles, required, clock_group)

    @staticmethod
    def timer_setup(timer_id: int = 0,
                    max_cycles: int = 40,
                    required: bool = False,
                    clock_group: str = "apb") -> TemporalConstraint:
        """Timer setup via back-to-back APB writes"""
        return create_hpet_timer_setup_constraint(timer_id, max_cycles, required, clock_group)


# =============================================================================
# HPETPresets - Preset Constraint Collections
# =============================================================================

class HPETPresets:
    """Preset constraint collections for common HPET test scenarios"""

    @staticmethod
    def basic_register_access(max_cycles: int = 25,
                              clock_group: str = "apb") -> List[TemporalConstraint]:
        """Basic APB register access - config write and counter read"""
        return [
            HPETConstraints.config_write(max_cycles=max_cycles, required=True, clock_group=clock_group),
            HPETConstraints.counter_read(max_cycles=max_cycles, required=True, clock_group=clock_group)
        ]

    @staticmethod
    def timer_operation(timer_id: int = 0,
                        max_cycles: int = 35,
                        clock_group: str = "hpet") -> List[TemporalConstraint]:
        """Timer operation - fire and interrupt clear"""
        return [
            HPETConstraints.timer_fire(timer_id=timer_id, max_cycles=max_cycles, required=True, clock_group=clock_group),
            HPETConstraints.interrupt_clear(timer_id=timer_id, max_cycles=max_cycles, required=True, clock_group=clock_group)
        ]

    @staticmethod
    def comprehensive(num_timers: int = 3,
                      max_cycles: int = 40) -> List[TemporalConstraint]:
        """Comprehensive HPET test - all scenarios"""
        constraints = [
            # APB register access
            HPETConstraints.config_write(max_cycles=max_cycles, required=True, clock_group="apb"),
            HPETConstraints.counter_read(max_cycles=max_cycles, required=True, clock_group="apb"),
            HPETConstraints.timer_setup(timer_id=0, max_cycles=max_cycles+10, required=False, clock_group="apb"),

            # Timer 0 operation
            HPETConstraints.timer_fire(timer_id=0, max_cycles=max_cycles, required=True, clock_group="hpet"),
            HPETConstraints.periodic_timer(timer_id=0, max_cycles=max_cycles+20, required=False, clock_group="hpet"),
            HPETConstraints.interrupt_clear(timer_id=0, max_cycles=max_cycles, required=True, clock_group="hpet"),
        ]

        # Add additional timer constraints if more than 1 timer
        if num_timers > 1:
            constraints.append(
                HPETConstraints.timer_fire(timer_id=1, max_cycles=max_cycles, required=False, clock_group="hpet")
            )

        return constraints


# =============================================================================
# Setup Helper Function
# =============================================================================

def setup_hpet_constraints_with_boundaries(wave_solver: TemporalConstraintSolver,
                                           preset_name: str = "comprehensive",
                                           num_timers: int = 3,
                                           max_cycles: int = 40):
    """
    Helper function to set up HPET constraints.

    Args:
        wave_solver: TemporalConstraintSolver instance
        preset_name: Name of preset ('basic_register', 'timer_operation', 'comprehensive')
        num_timers: Number of timers configured
        max_cycles: Maximum cycles for constraints

    Returns:
        Number of constraints added
    """

    if preset_name == "basic_register":
        constraints = HPETPresets.basic_register_access(max_cycles=max_cycles)
    elif preset_name == "timer_operation":
        constraints = HPETPresets.timer_operation(timer_id=0, max_cycles=max_cycles)
    elif preset_name == "comprehensive":
        constraints = HPETPresets.comprehensive(num_timers=num_timers, max_cycles=max_cycles)
    else:
        raise ValueError(f"Unknown preset: {preset_name}. Available: basic_register, timer_operation, comprehensive")

    for constraint in constraints:
        wave_solver.add_constraint(constraint)

    return len(constraints)


# =============================================================================
# Export
# =============================================================================

__all__ = [
    # Signal lists
    'create_hpet_apb_signals_list',
    'create_hpet_timer_signals_list',
    'create_hpet_cdc_signals_list',
    'create_hpet_interrupt_signals_list',

    # Boundary patterns
    'get_hpet_apb_boundary_pattern',
    'get_hpet_timer_boundary_pattern',

    # Constraint builders
    'create_hpet_config_write_constraint',
    'create_hpet_counter_read_constraint',
    'create_hpet_timer_fire_constraint',
    'create_hpet_periodic_timer_constraint',
    'create_hpet_interrupt_clear_constraint',
    'create_hpet_timer_setup_constraint',

    # Classes
    'HPETConstraints',
    'HPETPresets',

    # Setup function
    'setup_hpet_constraints_with_boundaries',
]
