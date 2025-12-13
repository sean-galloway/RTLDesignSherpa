# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GPIOConstraints
# Purpose: GPIO Constraints for Wavedrom Timing Diagram Generation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-06

"""
GPIO (General Purpose I/O) Constraints for WaveDrom Generation

This module provides temporal constraints for capturing GPIO timing behaviors:
1. APB register access (direction, output, input read)
2. Input synchronization (2-stage sync)
3. Output operations (direct write, set, clear, toggle)
4. Interrupt generation (edge and level detection)
5. Interrupt clearing (W1C)

Signal Hierarchy:
- External: APB interface, GPIO pins (gpio_in, gpio_out, gpio_oe), irq
- Internal: sync stages, edge detection, interrupt logic
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
# GPIO Signal Lists for Waveform Display
# =============================================================================

def create_gpio_apb_signals_list() -> List:
    """
    APB domain signals for GPIO register access waveforms.
    Shows APB transaction with internal register effects.
    """
    return [
        "clk",
        "rst_n",
        {},
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
            "cfg_gpio_enable",
            "cfg_direction",
            "cfg_output_data"
        ]
    ]


def create_gpio_output_signals_list() -> List:
    """
    GPIO output operation signals.
    Shows output data, atomic operations, and pin outputs.
    """
    return [
        "clk",
        "rst_n",
        {},
        ["Config",
            "cfg_gpio_enable",
            "cfg_direction",
            "cfg_output_data"
        ],
        {},
        ["Atomic Ops",
            "cfg_output_set",
            "cfg_output_clr",
            "cfg_output_tgl"
        ],
        {},
        ["Output",
            "r_output_data",
            "gpio_out",
            "gpio_oe"
        ]
    ]


def create_gpio_input_signals_list() -> List:
    """
    GPIO input synchronization signals.
    Shows multi-stage synchronizer operation.
    """
    return [
        "clk",
        "rst_n",
        {},
        ["GPIO Pins",
            "gpio_in"
        ],
        {},
        ["Sync Pipeline",
            "r_sync_stage[0]",
            "r_sync_stage[1]",
            "w_gpio_sync"
        ],
        {},
        ["Status",
            "sts_input_data"
        ]
    ]


def create_gpio_interrupt_signals_list() -> List:
    """
    GPIO interrupt generation signals.
    Shows edge detection and interrupt generation.
    """
    return [
        "clk",
        "rst_n",
        {},
        ["Input",
            "gpio_in",
            "w_gpio_sync",
            "r_gpio_prev"
        ],
        {},
        ["Edge Detect",
            "w_rising_edge",
            "w_falling_edge",
            "w_any_edge"
        ],
        {},
        ["Config",
            "cfg_int_enable",
            "cfg_int_type",
            "cfg_int_polarity",
            "cfg_int_enable_pins"
        ],
        {},
        ["Interrupt",
            "w_raw_int",
            "sts_int_pending",
            "irq"
        ]
    ]


def create_gpio_full_signals_list() -> List:
    """
    Complete GPIO signal set for comprehensive waveforms.
    Shows APB, GPIO pins, and interrupt in one diagram.
    """
    return [
        "clk",
        "rst_n",
        {},
        ["APB",
            "s_apb_PSEL",
            "s_apb_PENABLE",
            "s_apb_PREADY",
            "s_apb_PWRITE",
            "s_apb_PADDR",
            "s_apb_PWDATA"
        ],
        {},
        ["GPIO Pins",
            "gpio_in",
            "gpio_out",
            "gpio_oe"
        ],
        {},
        ["Interrupt",
            "sts_int_pending",
            "irq"
        ]
    ]


# =============================================================================
# GPIO Boundary Patterns
# =============================================================================

def get_gpio_apb_boundary_pattern():
    """APB transaction boundary pattern"""
    return {
        's_apb_PSEL': 0,
        's_apb_PENABLE': 0,
        's_apb_PREADY': 0
    }


def get_gpio_interrupt_boundary_pattern():
    """Interrupt boundary pattern"""
    return {
        'irq': 0
    }


# =============================================================================
# GPIO Constraint Builder Functions
# =============================================================================

def create_gpio_direction_write_constraint(max_window: int = 20,
                                           required: bool = True,
                                           clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO direction register write via APB.
    Captures: APB write -> direction changes -> gpio_oe updates
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("s_apb_PSEL", 0, 1)),
        create_temporal_event("write_type", create_static_pattern("s_apb_PWRITE", 1)),
        create_temporal_event("enable_start", create_transition_pattern("s_apb_PENABLE", 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern("s_apb_PREADY", 0, 1))
    ]

    constraint = TemporalConstraint(
        name="gpio_direction_write",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_apb_signals_list(),
        min_sequence_duration=3,
        max_sequence_duration=15,
        protocol_hint="apb"
    )
    constraint.post_match_cycles = 2
    return constraint


def create_gpio_output_write_constraint(max_window: int = 20,
                                        required: bool = True,
                                        clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO output register write via APB.
    Captures: APB write -> output data changes -> gpio_out updates
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("s_apb_PSEL", 0, 1)),
        create_temporal_event("write_type", create_static_pattern("s_apb_PWRITE", 1)),
        create_temporal_event("enable_start", create_transition_pattern("s_apb_PENABLE", 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern("s_apb_PREADY", 0, 1))
    ]

    constraint = TemporalConstraint(
        name="gpio_output_write",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_output_signals_list(),
        min_sequence_duration=3,
        max_sequence_duration=15,
        protocol_hint="apb"
    )
    constraint.post_match_cycles = 2
    return constraint


def create_gpio_input_read_constraint(max_window: int = 20,
                                      required: bool = True,
                                      clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO input register read via APB.
    Captures: APB read -> synchronized input returned
    """
    events = [
        create_temporal_event("psel_start", create_transition_pattern("s_apb_PSEL", 0, 1)),
        create_temporal_event("read_type", create_static_pattern("s_apb_PWRITE", 0)),
        create_temporal_event("enable_start", create_transition_pattern("s_apb_PENABLE", 0, 1)),
        create_temporal_event("ready_response", create_transition_pattern("s_apb_PREADY", 0, 1))
    ]

    constraint = TemporalConstraint(
        name="gpio_input_read",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_apb_signals_list(),
        min_sequence_duration=3,
        max_sequence_duration=15,
        protocol_hint="apb"
    )
    constraint.post_match_cycles = 2
    return constraint


def create_gpio_atomic_set_constraint(max_window: int = 15,
                                      required: bool = False,
                                      clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO atomic SET operation.
    Captures: set pulse -> output bit goes high
    """
    events = [
        create_temporal_event("set_pulse", create_transition_pattern("cfg_output_set", 0, 1)),
        create_temporal_event("output_high", create_static_pattern("r_output_data", 1))
    ]

    return TemporalConstraint(
        name="gpio_atomic_set",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_output_signals_list(),
        min_sequence_duration=1,
        max_sequence_duration=10,
        protocol_hint="gpio"
    )


def create_gpio_atomic_clear_constraint(max_window: int = 15,
                                        required: bool = False,
                                        clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO atomic CLEAR operation.
    Captures: clear pulse -> output bit goes low
    """
    events = [
        create_temporal_event("clr_pulse", create_transition_pattern("cfg_output_clr", 0, 1)),
        create_temporal_event("output_low", create_static_pattern("r_output_data", 0))
    ]

    return TemporalConstraint(
        name="gpio_atomic_clear",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_output_signals_list(),
        min_sequence_duration=1,
        max_sequence_duration=10,
        protocol_hint="gpio"
    )


def create_gpio_atomic_toggle_constraint(max_window: int = 15,
                                         required: bool = False,
                                         clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO atomic TOGGLE operation.
    Captures: toggle pulse -> output bit inverts
    """
    events = [
        create_temporal_event("tgl_pulse", create_transition_pattern("cfg_output_tgl", 0, 1)),
    ]

    return TemporalConstraint(
        name="gpio_atomic_toggle",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_output_signals_list(),
        min_sequence_duration=1,
        max_sequence_duration=10,
        protocol_hint="gpio"
    )


def create_gpio_rising_edge_int_constraint(max_window: int = 25,
                                           required: bool = True,
                                           clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO rising edge interrupt detection.
    Captures: input goes high -> edge detected -> interrupt asserts
    """
    events = [
        create_temporal_event("input_rise", create_transition_pattern("w_gpio_sync", 0, 1)),
        create_temporal_event("edge_detect", create_transition_pattern("w_rising_edge", 0, 1)),
        create_temporal_event("irq_assert", create_transition_pattern("irq", 0, 1))
    ]

    return TemporalConstraint(
        name="gpio_rising_edge_int",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_interrupt_signals_list(),
        min_sequence_duration=2,
        max_sequence_duration=15,
        protocol_hint="gpio"
    )


def create_gpio_falling_edge_int_constraint(max_window: int = 25,
                                            required: bool = True,
                                            clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO falling edge interrupt detection.
    Captures: input goes low -> edge detected -> interrupt asserts
    """
    events = [
        create_temporal_event("input_fall", create_transition_pattern("w_gpio_sync", 1, 0)),
        create_temporal_event("edge_detect", create_transition_pattern("w_falling_edge", 0, 1)),
        create_temporal_event("irq_assert", create_transition_pattern("irq", 0, 1))
    ]

    return TemporalConstraint(
        name="gpio_falling_edge_int",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_interrupt_signals_list(),
        min_sequence_duration=2,
        max_sequence_duration=15,
        protocol_hint="gpio"
    )


def create_gpio_interrupt_clear_constraint(max_window: int = 25,
                                           required: bool = True,
                                           clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO interrupt clear (W1C) sequence.
    Captures: APB write to INT_STATUS -> interrupt clears
    """
    events = [
        create_temporal_event("irq_active", create_static_pattern("irq", 1)),
        create_temporal_event("psel_start", create_transition_pattern("s_apb_PSEL", 0, 1)),
        create_temporal_event("write_type", create_static_pattern("s_apb_PWRITE", 1)),
        create_temporal_event("irq_clear", create_transition_pattern("irq", 1, 0))
    ]

    return TemporalConstraint(
        name="gpio_interrupt_clear",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_full_signals_list(),
        min_sequence_duration=3,
        max_sequence_duration=20,
        protocol_hint="apb"
    )


def create_gpio_input_sync_constraint(max_window: int = 20,
                                      required: bool = False,
                                      clock_group: str = "default") -> TemporalConstraint:
    """
    GPIO input synchronization pipeline.
    Captures: gpio_in change -> propagates through sync stages
    """
    events = [
        create_temporal_event("input_change", create_transition_pattern("gpio_in", 0, 1)),
    ]

    return TemporalConstraint(
        name="gpio_input_sync",
        events=events,
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=max_window,
        required=required,
        clock_group=clock_group,
        signals_to_show=create_gpio_input_signals_list(),
        min_sequence_duration=2,
        max_sequence_duration=10,
        protocol_hint="gpio"
    )


# =============================================================================
# GPIOConstraints Class - Main API
# =============================================================================

class GPIOConstraints:
    """GPIO constraints for wavedrom timing diagram generation"""

    @staticmethod
    def direction_write(max_cycles: int = 20,
                        required: bool = True,
                        clock_group: str = "default") -> TemporalConstraint:
        """APB write to GPIO_DIRECTION register"""
        return create_gpio_direction_write_constraint(max_cycles, required, clock_group)

    @staticmethod
    def output_write(max_cycles: int = 20,
                     required: bool = True,
                     clock_group: str = "default") -> TemporalConstraint:
        """APB write to GPIO_OUTPUT register"""
        return create_gpio_output_write_constraint(max_cycles, required, clock_group)

    @staticmethod
    def input_read(max_cycles: int = 20,
                   required: bool = True,
                   clock_group: str = "default") -> TemporalConstraint:
        """APB read of GPIO_INPUT register"""
        return create_gpio_input_read_constraint(max_cycles, required, clock_group)

    @staticmethod
    def atomic_set(max_cycles: int = 15,
                   required: bool = False,
                   clock_group: str = "default") -> TemporalConstraint:
        """Atomic SET operation"""
        return create_gpio_atomic_set_constraint(max_cycles, required, clock_group)

    @staticmethod
    def atomic_clear(max_cycles: int = 15,
                     required: bool = False,
                     clock_group: str = "default") -> TemporalConstraint:
        """Atomic CLEAR operation"""
        return create_gpio_atomic_clear_constraint(max_cycles, required, clock_group)

    @staticmethod
    def atomic_toggle(max_cycles: int = 15,
                      required: bool = False,
                      clock_group: str = "default") -> TemporalConstraint:
        """Atomic TOGGLE operation"""
        return create_gpio_atomic_toggle_constraint(max_cycles, required, clock_group)

    @staticmethod
    def rising_edge_interrupt(max_cycles: int = 25,
                              required: bool = True,
                              clock_group: str = "default") -> TemporalConstraint:
        """Rising edge interrupt detection"""
        return create_gpio_rising_edge_int_constraint(max_cycles, required, clock_group)

    @staticmethod
    def falling_edge_interrupt(max_cycles: int = 25,
                               required: bool = True,
                               clock_group: str = "default") -> TemporalConstraint:
        """Falling edge interrupt detection"""
        return create_gpio_falling_edge_int_constraint(max_cycles, required, clock_group)

    @staticmethod
    def interrupt_clear(max_cycles: int = 25,
                        required: bool = True,
                        clock_group: str = "default") -> TemporalConstraint:
        """Interrupt clear (W1C) sequence"""
        return create_gpio_interrupt_clear_constraint(max_cycles, required, clock_group)

    @staticmethod
    def input_sync(max_cycles: int = 20,
                   required: bool = False,
                   clock_group: str = "default") -> TemporalConstraint:
        """Input synchronization pipeline"""
        return create_gpio_input_sync_constraint(max_cycles, required, clock_group)


# =============================================================================
# GPIOPresets - Preset Constraint Collections
# =============================================================================

class GPIOPresets:
    """Preset constraint collections for common GPIO test scenarios"""

    @staticmethod
    def basic_io(max_cycles: int = 25,
                 clock_group: str = "default") -> List[TemporalConstraint]:
        """Basic I/O operations - direction, output, input"""
        return [
            GPIOConstraints.direction_write(max_cycles=max_cycles, required=True, clock_group=clock_group),
            GPIOConstraints.output_write(max_cycles=max_cycles, required=True, clock_group=clock_group),
            GPIOConstraints.input_read(max_cycles=max_cycles, required=True, clock_group=clock_group)
        ]

    @staticmethod
    def atomic_operations(max_cycles: int = 20,
                          clock_group: str = "default") -> List[TemporalConstraint]:
        """Atomic operations - set, clear, toggle"""
        return [
            GPIOConstraints.atomic_set(max_cycles=max_cycles, required=True, clock_group=clock_group),
            GPIOConstraints.atomic_clear(max_cycles=max_cycles, required=True, clock_group=clock_group),
            GPIOConstraints.atomic_toggle(max_cycles=max_cycles, required=True, clock_group=clock_group)
        ]

    @staticmethod
    def interrupt_handling(max_cycles: int = 30,
                           clock_group: str = "default") -> List[TemporalConstraint]:
        """Interrupt handling - edge detection and clearing"""
        return [
            GPIOConstraints.rising_edge_interrupt(max_cycles=max_cycles, required=True, clock_group=clock_group),
            GPIOConstraints.falling_edge_interrupt(max_cycles=max_cycles, required=False, clock_group=clock_group),
            GPIOConstraints.interrupt_clear(max_cycles=max_cycles, required=True, clock_group=clock_group)
        ]

    @staticmethod
    def comprehensive(max_cycles: int = 30) -> List[TemporalConstraint]:
        """Comprehensive GPIO test - all scenarios"""
        constraints = []
        constraints.extend(GPIOPresets.basic_io(max_cycles=max_cycles))
        constraints.extend(GPIOPresets.atomic_operations(max_cycles=max_cycles))
        constraints.extend(GPIOPresets.interrupt_handling(max_cycles=max_cycles))
        constraints.append(GPIOConstraints.input_sync(max_cycles=max_cycles, required=False))
        return constraints


# =============================================================================
# Setup Helper Function
# =============================================================================

def setup_gpio_constraints_with_boundaries(wave_solver: TemporalConstraintSolver,
                                           preset_name: str = "comprehensive",
                                           max_cycles: int = 30):
    """
    Helper function to set up GPIO constraints.

    Args:
        wave_solver: TemporalConstraintSolver instance
        preset_name: Name of preset ('basic_io', 'atomic', 'interrupt', 'comprehensive')
        max_cycles: Maximum cycles for constraints

    Returns:
        Number of constraints added
    """

    if preset_name == "basic_io":
        constraints = GPIOPresets.basic_io(max_cycles=max_cycles)
    elif preset_name == "atomic":
        constraints = GPIOPresets.atomic_operations(max_cycles=max_cycles)
    elif preset_name == "interrupt":
        constraints = GPIOPresets.interrupt_handling(max_cycles=max_cycles)
    elif preset_name == "comprehensive":
        constraints = GPIOPresets.comprehensive(max_cycles=max_cycles)
    else:
        raise ValueError(f"Unknown preset: {preset_name}. Available: basic_io, atomic, interrupt, comprehensive")

    for constraint in constraints:
        wave_solver.add_constraint(constraint)

    return len(constraints)


# =============================================================================
# Export
# =============================================================================

__all__ = [
    # Signal lists
    'create_gpio_apb_signals_list',
    'create_gpio_output_signals_list',
    'create_gpio_input_signals_list',
    'create_gpio_interrupt_signals_list',
    'create_gpio_full_signals_list',

    # Boundary patterns
    'get_gpio_apb_boundary_pattern',
    'get_gpio_interrupt_boundary_pattern',

    # Constraint builders
    'create_gpio_direction_write_constraint',
    'create_gpio_output_write_constraint',
    'create_gpio_input_read_constraint',
    'create_gpio_atomic_set_constraint',
    'create_gpio_atomic_clear_constraint',
    'create_gpio_atomic_toggle_constraint',
    'create_gpio_rising_edge_int_constraint',
    'create_gpio_falling_edge_int_constraint',
    'create_gpio_interrupt_clear_constraint',
    'create_gpio_input_sync_constraint',

    # Classes
    'GPIOConstraints',
    'GPIOPresets',

    # Setup function
    'setup_gpio_constraints_with_boundaries',
]
