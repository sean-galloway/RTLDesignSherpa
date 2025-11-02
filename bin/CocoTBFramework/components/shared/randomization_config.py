# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RandomizationMode
# Purpose: Randomization Configuration for Protocol Verification
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Randomization Configuration for Protocol Verification

This module provides a flexible configuration framework for controlling
randomization behavior in protocol verification environments, using
FlexRandomizer as the underlying randomization engine.
"""

from enum import Enum, auto
from typing import Dict, List, Any, Optional, Union, Callable, Tuple
from dataclasses import dataclass, field
import random
from collections import defaultdict

from .flex_randomizer import FlexRandomizer


class RandomizationMode(Enum):
    """Defines possible randomization modes."""
    DETERMINISTIC = auto()  # Fixed values, not random
    CONSTRAINED = auto()    # Constrained random with weights
    DIRECTED = auto()       # Directed test patterns
    SEQUENCE = auto()       # Sequence of values in order
    CUSTOM = auto()         # Custom generator function


@dataclass
class FieldRandomizationConfig:
    """Configuration for randomizing a specific field."""
    enabled: bool = True
    mode: RandomizationMode = RandomizationMode.CONSTRAINED
    constraints: Optional[Dict] = None
    sequence: Optional[List[Any]] = None
    custom_generator: Optional[Callable] = None
    dependencies: List[str] = field(default_factory=list)

    def __post_init__(self):
        """Validate and set derived values after initialization."""
        # Set default constraints if not specified
        if self.mode == RandomizationMode.CONSTRAINED and self.constraints is None:
            # Default to uniform 0-1 distribution
            self.constraints = {
                "bins": [(0, 1)],
                "weights": [1.0]
            }

        # Ensure sequence is a list when in SEQUENCE mode
        if self.mode == RandomizationMode.SEQUENCE and self.sequence is None:
            self.sequence = [0]  # Default sequence

        # Validate dependencies
        if not isinstance(self.dependencies, list):
            self.dependencies = list(self.dependencies) if self.dependencies else []


class RandomizationConfig:
    """
    Configuration for randomizing protocol fields.

    This class provides a flexible framework for configuring how
    protocol fields are randomized, using FlexRandomizer as the
    underlying randomization engine.
    """

    def __init__(self, protocol_name: str = "generic", seed: Optional[int] = None):
        """
        Initialize the randomization configuration.

        Args:
            protocol_name: Name of the protocol (e.g., "AXI4", "APB")
            seed: Master random seed for reproducibility
        """
        self.protocol_name = protocol_name
        self.master_seed = seed
        self.field_configs = {}
        self.group_configs = defaultdict(list)
        self.enabled = True
        self.current_values = {}

        # Create FlexRandomizer constraints dictionary
        self._randomizer_constraints = {}
        self._randomizers = {}

        # Track sequence positions
        self._sequence_positions = defaultdict(int)

    def configure_field(self, field_name: str, config: FieldRandomizationConfig) -> 'RandomizationConfig':
        """
        Configure randomization for a specific field.

        Args:
            field_name: Name of the field to configure
            config: Field randomization configuration

        Returns:
            Self for method chaining
        """
        self.field_configs[field_name] = config

        # Update FlexRandomizer constraints based on configuration
        self._update_randomizer_constraints(field_name, config)

        return self

    def _update_randomizer_constraints(self, field_name: str, config: FieldRandomizationConfig):
        """
        Update FlexRandomizer constraints based on field configuration.

        Args:
            field_name: Field name
            config: Field configuration
        """
        if not config.enabled:
            return

        if config.mode == RandomizationMode.CONSTRAINED and config.constraints:
            # Use constraints directly for FlexRandomizer
            self._randomizer_constraints[field_name] = config.constraints
        elif config.mode == RandomizationMode.SEQUENCE and config.sequence:
            # Convert sequence to FlexRandomizer sequence format
            self._randomizer_constraints[field_name] = config.sequence
        elif config.mode == RandomizationMode.CUSTOM and config.custom_generator:
            # Use custom generator function
            self._randomizer_constraints[field_name] = config.custom_generator
        elif config.mode == RandomizationMode.DETERMINISTIC:
            # Use a fixed value (first value or 0)
            fixed_value = 0
            if config.sequence and len(config.sequence) > 0:
                fixed_value = config.sequence[0]
            self._randomizer_constraints[field_name] = [fixed_value]

    def _get_or_create_randomizer(self, field_name: str) -> FlexRandomizer:
        """
        Get or create a FlexRandomizer for a field.

        Args:
            field_name: Field name

        Returns:
            FlexRandomizer instance for the field
        """
        if field_name not in self._randomizers:
            # Check if we have constraints for this field
            constraints = {}
            if field_name in self._randomizer_constraints:
                constraints = {field_name: self._randomizer_constraints[field_name]}

            # Create new randomizer
            self._randomizers[field_name] = FlexRandomizer(constraints)

        return self._randomizers[field_name]

    def add_to_group(self, group_name: str, field_name: str) -> 'RandomizationConfig':
        """
        Add a field to a named group for collective configuration.

        Args:
            group_name: Group name
            field_name: Field to add to the group

        Returns:
            Self for method chaining
        """
        self.group_configs[group_name].append(field_name)
        return self

    def configure_group(self,
                        group_name: str,
                       **config_kwargs) -> 'RandomizationConfig':
        """
        Configure all fields in a group with the same settings.

        Args:
            group_name: Group to configure
            **config_kwargs: Configuration parameters to apply to all fields

        Returns:
            Self for method chaining
        """
        if group_name not in self.group_configs:
            return self

        for field_name in self.group_configs[group_name]:
            # Create or update configuration for this field
            if field_name in self.field_configs:
                # Update existing config
                for key, value in config_kwargs.items():
                    if hasattr(self.field_configs[field_name], key):
                        setattr(self.field_configs[field_name], key, value)
            else:
                # Create new config
                self.field_configs[field_name] = FieldRandomizationConfig(**config_kwargs)

            # Update randomizer constraints
            self._update_randomizer_constraints(field_name, self.field_configs[field_name])

        return self

    def get_field_config(self, field_name: str) -> FieldRandomizationConfig:
        """
        Get configuration for a specific field.

        Args:
            field_name: Name of the field

        Returns:
            Field randomization configuration
        """
        if field_name not in self.field_configs:
            # Return default configuration if not specified
            return FieldRandomizationConfig()

        return self.field_configs[field_name]

    def generate_value(self, field_name: str) -> Any:
        """
        Generate a random value for a field based on its configuration.

        Args:
            field_name: Name of the field

        Returns:
            Generated value according to the field's configuration
        """
        if not self.enabled:
            # Return default when randomization is disabled
            config = self.get_field_config(field_name)
            if config.sequence and len(config.sequence) > 0:
                return config.sequence[0]
            return 0

        config = self.get_field_config(field_name)

        # Check if all dependencies are satisfied
        if config.dependencies:
            for dep in config.dependencies:
                if dep not in self.current_values:
                    # Missing dependency, use default value
                    if config.sequence and len(config.sequence) > 0:
                        return config.sequence[0]
                    return 0

        # Generate based on randomization mode
        if config.mode == RandomizationMode.DETERMINISTIC:
            # Return fixed value
            if config.sequence and len(config.sequence) > 0:
                return config.sequence[0]
            return 0

        elif config.mode == RandomizationMode.CONSTRAINED:
            # Use FlexRandomizer to generate constrained random value
            randomizer = self._get_or_create_randomizer(field_name)
            values = randomizer.next()
            return values.get(field_name, 0)

        elif config.mode == RandomizationMode.SEQUENCE:
            # Return next value from sequence
            if not config.sequence:
                return 0

            pos = self._sequence_positions[field_name]
            value = config.sequence[pos % len(config.sequence)]

            # Update position for next time
            self._sequence_positions[field_name] = (pos + 1) % len(config.sequence)

            return value

        elif config.mode == RandomizationMode.CUSTOM:
            # Use custom generator
            if not config.custom_generator:
                return 0

            try:
                return config.custom_generator(self.current_values)
            except Exception as e:
                print(f"Error in custom generator for {field_name}: {e}")
                return 0

        # Default
        return 0

    def generate_values(self, field_names: List[str]) -> Dict[str, Any]:
        """
        Generate values for multiple fields at once.

        Args:
            field_names: List of field names

        Returns:
            Dictionary mapping field names to generated values
        """
        result = {}

        # Generate values in dependency order
        dependency_graph = self._build_dependency_graph(field_names)
        ordered_fields = self._topological_sort(dependency_graph)

        for field in ordered_fields:
            value = self.generate_value(field)
            result[field] = value
            self.current_values[field] = value

        return result

    def _build_dependency_graph(self, field_names: List[str]) -> Dict[str, List[str]]:
        """
        Build a dependency graph for fields.

        Args:
            field_names: List of field names

        Returns:
            Dictionary mapping fields to their dependents
        """
        graph = defaultdict(list)

        for field in field_names:
            config = self.get_field_config(field)
            for dep in config.dependencies:
                if dep in field_names:
                    graph[dep].append(field)

        return graph

    def _topological_sort(self, graph: Dict[str, List[str]]) -> List[str]:
        """
        Perform topological sorting of fields based on dependencies.

        Args:
            graph: Dependency graph

        Returns:
            List of fields in dependency order
        """
        # Identify all nodes
        nodes = set()
        for node, edges in graph.items():
            nodes.add(node)
            nodes.update(edges)

        # Find roots (nodes with no incoming edges)
        incoming_edges = defaultdict(int)
        for edges in graph.values():
            for edge in edges:
                incoming_edges[edge] += 1

        roots = [node for node in nodes if incoming_edges[node] == 0]

        # Sort
        result = []
        while roots:
            root = roots.pop(0)
            result.append(root)

            # Remove edges from this node
            if root in graph:
                for node in graph[root]:
                    incoming_edges[node] -= 1
                    if incoming_edges[node] == 0:
                        roots.append(node)

        # Check for cycles
        return list(nodes) if len(result) != len(nodes) else result

    def enable(self) -> 'RandomizationConfig':
        """
        Enable randomization.

        Returns:
            Self for method chaining
        """
        self.enabled = True
        return self

    def disable(self) -> 'RandomizationConfig':
        """
        Disable randomization.

        Returns:
            Self for method chaining
        """
        self.enabled = False
        return self

    def set_seed(self, seed: int) -> 'RandomizationConfig':
        """
        Set the master random seed.

        Args:
            seed: Random seed

        Returns:
            Self for method chaining
        """
        self.master_seed = seed

        # Recreate all randomizers with new seed
        self._randomizers.clear()
        random.seed(seed)  # Set Python's random seed

        return self

    def reset_sequences(self) -> 'RandomizationConfig':
        """
        Reset all sequence positions to start.

        Returns:
            Self for method chaining
        """
        self._sequence_positions.clear()
        return self

    def create_constrained_config(self,
                                field_name: str,
                                bins: List[Union[Tuple[int, int], List[Any]]],
                                weights: Optional[List[float]] = None) -> 'RandomizationConfig':
        """
        Create a constrained randomization configuration for a field.

        Args:
            field_name: Field to configure
            bins: List of value ranges or sets
            weights: Weights for each bin (optional)

        Returns:
            Self for method chaining
        """
        if weights is None:
            # Equal weights for all bins
            weights = [1.0] * len(bins)

        constraints = {
            "bins": bins,
            "weights": weights
        }

        config = FieldRandomizationConfig(
            mode=RandomizationMode.CONSTRAINED,
            constraints=constraints
        )

        return self.configure_field(field_name, config)

    def create_sequence_config(self,
                                field_name: str,
                                sequence: List[Any]) -> 'RandomizationConfig':
        """
        Create a sequence-based configuration for a field.

        Args:
            field_name: Field to configure
            sequence: Sequence of values to use

        Returns:
            Self for method chaining
        """
        config = FieldRandomizationConfig(
            mode=RandomizationMode.SEQUENCE,
            sequence=sequence
        )

        return self.configure_field(field_name, config)

    def create_custom_config(self,
                            field_name: str,
                            generator: Callable) -> 'RandomizationConfig':
        """
        Create a custom randomization configuration for a field.

        Args:
            field_name: Field to configure
            generator: Custom generator function

        Returns:
            Self for method chaining
        """
        config = FieldRandomizationConfig(
            mode=RandomizationMode.CUSTOM,
            custom_generator=generator
        )

        return self.configure_field(field_name, config)
