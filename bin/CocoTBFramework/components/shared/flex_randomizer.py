# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FlexRandomizerError
# Purpose: Base exception class for FlexRandomizer errors.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

import random
import threading
import traceback
import inspect
from collections import deque
from typing import Dict, List, Tuple, Callable, Any, Union


class FlexRandomizerError(Exception):
    """Base exception class for FlexRandomizer errors."""
    pass


class ConstraintValidationError(FlexRandomizerError):
    """Raised when constraint validation fails."""
    pass


class GeneratorError(FlexRandomizerError):
    """Raised when a generator function fails."""
    pass


def _get_caller_info():
    """Get information about where FlexRandomizer was called from."""
    try:
        # Walk up the stack to find the first frame outside this file
        current_frame = inspect.currentframe()
        for frame_info in inspect.stack():
            filename = frame_info.filename
            function_name = frame_info.function
            line_number = frame_info.lineno

            # Skip frames within this file (flex_randomizer.py)
            if 'flex_randomizer.py' not in filename:
                # Get some context around the line if possible
                try:
                    with open(filename, 'r') as f:
                        lines = f.readlines()
                        if 0 <= line_number - 1 < len(lines):
                            code_line = lines[line_number - 1].strip()
                        else:
                            code_line = "<line not available>"
                except:
                    code_line = "<unable to read file>"

                return {
                    'filename': filename,
                    'function': function_name,
                    'line_number': line_number,
                    'code_line': code_line
                }
    except:
        pass

    return {
        'filename': '<unknown>',
        'function': '<unknown>',
        'line_number': 0,
        'code_line': '<unknown>'
    }


class FlexRandomizer:
    """Randomizes delays based on specified constraints with thread-safe operations.

    This class allows for constrained randomization of delays, ensuring that generated
    values fall within specified ranges and distributions. It supports multiple
    randomization strategies including constrained random, sequence looping, and
    function-based generation.

    The class is designed to be thread-safe for use in concurrent verification
    environments, with proper locking around state modifications.

    Attributes:
        constraints (Dict): The original constraint definitions
        sequences (Dict): Active sequence-based constraints
        generators (Dict): Active function-based generators
        object_bins (Dict): Object bin constraints (non-numeric discrete values)

    Example:
        Basic usage with constrained randomization:

        >>> constraints = {
        ...     'clock_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),
        ...     'data_delay': ([(1, 5), (8, 12)], [0.6, 0.4])
        ... }
        >>> randomizer = FlexRandomizer(constraints)
        >>> values = randomizer.next()
        >>> print(values)  # {'clock_delay': 7, 'data_delay': 9}

        Mixed constraint types:

        >>> mixed_constraints = {
        ...     'random_delay': ([(1, 10)], [1.0]),
        ...     'sequence_delay': [5, 10, 15, 20],
        ...     'function_delay': lambda: random.randint(1, 100)
        ... }
        >>> randomizer = FlexRandomizer(mixed_constraints)
    """

    def __init__(self, constraints: Dict[str, Union[Tuple, List, Callable]]):
        """Initialize the FlexRandomizer with delay constraints.

        Args:
            constraints: A dictionary defining the constraints for each delay field.
                Keys are field names (str), values can be:

                - Tuple (bins, weights): For constrained random generation
                    * bins: List of tuples (min, max) for integer ranges, or
                            List of tuples/lists of objects for discrete selection
                    * weights: List of relative weights (must sum to > 0)

                - List/Tuple: For sequence looping (rotates through values)

                - Callable: For function-based generation
                    * Can optionally accept dict of current values as parameter
                    * Should return a single value

        Raises:
            ConstraintValidationError: If constraints are invalid
            TypeError: If constraints parameter is not a dictionary
            ValueError: If constraint names are invalid or empty

        Example:
            >>> constraints = {
            ...     # Constrained random with 70% chance of 5-10, 30% chance of 20-30
            ...     'delay1': ([(5, 10), (20, 30)], [0.7, 0.3]),
            ...
            ...     # Object bins - choose from discrete string values
            ...     'message_type': ([('GET', 'POST'), ('DELETE',)], [0.8, 0.2]),
            ...
            ...     # Sequence that loops: 1, 2, 3, 1, 2, 3, ...
            ...     'sequence_val': [1, 2, 3],
            ...
            ...     # Function generator
            ...     'computed_val': lambda vals: vals.get('delay1', 0) * 2
            ... }
            >>> randomizer = FlexRandomizer(constraints)
        """
        # Get caller information for better error reporting
        caller_info = _get_caller_info()

        if not isinstance(constraints, dict):
            raise TypeError(
                f"Constraints must be a dictionary\n"
                f"Called from: {caller_info['filename']}:{caller_info['line_number']} in {caller_info['function']}()\n"
                f"Code: {caller_info['code_line']}"
            )

        if not constraints:
            raise ValueError(
                f"Constraints dictionary cannot be empty\n"
                f"Called from: {caller_info['filename']}:{caller_info['line_number']} in {caller_info['function']}()\n"
                f"Code: {caller_info['code_line']}"
            )

        # Validate constraint names
        for name in constraints.keys():
            if not isinstance(name, str) or not name.strip():
                raise ValueError(
                    f"Constraint names must be non-empty strings, got: {name}\n"
                    f"Called from: {caller_info['filename']}:{caller_info['line_number']} in {caller_info['function']}()\n"
                    f"Code: {caller_info['code_line']}"
                )
            if not name.replace('_', '').replace('-', '').isalnum():
                raise ValueError(
                    f"Constraint name '{name}' contains invalid characters\n"
                    f"Called from: {caller_info['filename']}:{caller_info['line_number']} in {caller_info['function']}()\n"
                    f"Code: {caller_info['code_line']}"
                )

        # Initialize thread safety
        self._lock = threading.RLock()

        # Store original constraints for reference and debugging
        self.constraints = constraints.copy()

        # Initialize state containers
        self.sequences = {}
        self.generators = {}
        self.object_bins = {}
        self._rand_fields = []  # Track fields using constrained random

        # Validate and categorize each constraint
        with self._lock:
            for delay_name, constraint in self.constraints.items():
                # Initialize the attribute
                setattr(self, delay_name, 0)

                try:
                    self._validate_and_categorize_constraint(delay_name, constraint, caller_info)
                except Exception as e:
                    raise ConstraintValidationError(
                        f"Invalid constraint for '{delay_name}': {e}\n"
                        f"Constraint value: {constraint}\n"
                        f"Constraint type: {type(constraint)}\n"
                        f"Called from: {caller_info['filename']}:{caller_info['line_number']} in {caller_info['function']}()\n"
                        f"Code: {caller_info['code_line']}"
                    ) from e

    def _validate_and_categorize_constraint(self, delay_name: str, constraint: Any, caller_info: dict) -> None:
        """Validate and categorize a single constraint.

        Args:
            delay_name: Name of the delay field
            constraint: The constraint definition to validate
            caller_info: Information about the calling context

        Raises:
            ConstraintValidationError: If the constraint is invalid
        """
        if isinstance(constraint, tuple) and len(constraint) == 2:
            # Constrained random: (bins, weights)
            bins, weights = constraint

            if not isinstance(bins, list) or not bins:
                raise ConstraintValidationError(
                    f"Bins must be a non-empty list, got {type(bins)} with value: {bins}"
                )

            if not isinstance(weights, list) or len(weights) != len(bins):
                raise ConstraintValidationError(
                    f"Weights must be a list with same length as bins. "
                    f"Got {len(weights)} weights for {len(bins)} bins. "
                    f"Weights: {weights}, Bins: {bins}"
                )

            if not all(isinstance(w, (int, float)) and w >= 0 for w in weights):
                raise ConstraintValidationError(
                    f"All weights must be non-negative numbers, got: {weights}"
                )

            if sum(weights) <= 0:
                raise ConstraintValidationError(
                    f"Sum of weights must be positive, got sum = {sum(weights)} from weights: {weights}"
                )

            # Check for common mistake: flat list of objects instead of bins of objects
            if not bins[0] or not isinstance(bins[0], (tuple, list)):
                # Check if this looks like object bins with wrong format
                if any(isinstance(item, (str, bool)) or (not isinstance(item, (int, float, tuple, list))) for item in bins):
                    example_fixed = [(item,) for item in bins]
                    raise ConstraintValidationError(
                        f"Object bins detected but using wrong format. "
                        f"Each bin must be a tuple/list of objects.\n"
                        f"You have: {bins}\n"
                        f"Should be: {example_fixed}\n"
                        f"For example: 'field': ([{bins[0]!r},), ({bins[1]!r},)], {weights}) if you want separate bins, "
                        f"or 'field': ({bins!r}], [1]) if you want all values in one bin."
                    )

            # Determine if this is object bins or integer range bins
            is_object_bin = self._is_object_bin(bins)

            if is_object_bin:
                # Validate object bins
                for i, bin_content in enumerate(bins):
                    if isinstance(bin_content, (list, tuple)):
                        if not bin_content:
                            raise ConstraintValidationError(f"Bin {i} is empty")
                    # Single objects are allowed as bins
                self.object_bins[delay_name] = constraint
            else:
                # Validate integer range bins
                for i, bin_range in enumerate(bins):
                    if not isinstance(bin_range, tuple) or len(bin_range) != 2:
                        raise ConstraintValidationError(
                            f"Bin {i} must be a tuple of (min, max), got {type(bin_range)}: {bin_range}. "
                            f"Note: Use (min, max) with parentheses, not [min, max] with brackets!"
                        )

                    min_val, max_val = bin_range
                    if not isinstance(min_val, int) or not isinstance(max_val, int):
                        raise ConstraintValidationError(
                            f"Bin {i} values must be integers, got ({type(min_val).__name__}, {type(max_val).__name__}): {bin_range}"
                        )

                    if min_val > max_val:
                        raise ConstraintValidationError(
                            f"Bin {i}: min ({min_val}) > max ({max_val})"
                        )

                # Add to constrained random fields
                self._add_rand_field(delay_name, self._get_full_range(bins))

        elif isinstance(constraint, (list, tuple)):
            # Sequence looping
            if not constraint:
                raise ConstraintValidationError("Sequence cannot be empty")

            # Convert to deque for efficient rotation
            self.sequences[delay_name] = deque(constraint)

        elif callable(constraint):
            # Function-based generator
            self.generators[delay_name] = constraint

        else:
            raise ConstraintValidationError(
                f"Constraint must be tuple (bins, weights), list/tuple for sequence, "
                f"or callable for generator. Got: {type(constraint)} with value: {constraint}"
            )

    def _is_object_bin(self, bins: List) -> bool:
        """Determine if bins contain objects rather than integer ranges.

        Args:
            bins: List of bin definitions

        Returns:
            True if bins contain objects, False if integer ranges
        """
        if not bins:
            return False

        first_bin = bins[0]

        # If first bin is a tuple/list with non-numeric items, it's an object bin
        if isinstance(first_bin, (tuple, list)):
            # Check for booleans first since bool is a subclass of int in Python
            return any(isinstance(x, bool) for x in first_bin) or not all(isinstance(x, (int, float)) for x in first_bin)

        # If first bin is not a tuple/list and not numeric, it's a single object
        # Check for bool first since bool is a subclass of int in Python
        return isinstance(first_bin, bool) or not isinstance(first_bin, (int, float, tuple, list))

    def _add_rand_field(self, name: str, rand_range: List[int]) -> None:
        """Add a field to randomization tracking.

        Args:
            name: Name of the field to randomize
            rand_range: Range of values for randomization

        Note:
            This method is kept for compatibility with the Randomized base class.
            Since we're not using coverage yet, it just tracks the field internally.
        """
        if name not in self._rand_fields:
            self._rand_fields.append(name)

    def is_rand(self, name: str) -> bool:
        """Check if a field is set for constrained randomization.

        Args:
            name: Name of the field to check

        Returns:
            True if the field uses constrained randomization, False otherwise
        """
        with self._lock:
            return name in self._rand_fields

    def _get_full_range(self, bins: List[Tuple[int, int]]) -> List[int]:
        """Generate a full range of values from a list of integer range bins.

        Args:
            bins: List of bins, where each bin is a tuple (min, max)

        Returns:
            List containing all integer values within the specified bins

        Raises:
            ConstraintValidationError: If bins are invalid
        """
        full_range = []
        for i, bin_range in enumerate(bins):
            try:
                min_val, max_val = bin_range
                full_range.extend(range(min_val, max_val + 1))
            except (ValueError, TypeError) as e:
                raise ConstraintValidationError(f"Invalid bin {i}: {e}") from e
        return full_range

    def _apply_constraints(self) -> None:
        """Apply constraints to generate values based on constraint type.

        This method is called internally by next() and handles the actual
        value generation for all constraint types.

        Raises:
            GeneratorError: If a generator function fails
        """
        # Handle standard constrained random values (integer ranges)
        for delay_name, constraint in self.constraints.items():
            if (delay_name not in self.sequences and
                delay_name not in self.generators and
                delay_name not in self.object_bins):

                try:
                    bins, weights = constraint
                    # Randomly select a bin based on weights
                    selected_bin = random.choices(bins, weights)[0]
                    # Generate random value within the selected bin
                    value = random.randint(selected_bin[0], selected_bin[1])
                    setattr(self, delay_name, value)
                except Exception as e:
                    raise GeneratorError(
                        f"Failed to generate constrained random value for '{delay_name}': {e}"
                    ) from e

        # Handle object bins (discrete non-numeric values)
        for delay_name, constraint in self.object_bins.items():
            try:
                bins, weights = constraint
                # Randomly select a bin based on weights
                selected_bin = random.choices(bins, weights)[0]

                # Select an item from the chosen bin
                if isinstance(selected_bin, (list, tuple)):
                    if not selected_bin:
                        raise GeneratorError(f"Selected bin for '{delay_name}' is empty")
                    value = random.choice(selected_bin)
                else:
                    # Single object bin
                    value = selected_bin

                setattr(self, delay_name, value)
            except Exception as e:
                raise GeneratorError(
                    f"Failed to generate object bin value for '{delay_name}': {e}"
                ) from e

        # Handle sequence-based values
        for delay_name, sequence in self.sequences.items():
            try:
                if not sequence:
                    raise GeneratorError(f"Sequence for '{delay_name}' is empty")

                value = sequence[0]
                # Rotate the sequence for next time
                sequence.rotate(-1)
                setattr(self, delay_name, value)
            except Exception as e:
                raise GeneratorError(
                    f"Failed to generate sequence value for '{delay_name}': {e}"
                ) from e

        # Handle function-based generators
        current_values = {name: getattr(self, name) for name in self.constraints}
        for delay_name, generator in self.generators.items():
            try:
                # Try to call generator with current values first
                try:
                    value = generator(current_values)
                except TypeError:
                    # If function doesn't accept arguments, call without args
                    value = generator()

                setattr(self, delay_name, value)
            except Exception as e:
                raise GeneratorError(
                    f"Generator function for '{delay_name}' failed: {e}"
                ) from e

    def next(self) -> Dict[str, Any]:
        """Generate and set values for all delays based on their constraint types.

        This method is thread-safe and generates a complete set of values
        according to the defined constraints.

        Returns:
            Dictionary containing the generated values for each delay field.
            Keys are field names, values are the generated values.

        Raises:
            GeneratorError: If any generator function fails

        Example:
            >>> randomizer = FlexRandomizer({
            ...     'delay1': ([(1, 5), (10, 15)], [0.7, 0.3]),
            ...     'delay2': [100, 200, 300]
            ... })
            >>> values = randomizer.next()
            >>> print(values)  # {'delay1': 3, 'delay2': 100}
            >>> values = randomizer.next()
            >>> print(values)  # {'delay1': 12, 'delay2': 200}
        """
        with self._lock:
            # Note: Since we're not using the Randomized base class coverage yet,
            # we skip the self.randomize() call and handle everything in _apply_constraints

            self._apply_constraints()
            return {delay_name: getattr(self, delay_name) for delay_name in self.constraints}

    def set_sequence(self, delay_name: str, sequence: List[Any]) -> None:
        """Set a looping sequence for a specific delay field.

        This method converts a field from any other constraint type to use
        a looping sequence. The sequence will rotate through values in order.

        Args:
            delay_name: The name of the delay field to modify
            sequence: The sequence of values to loop through (must be non-empty)

        Raises:
            ValueError: If delay_name is not in constraints or sequence is empty
            TypeError: If sequence is not a list or tuple

        Example:
            >>> randomizer.set_sequence('clock_delay', [10, 20, 30])
            >>> # Now clock_delay will cycle: 10, 20, 30, 10, 20, 30, ...
        """
        if delay_name not in self.constraints:
            raise ValueError(f"Delay name '{delay_name}' not found in constraints")

        if not isinstance(sequence, (list, tuple)):
            raise TypeError("Sequence must be a list or tuple")

        if not sequence:
            raise ValueError("Sequence cannot be empty")

        with self._lock:
            self.sequences[delay_name] = deque(sequence)

            # Remove from other constraint types
            if delay_name in self.generators:
                del self.generators[delay_name]
            if delay_name in self.object_bins:
                del self.object_bins[delay_name]
            if delay_name in self._rand_fields:
                self._rand_fields.remove(delay_name)

    def set_generator(self, delay_name: str, generator: Callable) -> None:
        """Set a generator function for a specific delay field.

        This method converts a field from any other constraint type to use
        a function-based generator.

        Args:
            delay_name: The name of the delay field to modify
            generator: A function that returns the next value.
                Can optionally accept a dictionary of current values as parameter.

        Raises:
            ValueError: If delay_name is not in constraints
            TypeError: If generator is not callable

        Example:
            >>> # Make data_delay always be twice the clock_delay
            >>> randomizer.set_generator('data_delay',
            ...                         lambda vals: vals['clock_delay'] * 2)
            >>>
            >>> # Use a parameterless generator
            >>> randomizer.set_generator('random_delay',
            ...                         lambda: random.randint(1, 100))
        """
        if delay_name not in self.constraints:
            raise ValueError(f"Delay name '{delay_name}' not found in constraints")

        if not callable(generator):
            raise TypeError("Generator must be callable")

        with self._lock:
            self.generators[delay_name] = generator

            # Remove from other constraint types
            if delay_name in self.sequences:
                del self.sequences[delay_name]
            if delay_name in self.object_bins:
                del self.object_bins[delay_name]
            if delay_name in self._rand_fields:
                self._rand_fields.remove(delay_name)

    def reset_to_random(self, delay_name: str) -> None:
        """Reset a delay field back to using its original constraint definition.

        This method restores a field to its original constraint type as defined
        in the constructor, removing any sequence or generator overrides.

        Args:
            delay_name: The name of the delay field to reset

        Raises:
            ValueError: If delay_name is not in constraints
            ConstraintValidationError: If the original constraint is invalid

        Example:
            >>> # Reset field back to its original constrained random behavior
            >>> randomizer.reset_to_random('clock_delay')
        """
        if delay_name not in self.constraints:
            raise ValueError(f"Delay name '{delay_name}' not found in constraints")

        with self._lock:
            # Remove from current override types
            if delay_name in self.sequences:
                del self.sequences[delay_name]
            if delay_name in self.generators:
                del self.generators[delay_name]
            if delay_name in self.object_bins:
                del self.object_bins[delay_name]
            if delay_name in self._rand_fields:
                self._rand_fields.remove(delay_name)

            # Re-categorize based on original constraint
            constraint = self.constraints[delay_name]
            try:
                caller_info = _get_caller_info()
                self._validate_and_categorize_constraint(delay_name, constraint, caller_info)
            except Exception as e:
                raise ConstraintValidationError(
                    f"Failed to reset '{delay_name}' to original constraint: {e}"
                ) from e

    def get_constraint_type(self, delay_name: str) -> str:
        """Get the current constraint type for a delay field.

        Args:
            delay_name: Name of the delay field

        Returns:
            String describing the constraint type: 'sequence', 'generator',
            'object_bin', 'constrained_random', or 'unknown'

        Raises:
            ValueError: If delay_name is not in constraints
        """
        if delay_name not in self.constraints:
            raise ValueError(f"Delay name '{delay_name}' not found in constraints")

        with self._lock:
            if delay_name in self.sequences:
                return 'sequence'
            elif delay_name in self.generators:
                return 'generator'
            elif delay_name in self.object_bins:
                return 'object_bin'
            elif delay_name in self._rand_fields:
                return 'constrained_random'
            else:
                return 'unknown'

    def get_field_names(self) -> List[str]:
        """Get a list of all delay field names.

        Returns:
            List of field names defined in constraints
        """
        return list(self.constraints.keys())

    def __str__(self) -> str:
        """Return a human-readable string representation of the randomizer state.

        Returns:
            String showing current constraint types and values for each field
        """
        with self._lock:
            lines = [f"FlexRandomizer with {len(self.constraints)} fields:"]

            for name in sorted(self.constraints.keys()):
                constraint_type = self.get_constraint_type(name)
                current_value = getattr(self, name, 'unset')

                # Add type-specific details
                details = ""
                if constraint_type == 'sequence':
                    seq_list = list(self.sequences[name])
                    details = f" (sequence: {seq_list})"
                elif constraint_type == 'generator':
                    details = f" (generator: {self.generators[name].__name__})"
                elif constraint_type == 'object_bin':
                    bins, weights = self.object_bins[name]
                    details = f" (object_bins: {len(bins)} bins)"
                elif constraint_type == 'constrained_random':
                    constraint = self.constraints[name]
                    if isinstance(constraint, tuple):
                        bins, weights = constraint
                        details = f" (random: {len(bins)} bins)"

                lines.append(f"  {name}: {current_value} [{constraint_type}]{details}")

            return "\n".join(lines)

    def __repr__(self) -> str:
        """Return a detailed string representation suitable for debugging.

        Returns:
            String showing the complete internal state
        """
        with self._lock:
            return (f"FlexRandomizer(constraints={self.constraints}, "
                    f"sequences={dict(self.sequences)}, "
                    f"generators={list(self.generators.keys())}, "
                    f"object_bins={list(self.object_bins.keys())}, "
                    f"rand_fields={self._rand_fields})")
