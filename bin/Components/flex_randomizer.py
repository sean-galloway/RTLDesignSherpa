"""Flexible Constrained Value Generator"""
import random
from typing import Dict, List, Callable
from collections import deque
from cocotb_coverage.crv import Randomized


class FlexRandomizer(Randomized):
    """Randomizes delays based on specified constraints.
    
    This class allows for constrained randomization of delays, ensuring
    that generated values fall within specified ranges and distributions.
    It also supports sequence looping and function-based generation.
    """
    
    def __init__(self, constraints: Dict):
        """Initialize the FlexRandomizer with delay constraints.
        
        Args:
            constraints (dict): A dictionary defining the constraints for each delay.
                The keys are the names of the delays, and the values can be:
                - Tuple (bins, weights): For constrained random generation
                    Bins can be either:
                    - List of tuples (min, max) for integer ranges
                    - List of tuples/lists of objects for selecting from discrete objects
                - List/Tuple: For sequence looping
                - Callable: For function-based generation
        """
        super().__init__()
        self.constraints = constraints
        self.sequences = {}
        self.generators = {}
        self.object_bins = {}  # For tracking which fields use object bins rather than integer ranges
        self._rand_fields = []  # Track randomized fields
        
        # Initialize attributes for each delay
        for delay_name, constraint in self.constraints.items():
            setattr(self, delay_name, 0)
            
            # Handle different constraint types
            if isinstance(constraint, tuple) and len(constraint) == 2 and isinstance(constraint[0], list):
                # Check if this is an object bin or integer range bin
                is_object_bin = False
                if constraint[0]:  # Make sure there's at least one bin
                    first_bin = constraint[0][0]
                    # If the first bin is a tuple/list of non-numeric items, it's an object bin
                    if isinstance(first_bin, (tuple, list)) and not all(isinstance(x, (int, float)) for x in first_bin):
                        is_object_bin = True
                    # Or if the first bin is not a tuple/range at all, it's a single object
                    elif not isinstance(first_bin, (tuple, list)) and not isinstance(first_bin, (int, float)):
                        is_object_bin = True
                
                if is_object_bin:
                    # For object bins, we don't use the CRV's randomization
                    self.object_bins[delay_name] = constraint
                else:
                    # Standard constrained random with numeric ranges - (bins, weights)
                    self._add_rand_field(delay_name, self._get_full_range(constraint[0]))
            elif callable(constraint):
                # Function-based generator
                self.generators[delay_name] = constraint
            else:
                # Sequence for looping - convert to deque for efficient rotation
                self.sequences[delay_name] = deque(constraint)
    
    def _add_rand_field(self, name, rand_range):
        """Add a field to randomization and track it in our internal list.
        
        Args:
            name (str): Name of the field to randomize
            rand_range: Range of values for randomization
        """
        # Add to cocotb_coverage randomization
        self.add_rand(name, rand_range)
        
        # Track in our internal list
        if name not in self._rand_fields:
            self._rand_fields.append(name)
    
    def is_rand(self, name):
        """Check if a field is already set for randomization.
        
        Args:
            name (str): Name of the field to check.
            
        Returns:
            bool: True if the field is randomized, False otherwise.
        """
        return name in self._rand_fields
    
    def _get_full_range(self, bins):
        """Generate a full range of values from a list of bins.
        
        Args:
            bins (list): A list of bins, where each bin is a tuple specifying a range.
            
        Returns:
            list: A list containing all the values within the specified bins.
        """
        full_range = []
        for bin_range in bins:
            full_range.extend(range(bin_range[0], bin_range[1] + 1))
        return full_range
    
    def _apply_constraints(self):
        """Apply constraints to randomized values based on constraint type."""
        # Handle standard constrained random values
        for delay_name, constraint in self.constraints.items():
            if (delay_name not in self.sequences and 
                delay_name not in self.generators and 
                delay_name not in self.object_bins):
                bins, weights = constraint
                choice = random.choices(bins, weights)[0]
                value = random.randint(choice[0], choice[1])
                setattr(self, delay_name, value)
        
        # Handle object bins (non-integer ranges)
        for delay_name, constraint in self.object_bins.items():
            bins, weights = constraint
            # First randomly select a bin based on weights
            selected_bin = random.choices(bins, weights)[0]
            
            # Then randomly select an item from the chosen bin
            if isinstance(selected_bin, (list, tuple)):
                value = random.choice(selected_bin)
            else:
                # If it's not a collection, use the bin itself as the value
                value = selected_bin
                
            setattr(self, delay_name, value)
        
        # Handle sequence-based values
        for delay_name, sequence in self.sequences.items():
            if sequence:  # Check if sequence is not empty
                value = sequence[0]
                # Rotate the sequence for next time
                sequence.rotate(-1)
                setattr(self, delay_name, value)
        
        # Handle function-based generators
        current_values = {name: getattr(self, name) for name in self.constraints}
        for delay_name, generator in self.generators.items():
            try:
                # Pass current values to the generator function
                value = generator(current_values)
            except TypeError:
                # If function doesn't accept arguments, call it without args
                value = generator()
            setattr(self, delay_name, value)
    
    def next(self):
        """Generate and set values for the delays based on their constraint types.
        
        Returns:
            dict: A dictionary containing the generated values for each delay.
        """
        # Only randomize for those using constrained random with integer ranges
        if any(delay_name not in self.sequences and 
                delay_name not in self.generators and
                delay_name not in self.object_bins
                for delay_name in self.constraints):
            self.randomize()
        
        self._apply_constraints()
        return {delay_name: getattr(self, delay_name) for delay_name in self.constraints}
    
    def set_sequence(self, delay_name: str, sequence: List):
        """Set a looping sequence for a specific delay.
        
        Args:
            delay_name (str): The name of the delay to set the sequence for.
            sequence (List): The sequence of values to loop through.
        """
        if delay_name not in self.constraints:
            raise ValueError(f"Delay name '{delay_name}' not found in constraints")
        self.sequences[delay_name] = deque(sequence)
        # Remove from other types if present
        if delay_name in self.generators:
            del self.generators[delay_name]
        
        # Remove from randomized fields if present
        if delay_name in self._rand_fields:
            self._rand_fields.remove(delay_name)
    
    def set_generator(self, delay_name: str, generator: Callable):
        """Set a generator function for a specific delay.
        
        Args:
            delay_name (str): The name of the delay to set the generator for.
            generator (Callable): A function that returns the next value.
                The function can optionally accept a dictionary of current values.
        """
        if delay_name not in self.constraints:
            raise ValueError(f"Delay name '{delay_name}' not found in constraints")
        self.generators[delay_name] = generator
        # Remove from other types if present
        if delay_name in self.sequences:
            del self.sequences[delay_name]
        
        # Remove from randomized fields if present
        if delay_name in self._rand_fields:
            self._rand_fields.remove(delay_name)
    
    def reset_to_random(self, delay_name: str):
        """Reset a delay back to using constrained random values.
        
        Args:
            delay_name (str): The name of the delay to reset.
        """
        if delay_name not in self.constraints:
            raise ValueError(f"Delay name '{delay_name}' not found in constraints")
        # Remove from sequences and generators if present
        if delay_name in self.sequences:
            del self.sequences[delay_name]
        if delay_name in self.generators:
            del self.generators[delay_name]
        if delay_name in self.object_bins:
            del self.object_bins[delay_name]

        # Re-add to randomized fields if not already there
        constraint = self.constraints[delay_name]
        if isinstance(constraint, tuple) and len(constraint) == 2:
            # Check if this is an object bin
            is_object_bin = False
            if constraint[0]:  # Make sure there's at least one bin
                first_bin = constraint[0][0]
                if isinstance(first_bin, (tuple, list)) and not all(isinstance(x, (int, float)) for x in first_bin):
                    is_object_bin = True
                elif not isinstance(first_bin, (tuple, list)) and not isinstance(first_bin, (int, float)):
                    is_object_bin = True

            if is_object_bin:
                # For object bins, we don't use the CRV's randomization
                self.object_bins[delay_name] = constraint
            elif not self.is_rand(delay_name):
                # Standard constrained random with numeric ranges
                self._add_rand_field(delay_name, self._get_full_range(constraint[0]))


##############################################################################
# COMPREHENSIVE USAGE EXAMPLES
##############################################################################

def demonstrate_basic_randomization():
    """Example of basic constrained randomization."""
    print("\n=== BASIC CONSTRAINED RANDOMIZATION ===")
    
    # Define constraints with bins and weights
    constraints = {
        'clock_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),  # 70% chance of 5-10, 30% chance of 20-30
        'data_delay': ([(1, 5), (8, 12), (15, 20)], [0.5, 0.3, 0.2]),  # Multiple bins with weights
        'reset_delay': ([(0, 5)], [1.0])  # Single bin with 100% weight
    }
    
    # Create the randomizer
    flex_rand = FlexRandomizer(constraints)
    
    # Generate and show several sets of random values
    print("Generating 5 sets of random values:")
    for i in range(5):
        values = flex_rand.next()
        print(f"  Set {i+1}: {values}")
    
    return flex_rand


def demonstrate_sequence_looping(flex_rand):
    """Example of sequence looping functionality."""
    print("\n=== SEQUENCE LOOPING ===")
    
    # Convert clock_delay to use a sequence
    clock_sequence = [5, 10, 15, 20, 25]
    flex_rand.set_sequence('clock_delay', clock_sequence)
    print(f"Set clock_delay to loop through sequence: {clock_sequence}")
    
    # Generate several values to show the sequence looping
    print("Generating 8 sets of values to demonstrate looping:")
    for i in range(8):
        values = flex_rand.next()
        print(f"  Set {i+1}: {values}")
        # Highlighting the looping sequence
        print(f"    * clock_delay: {values['clock_delay']} (sequence position {i % len(clock_sequence)})")
    
    return flex_rand


def demonstrate_function_generators(flex_rand):
    """Example of function-based generators."""
    print("\n=== FUNCTION-BASED GENERATORS ===")
    
    # 1. Simple function generator that returns a constant
    print("Setting data_delay to a constant function generator (always returns 42):")
    flex_rand.set_generator('data_delay', lambda: 42)
    
    # Generate a few values
    for i in range(3):
        values = flex_rand.next()
        print(f"  Set {i+1}: {values}")
    
    # 2. Generator function that uses a counter
    print("\nSetting data_delay to a counter function generator:")
    counter = 0
    def counter_generator():
        nonlocal counter
        counter += 1
        return counter
    
    flex_rand.set_generator('data_delay', counter_generator)
    
    # Generate a few values
    for i in range(3):
        values = flex_rand.next()
        print(f"  Set {i+1}: {values}")
    
    # 3. Generator function that depends on other values
    print("\nSetting data_delay to depend on clock_delay:")
    flex_rand.set_generator('data_delay', lambda values: values['clock_delay'] * 2)
    
    # Generate a few values
    for i in range(5):
        values = flex_rand.next()
        print(f"  Set {i+1}: {values}")
        print(f"    * data_delay = clock_delay * 2: {values['data_delay']} = {values['clock_delay']} * 2")
    
    return flex_rand


def demonstrate_mixed_modes(flex_rand):
    """Example of mixing different generation modes."""
    print("\n=== MIXED GENERATION MODES ===")
    
    # Reset data_delay to random
    flex_rand.reset_to_random('data_delay')
    print("Reset data_delay back to constrained random")
    
    # Add a complex generator for reset_delay that depends on both other values
    def complex_generator(values):
        if values['clock_delay'] > 15:
            return max(1, values['data_delay'] // 2)
        else:
            return min(10, values['data_delay'] + 2)
    
    flex_rand.set_generator('reset_delay', complex_generator)
    print("Set reset_delay to a complex generator that depends on other values")
    
    # Generate several values to show the interaction
    print("Generating 5 sets with mixed generation modes:")
    for i in range(5):
        values = flex_rand.next()
        print(f"  Set {i+1}: {values}")
        print(f"    * clock_delay: {values['clock_delay']} (from sequence)")
        print(f"    * data_delay: {values['data_delay']} (constrained random)")
        print(f"    * reset_delay: {values['reset_delay']} (function generator based on other values)")
    
    return flex_rand


def demonstrate_initialization_with_different_types():
    """Example of initializing with different constraint types."""
    print("\n=== INITIALIZATION WITH DIFFERENT CONSTRAINT TYPES ===")
    
    # Define mixed constraints
    mixed_constraints = {
        'random_delay': ([(1, 10), (20, 30)], [0.8, 0.2]),  # Standard constrained random
        'sequence_delay': [5, 10, 15, 20],  # Sequence for looping
        'function_delay': lambda: random.randint(1, 100)  # Function generator
    }
    
    # Create randomizer with mixed constraints
    mixed_rand = FlexRandomizer(mixed_constraints)
    print("Created FlexRandomizer with mixed constraint types:")
    print("  * random_delay: constrained random with bins")
    print("  * sequence_delay: sequence [5, 10, 15, 20]")
    print("  * function_delay: random function returning 1-100")
    
    # Generate several values
    print("\nGenerating 5 sets of values:")
    for i in range(5):
        values = mixed_rand.next()
        print(f"  Set {i+1}: {values}")
    
    return mixed_rand


def demonstrate_error_handling():
    """Example of error handling."""
    print("\n=== ERROR HANDLING ===")
    
    # Create a simple randomizer
    constraints = {
        'delay1': ([(1, 10)], [1.0]),
        'delay2': ([(1, 10)], [1.0])
    }
    
    flex_rand = FlexRandomizer(constraints)
    
    # Try to set a sequence for a non-existent delay
    print("Attempting to set a sequence for a non-existent delay:")
    try:
        flex_rand.set_sequence('non_existent_delay', [1, 2, 3])
    except ValueError as e:
        print(f"  Caught exception: {e}")
    
    # Try to set a generator that raises an exception
    print("\nSetting a generator that might raise an exception:")
    
    def problematic_generator(values):
        if values['delay1'] > 5:
            # This will cause a ZeroDivisionError for demonstration
            return 10 // (values['delay2'] - values['delay2'])
        return values['delay1'] + values['delay2']
    
    flex_rand.set_generator('delay2', problematic_generator)
    
    print("Generating values until an exception might occur:")
    try:
        for i in range(10):
            values = flex_rand.next()
            print(f"  Set {i+1}: {values}")
    except Exception as e:
        print(f"  Caught exception: {type(e).__name__}: {e}")
    
    return flex_rand

def demonstrate_object_bins():
    """Example showing how to use object bins with the FlexRandomizer."""
    print("\n=== OBJECT BINS DEMONSTRATION ===")
    
    # Define constraints with various types of bins
    constraints = {
        # Integer range bins (the original functionality)
        'int_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),  
        
        # String bins - each bin is a tuple of strings
        'message_type': ([('GET', 'PUT', 'POST'), ('DELETE', 'PATCH'), ('OPTIONS', 'HEAD')], [0.6, 0.3, 0.1]),
        
        # Mixed type bins
        'response_code': ([
            (200, 201, 202, 204),  # Success codes (more likely)
            (301, 302, 307, 308),  # Redirection codes
            (400, 401, 403, 404),  # Client error codes
            (500, 501, 502, 503)   # Server error codes
        ], [0.6, 0.1, 0.2, 0.1]),
        
        # Complex object bins (using tuples for demonstration)
        'transaction': ([
            (('read', 4), ('read', 8), ('read', 16)),    # Read transactions of different sizes
            (('write', 4), ('write', 8), ('write', 16)), # Write transactions
            (('config', 'setup'), ('config', 'cleanup'))  # Configuration transactions
        ], [0.5, 0.4, 0.1]),
        
        # Enum-like values
        'power_state': ([
            'ACTIVE',
            'IDLE',
            'SLEEP',
            'HIBERNATE'
        ], [0.4, 0.3, 0.2, 0.1])
    }
    
    # Create the randomizer
    flex_rand = FlexRandomizer(constraints)
    
    # Generate and show several sets of random values
    print("Generating 10 sets of values with object bins:")
    for i in range(10):
        values = flex_rand.next()
        print(f"\nSet {i+1}:")
        for key, value in values.items():
            print(f"  {key}: {value}")
    
    # Demonstrate sequence for an object field
    print("\n--- Setting message_type to a sequence ---")
    flex_rand.set_sequence('message_type', ['GET', 'GET', 'POST', 'GET'])
    
    # Generate a few values with the sequence
    for i in range(5):
        values = flex_rand.next()
        print(f"\nSet {i+1}:")
        for key, value in values.items():
            if key == 'message_type':
                print(f"  {key}: {value} (from sequence)")
            else:
                print(f"  {key}: {value}")
    
    # Demonstrate function generator that works with object values
    print("\n--- Setting transaction to depend on other values ---")
    
    def transaction_generator(values):
        """Generate transaction based on other values"""
        if values['power_state'] == 'ACTIVE':
            # Only do writes in ACTIVE state
            return ('write', 16) if values['int_delay'] > 15 else ('write', 8)
        elif values['power_state'] == 'IDLE':
            # Read in IDLE state
            return ('read', 8)
        else:
            # Config in low power states
            return ('config', 'sleep_settings')
    
    flex_rand.set_generator('transaction', transaction_generator)
    
    # Generate values with the generator
    for i in range(10):
        values = flex_rand.next()
        print(f"\nSet {i+1}:")
        print(f"  power_state: {values['power_state']}")
        print(f"  int_delay: {values['int_delay']}")
        print(f"  transaction: {values['transaction']} (generated based on other values)")
    
    # Reset transaction back to random
    print("\n--- Resetting transaction back to random ---")
    flex_rand.reset_to_random('transaction')
    
    # Generate a few more sets
    for i in range(5):
        values = flex_rand.next()
        print(f"\nSet {i+1}:")
        for key, value in values.items():
            print(f"  {key}: {value}")
    
    return flex_rand



def main():  # sourcery skip: extract-duplicate-method
    """Run all the demonstration functions."""
    print("FLEXRANDOMIZER COMPREHENSIVE USAGE EXAMPLES")
    print("===========================================")
    
    # Demonstrate basic randomization
    flex_rand = demonstrate_basic_randomization()
    
    # Demonstrate sequence looping
    flex_rand = demonstrate_sequence_looping(flex_rand)
    
    # Demonstrate function generators
    flex_rand = demonstrate_function_generators(flex_rand)
    
    # Demonstrate mixed modes
    flex_rand = demonstrate_mixed_modes(flex_rand)
    
    # Demonstrate initialization with different types
    mixed_rand = demonstrate_initialization_with_different_types()
    
    # Demonstrate error handling
    error_rand = demonstrate_error_handling()
    
    print("\n=== ADVANCED USAGE PATTERN ===")
    print("Example of a typical testbench usage pattern:")
    
    # Create a randomizer for a more realistic example
    timing_constraints = {
        'clk_to_q': ([(2, 5), (6, 10)], [0.8, 0.2]),
        'setup_time': ([(1, 3)], [1.0]),
        'hold_time': ([(1, 2)], [1.0]),
        'clock_period': ([(10, 20), (30, 50)], [0.7, 0.3])
    }
    
    timing_rand = FlexRandomizer(timing_constraints)
    
    # In a typical testbench, you might want to:
    # 1. Run some tests with fully random values
    print("\nRunning 3 iterations with fully random values:")
    for i in range(3):
        timing = timing_rand.next()
        print(f"  Iteration {i+1}: {timing}")
    
    # 2. Then fix some values for specific tests
    timing_rand.set_sequence('clock_period', [20, 20, 20, 20, 20])
    print("\nFixed clock_period to 20ns for stability tests")
    
    # 3. Make some values dependent on others
    timing_rand.set_generator('hold_time', lambda values: values['setup_time'] // 2)
    print("Set hold_time to be half of setup_time")
    
    # 4. Run the specific tests
    print("\nRunning 3 iterations with partially controlled values:")
    for i in range(3):
        timing = timing_rand.next()
        print(f"  Iteration {i+1}: {timing}")
    
    # 5. Reset to fully random for coverage-driven tests
    timing_rand.reset_to_random('clock_period')
    timing_rand.reset_to_random('hold_time')
    print("\nReset to fully random for coverage testing")
    
    # 6. Run final random tests
    print("\nRunning 3 final random iterations:")
    for i in range(3):
        timing = timing_rand.next()
        print(f"  Iteration {i+1}: {timing}")

    # 7. Demonstrate object bins
    print("\nRunning Test Object Bins")
    demonstrate_object_bins()

    print("\nCompletion of all FlexRandomizer examples")


if __name__ == "__main__":
    main()
