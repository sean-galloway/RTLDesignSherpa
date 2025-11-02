# flex_config_gen.py

Helper class for creating FlexRandomizer configurations with weighted bins. This module simplifies the creation of FlexRandomizer constraint dictionaries by providing a clean API for building weighted bin configurations and common shortcuts.

## Overview

The `flex_config_gen.py` module provides an intuitive way to build complex randomization configurations for FlexRandomizer. It includes pre-defined timing patterns and a fluent API for creating custom configurations.

## Pre-defined Profiles

### DEFAULT_PROFILES

A collection of commonly used timing patterns:

```python
DEFAULT_PROFILES = {
    # Always zero delay - for back-to-back transactions
    'backtoback': ([(0, 0)], [1]),

    # Fixed delays
    'fixed1': ([(1, 1)], [1]),                           # Always 1 cycle delay
    'fixed2': ([(2, 2)], [1]),                           # Always 2 cycle delay

    # Mostly zero with occasional small delays
    'mostly_zero': ([(0, 0), (1, 3)], [9, 1]),         # 90% zero, 10% small delay

    # Fast pattern - mostly zero, some small delays
    'fast': ([(0, 0), (1, 2)], [8, 1]),                # 89% zero, 11% tiny delay

    # Standard constrained pattern from project examples
    'constrained': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1]), # Balanced distribution

    # Burst pattern - mostly zero with occasional long pauses
    'bursty': ([(0, 0), (15, 25)], [10, 1]),           # Fast bursts with pauses

    # Always has some delay
    'slow': ([(5, 10), (11, 20)], [3, 1]),             # Moderate to slow delays

    # Wide variation for stress testing
    'stress': ([(0, 2), (3, 8), (9, 20), (21, 50)], [4, 3, 2, 1]), # Full range stress

    # Additional meaningful profiles
    'moderate': ([(1, 3), (4, 8)], [3, 1]),                             # Never zero, small-medium delays
    'balanced': ([(0, 0), (1, 5), (6, 15)], [1, 1, 1]),                 # Equal probability ranges
    'heavy_pause': ([(0, 0), (20, 40)], [3, 1]),                        # Mostly fast with heavy pauses
    'gradual': ([(1, 2), (3, 5), (6, 10), (11, 20)], [8, 4, 2, 1]),     # Exponential falloff
    'jittery': ([(0, 1), (2, 4), (5, 8)], [2, 3, 2]),                   # Small random variations
    'pipeline': ([(2, 4), (8, 12)], [4, 1]),                            # Pipeline-friendly delays
    'throttled': ([(3, 7), (15, 30)], [7, 1]),                          # Controlled throughput
    'chaotic': ([(0, 5), (10, 15), (25, 35), (50, 80)], [3, 2, 2, 1]),  # Unpredictable timing
    'smooth': ([(2, 6), (7, 12)], [2, 1]),                              # Consistent moderate delays
    'efficient': ([(0, 0), (1, 1), (2, 3)], [6, 2, 1])                  # Optimized for throughput
}
```

## Classes

### FieldConfig

Configuration for a single field within a profile.

#### Constructor

```python
FieldConfig(field_name: str, profile_name: str)
```

**Parameters:**
- `field_name`: The field name
- `profile_name`: The profile name this field belongs to

#### Methods

##### `add_bin(bin_range: Tuple[int, int], weight: Union[int, float]) -> 'FieldConfig'`
Add a weighted bin to this field.

**Parameters:**
- `bin_range`: Tuple of (min, max) values for the bin
- `weight`: Weight for this bin (relative to other bins)

**Returns:** Self for method chaining

```python
config.fast.psel.add_bin((0, 0), 8).add_bin((1, 5), 1)
# Results in: 'psel': ([(0, 0), (1, 5)], [8, 1])
```

##### `clear() -> 'FieldConfig'`
Clear all bins for this field.

```python
config.fast.psel.clear()
```

##### `fixed_value(value: int) -> 'FieldConfig'`
Set field to always return a fixed value.

```python
config.fast.psel.fixed_value(0)
# Results in: 'psel': ([(0, 0)], [1])
```

##### `mostly_zero(zero_weight: Union[int, float] = 9, fallback_range: Tuple[int, int] = (1, 5), fallback_weight: Union[int, float] = 1) -> 'FieldConfig'`
Create a pattern that's mostly zero with occasional other values.

```python
config.fast.psel.mostly_zero(zero_weight=15, fallback_range=(1, 8), fallback_weight=2)
# Results in: 'psel': ([(0, 0), (1, 8)], [15, 2])
```

##### `burst_pattern(fast_cycles: int = 0, pause_range: Tuple[int, int] = (15, 25), burst_ratio: Union[int, float] = 10) -> 'FieldConfig'`
Create a burst pattern - mostly fast cycles with occasional pauses.

```python
config.bursty.psel.burst_pattern(fast_cycles=0, pause_range=(20, 30), burst_ratio=12)
# Results in: 'psel': ([(0, 0), (20, 30)], [12, 1])
```

##### `uniform_range(min_val: int, max_val: int) -> 'FieldConfig'`
Create a uniform distribution across a range.

```python
config.slow.psel.uniform_range(5, 15)
# Results in: 'psel': ([(5, 15)], [1])
```

##### `weighted_ranges(range_weights: List[Tuple[Tuple[int, int], Union[int, float]]]) -> 'FieldConfig'`
Set multiple weighted ranges at once.

```python
config.constrained.psel.weighted_ranges([
    ((0, 0), 5),
    ((1, 3), 3),
    ((10, 20), 1)
])
# Results in: 'psel': ([(0, 0), (1, 3), (10, 20)], [5, 3, 1])
```

##### `copy_from(other: 'FieldConfig') -> 'FieldConfig'`
Copy configuration from another field.

```python
config.profile2.field2.copy_from(config.profile1.field1)
```

##### `probability_split(prob_ranges: List[Tuple[Tuple[int, int], float]]) -> 'FieldConfig'`
Set ranges based on probabilities (automatically converts to weights).

```python
config.fast.psel.probability_split([
    ((0, 0), 0.8),      # 80% chance
    ((1, 5), 0.2)       # 20% chance
])
# Results in: 'psel': ([(0, 0), (1, 5)], [8, 2]) (scaled to integers)
```

##### `to_constraint() -> Tuple[List[Tuple[int, int]], List[Union[int, float]]]`
Convert to the tuple format expected by FlexRandomizer.

### ProfileConfig

Configuration for all fields within a profile.

#### Constructor

```python
ProfileConfig(profile_name: str, field_names: List[str], prefix: str = "")
```

**Parameters:**
- `profile_name`: Name of the profile
- `field_names`: List of field names (e.g., ['psel', 'penable'])
- `prefix`: Optional prefix for field names

#### Attribute Access

Fields can be accessed as attributes:

```python
profile.psel.add_bin((0, 0), 8)
profile.penable.mostly_zero()
```

### FlexConfigGen

Main helper class for generating FlexRandomizer configurations with weighted bins.

#### Constructor

```python
FlexConfigGen(profiles: List[str], fields: List[str], prefix: str = "", custom_profiles: Optional[Dict[str, Tuple]] = None)
```

**Parameters:**
- `profiles`: List of profile names to create
- `fields`: List of field names (e.g., ['psel', 'penable'])
- `prefix`: Optional prefix for field names
- `custom_profiles`: Optional dict of custom profile definitions

```python
config = FlexConfigGen(
    profiles=['backtoback', 'constrained', 'fast'],
    fields=['psel', 'penable'],
    custom_profiles={'my_pattern': ([(1, 1), (10, 15)], [8, 1])}
)
```

#### Methods

##### `build(return_flexrandomizer: bool = True) -> Union[FlexRandomizer, Dict]`
Build the final configuration.

**Parameters:**
- `return_flexrandomizer`: If True, return FlexRandomizer instance; if False, return constraint dictionary

**Returns:** FlexRandomizer instance or constraint dictionary

```python
# Get FlexRandomizer directly (default)
randomizer = config.build()

# Get dictionary for manual use
constraint_dict = config.build(return_flexrandomizer=False)
```

##### `get_available_profiles() -> List[str]`
Get list of available canned profiles.

```python
profiles = config.get_available_profiles()
print(f"Available profiles: {profiles}")
```

##### `get_profile_preview(profile_name: str) -> str`
Get a preview of what a canned profile looks like.

```python
preview = config.get_profile_preview('fast')
print(preview)  # "fast: (bins=[(0, 0), (1, 2)], weights=[8, 1])"
```

#### Profile Access

Profiles can be accessed as attributes:

```python
config.fast.psel.mostly_zero(zero_weight=10)
config.constrained.penable.weighted_ranges([((0, 0), 3), ((1, 5), 1)])
```

## Convenience Functions

### `quick_config(profiles: List[str], fields: List[str], **kwargs) -> FlexConfigGen`

Quick way to create a FlexConfigGen with common defaults.

```python
config = quick_config(['fast', 'constrained'], ['psel', 'penable'])
randomizer = config.build()['fast']  # Get the 'fast' profile randomizer
```

## Usage Patterns

### Basic Configuration

```python
# Create configuration generator
config = FlexConfigGen(
    profiles=['fast', 'constrained', 'bursty'],
    fields=['psel', 'penable']
)

# Customize the 'fast' profile
config.fast.psel.mostly_zero(zero_weight=15, fallback_range=(1, 3))
config.fast.penable.fixed_value(1)  # Always enabled

# Customize the 'constrained' profile  
config.constrained.psel.weighted_ranges([
    ((0, 0), 5),      # 50% zero delay
    ((1, 8), 3),      # 30% small delay
    ((9, 20), 2)      # 20% medium delay
])
config.constrained.penable.probability_split([
    ((0, 0), 0.1),    # 10% disabled
    ((1, 1), 0.9)     # 90% enabled
])

# Build randomizers
randomizers = config.build()

# Use specific profile
fast_randomizer = randomizers['fast']
values = fast_randomizer.next()
print(f"Fast pattern: psel={values['psel']}, penable={values['penable']}")
```

### Custom Profiles

```python
# Define custom timing patterns
custom_profiles = {
    'ultra_fast': ([(0, 0)], [1]),                    # Always zero
    'mixed_burst': ([(0, 0), (5, 10), (20, 30)], [6, 3, 1]),  # Burst pattern
    'test_specific': ([(2, 4), (8, 12)], [1, 1])     # Test-specific timing
}

config = FlexConfigGen(
    profiles=['ultra_fast', 'mixed_burst', 'test_specific'],
    fields=['ready_delay', 'valid_delay'],
    custom_profiles=custom_profiles
)

# Further customize
config.ultra_fast.ready_delay.fixed_value(0)
config.ultra_fast.valid_delay.fixed_value(0)

config.mixed_burst.ready_delay.burst_pattern(pause_range=(25, 35))
config.mixed_burst.valid_delay.mostly_zero(zero_weight=8)
```

### Integration with Protocol Components

```python
class ProtocolMaster:
    def __init__(self, dut, field_names):
        # Create timing configuration
        self.timing_config = FlexConfigGen(
            profiles=['fast', 'normal', 'slow', 'stress'],
            fields=field_names
        )
        
        # Customize profiles for this protocol
        self._setup_timing_profiles()
        
        # Build randomizers
        self.randomizers = self.timing_config.build()
        
        # Start with fast profile
        self.current_randomizer = self.randomizers['fast']
    
    def _setup_timing_profiles(self):
        # Fast profile - mostly back-to-back
        self.timing_config.fast.setup_delay.mostly_zero(zero_weight=9)
        self.timing_config.fast.hold_delay.fixed_value(0)
        
        # Normal profile - moderate delays
        self.timing_config.normal.setup_delay.weighted_ranges([
            ((0, 0), 3), ((1, 3), 2), ((4, 8), 1)
        ])
        self.timing_config.normal.hold_delay.uniform_range(1, 5)
        
        # Slow profile - always has delays
        self.timing_config.slow.setup_delay.uniform_range(5, 15)
        self.timing_config.slow.hold_delay.uniform_range(3, 10)
        
        # Stress profile - chaotic timing
        self.timing_config.stress.setup_delay.weighted_ranges([
            ((0, 2), 2), ((3, 10), 2), ((11, 30), 1), ((31, 100), 1)
        ])
        self.timing_config.stress.hold_delay.weighted_ranges([
            ((0, 5), 3), ((6, 20), 2), ((21, 50), 1)
        ])
    
    def set_timing_profile(self, profile_name):
        """Switch to a different timing profile"""
        if profile_name in self.randomizers:
            self.current_randomizer = self.randomizers[profile_name]
            self.log.info(f"Switched to {profile_name} timing profile")
        else:
            self.log.error(f"Unknown profile: {profile_name}")
    
    def get_next_delays(self):
        """Get next set of delay values"""
        return self.current_randomizer.next()
```

### Advanced Configuration Patterns

```python
# Configuration with field dependencies
config = FlexConfigGen(
    profiles=['dependent_timing'],
    fields=['master_delay', 'slave_delay']
)

# Master delay uses standard pattern
config.dependent_timing.master_delay.weighted_ranges([
    ((0, 0), 5), ((1, 5), 3), ((6, 15), 2)
])

# Slave delay depends on master delay (configured later in randomizer)
config.dependent_timing.slave_delay.uniform_range(0, 10)

# Build base configuration
constraint_dict = config.build(return_flexrandomizer=False)

# Add dependency manually to FlexRandomizer
def slave_delay_generator(current_values):
    master_delay = current_values.get('master_delay', 0)
    # Slave delay is always less than or equal to master delay
    return min(master_delay, random.randint(0, master_delay + 2))

# Create FlexRandomizer with custom generator
final_randomizer = FlexRandomizer(constraint_dict['dependent_timing'])
final_randomizer.set_generator('slave_delay', slave_delay_generator)
```

### Profile Comparison and Analysis

```python
def analyze_profile_characteristics(config, profile_name, num_samples=1000):
    """Analyze the characteristics of a timing profile"""
    randomizer = config.build()[profile_name]
    
    samples = []
    for _ in range(num_samples):
        values = randomizer.next()
        samples.append(values)
    
    # Calculate statistics
    stats = {}
    for field_name in randomizer.get_field_names():
        field_values = [sample[field_name] for sample in samples]
        stats[field_name] = {
            'min': min(field_values),
            'max': max(field_values),
            'avg': sum(field_values) / len(field_values),
            'zero_percent': (field_values.count(0) / len(field_values)) * 100
        }
    
    return stats

# Usage
config = quick_config(['fast', 'constrained', 'stress'], ['delay1', 'delay2'])
for profile in ['fast', 'constrained', 'stress']:
    stats = analyze_profile_characteristics(config, profile)
    print(f"\n{profile.upper()} Profile Statistics:")
    for field, field_stats in stats.items():
        print(f"  {field}: avg={field_stats['avg']:.1f}, "
              f"range=[{field_stats['min']}-{field_stats['max']}], "
              f"zero={field_stats['zero_percent']:.1f}%")
```

## Best Practices

### 1. **Start with Canned Profiles**
Use pre-defined profiles as starting points and customize as needed:

```python
config = quick_config(['fast', 'constrained'], ['delay'])
# Customize from there
config.fast.delay.mostly_zero(zero_weight=12)
```

### 2. **Use Meaningful Profile Names**
Create profiles that describe their intended use:

```python
custom_profiles = {
    'setup_phase': ([(10, 20)], [1]),        # Slow for setup
    'data_transfer': ([(0, 0), (1, 2)], [9, 1]),  # Fast for data
    'cleanup_phase': ([(5, 15)], [1])        # Medium for cleanup
}
```

### 3. **Validate Profile Behavior**
Test profiles to ensure they behave as expected:

```python
def validate_profile(randomizer, field_name, expected_zero_percent):
    samples = [randomizer.next()[field_name] for _ in range(1000)]
    zero_percent = (samples.count(0) / len(samples)) * 100
    assert abs(zero_percent - expected_zero_percent) < 5, \
        f"Expected ~{expected_zero_percent}% zeros, got {zero_percent:.1f}%"
```

### 4. **Use Method Chaining**
Take advantage of fluent interface for cleaner code:

```python
(config.fast.delay
    .clear()
    .mostly_zero(zero_weight=15)
    .add_bin((10, 20), 1))  # Add occasional long delay
```

### 5. **Document Profile Intent**
Comment your profile configurations:

```python
# Fast profile: optimized for maximum throughput testing
config.fast.delay.mostly_zero(zero_weight=20)  # 95% zero delay

# Stress profile: designed to find timing-related bugs  
config.stress.delay.weighted_ranges([
    ((0, 0), 1),      # Occasional zero delay
    ((1, 50), 2),     # Most delays in medium range
    ((51, 200), 1)    # Some very long delays
])
```

The FlexConfigGen provides a powerful and intuitive way to create complex randomization patterns while maintaining readability and flexibility for verification environments.
