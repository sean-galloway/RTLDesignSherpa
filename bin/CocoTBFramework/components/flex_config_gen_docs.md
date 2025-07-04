# FlexConfigGen Documentation

## Overview

FlexConfigGen is a helper class that simplifies creating FlexRandomizer configurations by providing canned timing profiles, fluent API for configuration, and convenient shortcuts for common randomization patterns. It's designed specifically for protocol verification timing scenarios.

## Key Features

- **Canned Timing Profiles**: Pre-defined patterns like 'fast', 'bursty', 'constrained'
- **Fluent Configuration API**: Method chaining for clean, readable setup
- **Profile-Based Organization**: Group configurations by timing characteristics
- **Automatic FlexRandomizer Generation**: Direct creation of randomizers
- **Protocol-Friendly**: Designed for timing delays and protocol patterns

## Installation

```python
from CocoTBFramework.components.flex_config_gen import (
    FlexConfigGen, 
    quick_config,
    DEFAULT_PROFILES
)
```

## Basic Usage

### 1. Quick Start with Canned Profiles

```python
# Create configuration for multiple profiles and fields
config = FlexConfigGen(
    profiles=['fast', 'constrained', 'bursty'],
    fields=['psel', 'penable', 'pready']
)

# Build FlexRandomizer instances
randomizers = config.build()

# Use specific profile
fast_randomizer = randomizers['fast']
values = fast_randomizer.next()
print(values)  # {'psel': 0, 'penable': 1, 'pready': 0}
```

### 2. Using quick_config Helper

```python
# Quick creation for common use cases
config = quick_config(['backtoback', 'slow'], ['awready', 'wready'])
randomizers = config.build()

# Use back-to-back profile (always 0 delay)
backtoback = randomizers['backtoback']
print(backtoback.next())  # {'awready': 0, 'wready': 0}

# Use slow profile (moderate delays)
slow = randomizers['slow'] 
print(slow.next())  # {'awready': 7, 'wready': 12}
```

### 3. Viewing Available Profiles

```python
config = FlexConfigGen(['fast'], ['delay'])

# See all available canned profiles
profiles = config.get_available_profiles()
print(profiles)
# ['backtoback', 'fixed1', 'fixed2', 'mostly_zero', 'fast', 'constrained', 
#  'bursty', 'slow', 'stress', 'moderate', 'balanced', ...]

# Preview a profile
print(config.get_profile_preview('bursty'))
# bursty: (bins=[(0, 0), (15, 25)], weights=[10, 1])
```

## Canned Profiles Reference

### Basic Timing Profiles

```python
# Zero delay patterns
'backtoback': ([(0, 0)], [1])                    # Always 0 (back-to-back)
'mostly_zero': ([(0, 0), (1, 3)], [9, 1])       # 90% zero, 10% small delay

# Fixed delay patterns  
'fixed1': ([(1, 1)], [1])                        # Always 1 cycle
'fixed2': ([(2, 2)], [1])                        # Always 2 cycles

# Performance-oriented patterns
'fast': ([(0, 0), (1, 2)], [8, 1])              # 89% zero, 11% tiny delay
'efficient': ([(0, 0), (1, 1), (2, 3)], [6, 2, 1])  # Optimized throughput

# Balanced patterns
'constrained': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1])  # Balanced distribution
'moderate': ([(1, 3), (4, 8)], [3, 1])                   # Never zero, small-medium
'balanced': ([(0, 0), (1, 5), (6, 15)], [1, 1, 1])      # Equal probability ranges

# Stress testing patterns
'slow': ([(5, 10), (11, 20)], [3, 1])           # Moderate to slow delays
'stress': ([(0, 2), (3, 8), (9, 20), (21, 50)], [4, 3, 2, 1])  # Full range
'chaotic': ([(0, 5), (10, 15), (25, 35), (50, 80)], [3, 2, 2, 1])  # Unpredictable

# Specialized patterns
'bursty': ([(0, 0), (15, 25)], [10, 1])         # Fast bursts with pauses
'pipeline': ([(2, 4), (8, 12)], [4, 1])         # Pipeline-friendly delays
'throttled': ([(3, 7), (15, 30)], [7, 1])       # Controlled throughput
```

## Advanced Configuration

### 1. Custom Profile Modification

```python
config = FlexConfigGen(['fast', 'custom'], ['psel', 'penable'])

# Modify individual fields in a profile
config.fast.psel.clear().add_bin((0, 0), 10).add_bin((2, 5), 1)  # Custom fast pattern
config.fast.penable.fixed_value(1)                               # Always 1

# Configure another profile differently  
config.custom.psel.mostly_zero(zero_weight=15, fallback_range=(1, 8), fallback_weight=2)
config.custom.penable.burst_pattern(fast_cycles=0, pause_range=(10, 20), burst_ratio=8)

randomizers = config.build()
```

### 2. Using Configuration Methods

```python
config = FlexConfigGen(['pattern1', 'pattern2'], ['delay1', 'delay2'])

# Method 1: add_bin for precise control
config.pattern1.delay1.clear() \
    .add_bin((0, 0), 8) \
    .add_bin((1, 3), 2) \
    .add_bin((10, 15), 1)

# Method 2: mostly_zero shortcut
config.pattern1.delay2.mostly_zero(zero_weight=12, fallback_range=(2, 6))

# Method 3: burst_pattern shortcut
config.pattern2.delay1.burst_pattern(pause_range=(20, 30), burst_ratio=15)

# Method 4: weighted_ranges for multiple ranges
config.pattern2.delay2.weighted_ranges([
    ((0, 1), 5),
    ((2, 4), 3), 
    ((8, 12), 1)
])

randomizers = config.build()
```

### 3. Probability-Based Configuration

```python
config = FlexConfigGen(['prob_test'], ['ready_delay'])

# Configure using probabilities instead of weights
config.prob_test.ready_delay.probability_split([
    ((0, 0), 0.7),      # 70% zero delay
    ((1, 3), 0.2),      # 20% small delay
    ((5, 10), 0.1)      # 10% larger delay
])

randomizer = config.build()['prob_test']
```

### 4. Custom Profiles

```python
# Define custom profile patterns
custom_profiles = {
    'my_pattern': ([(1, 1), (10, 15)], [8, 1]),
    'debug_pattern': ([(5, 5)], [1])  # Fixed 5 for debugging
}

config = FlexConfigGen(
    profiles=['my_pattern', 'debug_pattern', 'fast'],
    fields=['clk_delay', 'data_delay'],
    custom_profiles=custom_profiles
)

randomizers = config.build()
```

## Field Configuration Methods

### Basic Configuration

```python
config = FlexConfigGen(['test'], ['field'])

# Fixed value
config.test.field.fixed_value(5)
# Result: 'field': ([(5, 5)], [1])

# Uniform range
config.test.field.uniform_range(1, 10) 
# Result: 'field': ([(1, 10)], [1])

# Clear and rebuild
config.test.field.clear().add_bin((0, 2), 3).add_bin((5, 8), 1)
# Result: 'field': ([(0, 2), (5, 8)], [3, 1])
```

### Pattern-Based Configuration

```python
# Mostly zero pattern
config.test.field.mostly_zero(zero_weight=20, fallback_range=(1, 4), fallback_weight=3)
# Result: 'field': ([(0, 0), (1, 4)], [20, 3])

# Burst pattern
config.test.field.burst_pattern(fast_cycles=0, pause_range=(15, 25), burst_ratio=12)
# Result: 'field': ([(0, 0), (15, 25)], [12, 1])

# Weighted ranges
config.test.field.weighted_ranges([
    ((0, 1), 4),
    ((2, 5), 2),
    ((10, 20), 1)
])
# Result: 'field': ([(0, 1), (2, 5), (10, 20)], [4, 2, 1])
```

### Configuration Copying and Chaining

```python
config = FlexConfigGen(['source', 'target'], ['field1', 'field2'])

# Configure source
config.source.field1.mostly_zero()

# Copy configuration to another field/profile
config.source.field2.copy_from(config.source.field1)
config.target.field1.copy_from(config.source.field1)

# Method chaining
config.target.field2.clear() \
    .add_bin((0, 0), 5) \
    .add_bin((1, 3), 3) \
    .add_bin((8, 15), 1)
```

## Practical Examples

### 1. APB Protocol Configuration

```python
def create_apb_config():
    """Create APB protocol timing configuration."""
    config = FlexConfigGen(
        profiles=['fast_apb', 'normal_apb', 'slow_apb'],
        fields=['psel_delay', 'penable_delay', 'pready_cycles']
    )
    
    # Fast APB - mostly back-to-back
    config.fast_apb.psel_delay.mostly_zero(zero_weight=15, fallback_range=(1, 2))
    config.fast_apb.penable_delay.fixed_value(1)  # Standard 1 cycle
    config.fast_apb.pready_cycles.mostly_zero(zero_weight=10, fallback_range=(1, 1))
    
    # Normal APB - balanced timing
    config.normal_apb.psel_delay.weighted_ranges([((0, 0), 3), ((1, 3), 2), ((5, 8), 1)])
    config.normal_apb.penable_delay.fixed_value(1)
    config.normal_apb.pready_cycles.weighted_ranges([((1, 1), 5), ((2, 3), 2), ((5, 8), 1)])
    
    # Slow APB - stress testing
    config.slow_apb.psel_delay.uniform_range(2, 10)
    config.slow_apb.penable_delay.fixed_value(1)
    config.slow_apb.pready_cycles.uniform_range(3, 15)
    
    return config.build()

# Usage
apb_randomizers = create_apb_config()
fast_apb = apb_randomizers['fast_apb']
```

### 2. AXI4 Configuration

```python
def create_axi4_config():
    """Create AXI4 protocol timing configuration."""
    config = FlexConfigGen(
        profiles=['high_perf', 'balanced', 'backpressure'],
        fields=['awready_delay', 'wready_delay', 'arready_delay', 'rvalid_delay']
    )
    
    # High performance - minimal delays
    for field in ['awready_delay', 'wready_delay', 'arready_delay']:
        config.high_perf.__getattr__(field).mostly_zero(zero_weight=12, fallback_range=(1, 2))
    config.high_perf.rvalid_delay.mostly_zero(zero_weight=8, fallback_range=(1, 3))
    
    # Balanced - realistic timing
    for field in ['awready_delay', 'wready_delay', 'arready_delay']:
        config.balanced.__getattr__(field).weighted_ranges([
            ((0, 0), 5), ((1, 3), 3), ((5, 10), 1)
        ])
    config.balanced.rvalid_delay.weighted_ranges([((1, 2), 4), ((3, 8), 2), ((10, 20), 1)])
    
    # Backpressure testing - more delays
    for field in ['awready_delay', 'wready_delay', 'arready_delay']:
        config.backpressure.__getattr__(field).burst_pattern(pause_range=(5, 15), burst_ratio=3)
    config.backpressure.rvalid_delay.uniform_range(5, 25)
    
    return config.build()

# Usage in test
axi_randomizers = create_axi4_config()
test_randomizer = axi_randomizers['balanced']

async def axi_write_test():
    delays = test_randomizer.next()
    await setup_write_transaction(
        awready_delay=delays['awready_delay'],
        wready_delay=delays['wready_delay']
    )
```

### 3. Memory Controller Configuration

```python
def create_memory_config():
    """Create memory controller timing patterns."""
    config = FlexConfigGen(
        profiles=['ddr_fast', 'ddr_normal', 'ddr_power_save'],
        fields=['cas_latency', 'ras_latency', 'refresh_delay'],
        prefix='mem_'  # Add prefix to field names
    )
    
    # Fast DDR timing
    config.ddr_fast.cas_latency.fixed_value(3)
    config.ddr_fast.ras_latency.uniform_range(12, 15)
    config.ddr_fast.refresh_delay.mostly_zero(zero_weight=20, fallback_range=(1, 3))
    
    # Normal DDR timing  
    config.ddr_normal.cas_latency.weighted_ranges([((3, 3), 2), ((4, 5), 1)])
    config.ddr_normal.ras_latency.uniform_range(15, 20)
    config.ddr_normal.refresh_delay.weighted_ranges([((0, 0), 3), ((1, 5), 2), ((8, 12), 1)])
    
    # Power save mode
    config.ddr_power_save.cas_latency.weighted_ranges([((4, 5), 3), ((6, 8), 1)])
    config.ddr_power_save.ras_latency.uniform_range(20, 30)
    config.ddr_power_save.refresh_delay.uniform_range(5, 15)
    
    return config.build()

# Usage
mem_randomizers = create_memory_config()
# Field names will be: 'mem_cas_latency', 'mem_ras_latency', 'mem_refresh_delay'
```

## Integration Patterns

### 1. Test Class Integration

```python
class ProtocolTestBase:
    def __init__(self, protocol_name):
        self.protocol_name = protocol_name
        self.config_gen = None
        self.randomizers = {}
        self.current_profile = 'balanced'
    
    def setup_timing_profiles(self, profiles, fields):
        """Setup timing configuration."""
        self.config_gen = FlexConfigGen(profiles, fields)
        self.configure_profiles()
        self.randomizers = self.config_gen.build()
    
    def configure_profiles(self):
        """Override in subclasses."""
        pass
    
    def set_timing_profile(self, profile_name):
        """Switch timing profile."""
        if profile_name in self.randomizers:
            self.current_profile = profile_name
    
    def get_timing(self):
        """Get next timing values."""
        return self.randomizers[self.current_profile].next()

class APBTest(ProtocolTestBase):
    def __init__(self):
        super().__init__("APB")
        self.setup_timing_profiles(
            profiles=['fast', 'normal', 'stress'], 
            fields=['psel_delay', 'penable_delay']
        )
    
    def configure_profiles(self):
        # Fast profile
        self.config_gen.fast.psel_delay.mostly_zero()
        self.config_gen.fast.penable_delay.fixed_value(1)
        
        # Normal profile  
        self.config_gen.normal.psel_delay.weighted_ranges([((0, 2), 3), ((3, 8), 1)])
        self.config_gen.normal.penable_delay.fixed_value(1)
        
        # Stress profile
        self.config_gen.stress.psel_delay.uniform_range(5, 20)
        self.config_gen.stress.penable_delay.fixed_value(1)
```

### 2. Configuration Validation

```python
def validate_config(config_gen):
    """Validate configuration before use."""
    try:
        # Build to check for errors
        randomizers = config_gen.build()
        
        # Test each randomizer
        for profile_name, randomizer in randomizers.items():
            values = randomizer.next()
            print(f"Profile '{profile_name}' validation passed: {values}")
            
        return True
    except Exception as e:
        print(f"Configuration validation failed: {e}")
        return False

# Usage
config = quick_config(['fast', 'slow'], ['delay1', 'delay2'])
if validate_config(config):
    randomizers = config.build()
```

## API Reference

### FlexConfigGen Class

```python
FlexConfigGen(profiles: List[str], fields: List[str], 
              prefix: str = "", custom_profiles: Optional[Dict] = None)
```

#### Core Methods
- `build(return_flexrandomizer: bool = True) -> Union[FlexRandomizer, Dict]`
- `get_available_profiles() -> List[str]`
- `get_profile_preview(profile_name: str) -> str`

#### Profile Access
- `config.{profile_name}` → Returns ProfileConfig
- `config.{profile_name}.{field_name}` → Returns FieldConfig

### FieldConfig Methods

#### Basic Configuration
- `add_bin(bin_range: Tuple[int, int], weight: float) -> FieldConfig`
- `clear() -> FieldConfig`
- `fixed_value(value: int) -> FieldConfig`
- `uniform_range(min_val: int, max_val: int) -> FieldConfig`

#### Pattern Methods
- `mostly_zero(zero_weight=9, fallback_range=(1,5), fallback_weight=1) -> FieldConfig`
- `burst_pattern(fast_cycles=0, pause_range=(15,25), burst_ratio=10) -> FieldConfig`
- `weighted_ranges(range_weights: List[Tuple]) -> FieldConfig`
- `probability_split(prob_ranges: List[Tuple]) -> FieldConfig`

#### Utility Methods
- `copy_from(other: FieldConfig) -> FieldConfig`
- `to_constraint() -> Tuple[List, List]`

### Helper Functions

```python
quick_config(profiles: List[str], fields: List[str], **kwargs) -> FlexConfigGen
```

## Best Practices

1. **Use Descriptive Profile Names**: Choose names that reflect timing characteristics
2. **Start with Canned Profiles**: Modify existing profiles rather than building from scratch
3. **Validate Configurations**: Test configurations before using in verification
4. **Group Related Fields**: Use consistent patterns across related protocol fields
5. **Document Custom Profiles**: Maintain clear documentation of custom timing patterns
6. **Use Method Chaining**: Leverage fluent API for readable configuration code

FlexConfigGen provides a powerful yet easy-to-use interface for creating sophisticated timing configurations in protocol verification environments.