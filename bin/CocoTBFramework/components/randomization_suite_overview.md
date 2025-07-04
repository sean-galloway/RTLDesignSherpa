# Randomization Suite Overview

## Architecture Overview

The randomization suite consists of three complementary classes that work together to provide flexible, powerful randomization for protocol verification:

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│  FlexConfigGen  │───▶│  FlexRandomizer  │◄───│RandomizationConfig│
│   (Helper)      │    │     (Core)       │    │   (Framework)   │
└─────────────────┘    └──────────────────┘    └─────────────────┘
     Convenience              Engine               High-Level
     Canned Profiles          Thread-Safe          Field Dependencies
     Fluent API               Multi-Strategy       Group Management
```

## When to Use Each Class

### Use FlexRandomizer When:
- You need direct control over randomization constraints
- Building custom randomization engines
- Working with thread-safe environments
- Need multiple constraint types (bins, sequences, functions)

### Use RandomizationConfig When:
- Managing complex field relationships and dependencies
- Need structured configuration with modes and groups
- Building reusable randomization frameworks
- Want high-level abstractions over randomization

### Use FlexConfigGen When:
- Working with protocol timing scenarios
- Want pre-built timing profiles (fast, bursty, constrained, etc.)
- Need quick setup with sensible defaults
- Prefer fluent configuration APIs

## Quick Start Guide

### 1. Simple Protocol Timing (FlexConfigGen)

```python
from CocoTBFramework.components.flex_config_gen import quick_config

# Quickest way to get started
config = quick_config(['fast', 'constrained'], ['psel', 'penable'])
randomizers = config.build()

# Use in your test
timing = randomizers['fast'].next()
# {'psel': 0, 'penable': 1}
```

### 2. Complex Dependencies (RandomizationConfig)

```python
from CocoTBFramework.components.randomization_config import (
    RandomizationConfig, FieldRandomizationConfig, RandomizationMode
)

config = RandomizationConfig("AXI4")

# Setup complex dependencies
config.create_constrained_config("burst_length", [(4, 4), (8, 8), (16, 16)], [0.5, 0.3, 0.2])

dependent_config = FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM,
    custom_generator=lambda vals: vals.get("burst_length", 4) * 2,
    dependencies=["burst_length"]
)
config.configure_field("total_beats", dependent_config)

values = config.generate_values(["burst_length", "total_beats"])
```

### 3. Direct Control (FlexRandomizer)

```python
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

constraints = {
    'delay': ([(0, 5), (10, 20)], [0.8, 0.2]),
    'pattern': [1, 2, 4, 8],
    'computed': lambda vals: vals.get('delay', 0) + random.randint(1, 3)
}

randomizer = FlexRandomizer(constraints)
values = randomizer.next()
```

## Integration Patterns

### 1. Layered Approach

```python
class ProtocolTest:
    def __init__(self):
        # Layer 1: FlexConfigGen for basic timing
        self.timing_config = quick_config(['fast', 'slow'], ['ready_delay'])
        self.timing_randomizers = self.timing_config.build()
        
        # Layer 2: RandomizationConfig for complex fields  
        self.field_config = RandomizationConfig("Protocol")
        self.field_config.create_constrained_config("burst_size", [(1, 8), (16, 32)], [0.7, 0.3])
        
        # Layer 3: Direct FlexRandomizer for specific needs
        self.error_randomizer = FlexRandomizer({
            'error_inject': lambda: random.choice([False] * 99 + [True])  # 1% error rate
        })
    
    def get_transaction_params(self):
        timing = self.timing_randomizers['fast'].next()
        fields = self.field_config.generate_values(['burst_size'])
        errors = self.error_randomizer.next()
        
        return {**timing, **fields, **errors}
```

### 2. Configuration Factory Pattern

```python
def create_protocol_randomization(protocol_type, performance_mode):
    """Factory for creating protocol-specific randomization."""
    
    if protocol_type == "AXI4":
        if performance_mode == "high_performance":
            config = quick_config(['fast', 'backtoback'], ['awready', 'wready', 'arready'])
            config.fast.awready.mostly_zero(zero_weight=15)
            config.fast.wready.mostly_zero(zero_weight=12)
            
        elif performance_mode == "stress_test":
            config = quick_config(['bursty', 'chaotic'], ['awready', 'wready', 'arready'])
            
        return config.build()
        
    elif protocol_type == "APB":
        # APB-specific configuration
        config = quick_config(['constrained', 'slow'], ['psel', 'penable'])
        return config.build()
```

### 3. Hybrid Configuration

```python
class HybridRandomizer:
    """Combines all three approaches for maximum flexibility."""
    
    def __init__(self):
        # FlexConfigGen for timing
        self.timing_gen = quick_config(['fast', 'normal', 'slow'], ['clk_delay'])
        self.timing_randomizers = self.timing_gen.build()
        
        # RandomizationConfig for structured fields
        self.field_config = RandomizationConfig("Hybrid")
        self.setup_field_config()
        
        # Direct FlexRandomizer for special cases
        self.special_randomizer = FlexRandomizer({
            'debug_mode': lambda: random.choice([False] * 9 + [True])
        })
        
        self.current_timing_profile = 'normal'
    
    def setup_field_config(self):
        # Group configuration
        self.field_config.add_to_group("addresses", "base_addr")
        self.field_config.add_to_group("addresses", "offset_addr")
        
        self.field_config.configure_group(
            "addresses",
            mode=RandomizationMode.CONSTRAINED,
            constraints={"bins": [(0x1000, 0x2000), (0x5000, 0x6000)], "weights": [0.8, 0.2]}
        )
    
    def randomize(self, timing_profile=None):
        if timing_profile:
            self.current_timing_profile = timing_profile
            
        timing = self.timing_randomizers[self.current_timing_profile].next()
        fields = self.field_config.generate_values(["base_addr", "offset_addr"])
        special = self.special_randomizer.next()
        
        return {**timing, **fields, **special}
```

## Common Patterns and Idioms

### 1. Profile Switching

```python
class AdaptiveTest:
    def __init__(self):
        self.config = quick_config(['fast', 'normal', 'stress'], ['delay'])
        self.randomizers = self.config.build()
        self.current_phase = 'normal'
    
    def switch_phase(self, phase):
        self.current_phase = phase
        print(f"Switched to {phase} timing profile")
    
    def get_timing(self):
        return self.randomizers[self.current_phase].next()

# Usage
test = AdaptiveTest()
test.switch_phase('fast')      # High performance phase
test.switch_phase('stress')    # Stress testing phase
```

### 2. Constrained Dependencies

```python
def setup_memory_timing():
    config = RandomizationConfig("Memory")
    
    # Base constraint
    config.create_constrained_config("frequency", [(100, 200), (300, 400)], [0.7, 0.3])
    
    # Dependent constraints
    config.create_custom_config(
        "cas_latency", 
        generator=lambda vals: 3 if vals.get("frequency", 100) <= 200 else 5
    )
    
    config.create_custom_config(
        "refresh_cycles",
        generator=lambda vals: vals.get("frequency", 100) // 10
    )
    
    return config
```

### 3. Mixed Constraint Types

```python
def create_mixed_randomizer():
    # Use FlexRandomizer directly for mixed types
    constraints = {
        # Weighted random
        'priority': ([(1, 3), (4, 7)], [0.8, 0.2]),
        
        # Sequence
        'pattern': ['A', 'B', 'C', 'A'],
        
        # Function with objects
        'command': lambda: random.choice(['READ', 'WRITE', 'MODIFY']),
        
        # Object bins
        'status': ([['OK'], ['ERROR', 'TIMEOUT']], [0.9, 0.1])
    }
    
    return FlexRandomizer(constraints)
```

## Performance Considerations

### 1. Thread Safety

```python
# All classes are thread-safe
import threading

randomizer = FlexRandomizer(constraints)  # Thread-safe
config = RandomizationConfig("Protocol")  # Not explicitly thread-safe

# For concurrent access to RandomizationConfig
import threading
lock = threading.Lock()

def safe_generate():
    with lock:
        return config.generate_values(['field1', 'field2'])
```

### 2. Memory Usage

```python
# FlexConfigGen creates multiple FlexRandomizer instances
config = quick_config(['profile1', 'profile2', 'profile3'], ['field1', 'field2'])
randomizers = config.build()  # Creates 3 FlexRandomizer instances

# For memory efficiency, build only needed profiles
needed_randomizers = {}
for profile in ['profile1']:  # Only build what you need
    profile_config = FlexConfigGen([profile], ['field1', 'field2'])
    needed_randomizers[profile] = profile_config.build()[profile]
```

### 3. Initialization Cost

```python
# Heavy initialization - do once
class TestSetup:
    _randomizers = None
    
    @classmethod
    def get_randomizers(cls):
        if cls._randomizers is None:
            config = quick_config(['fast', 'slow'], ['delay1', 'delay2'])
            cls._randomizers = config.build()
        return cls._randomizers

# Light usage - reuse randomizers
randomizers = TestSetup.get_randomizers()
```

## Debugging and Validation

### 1. Configuration Validation

```python
def validate_randomization_setup():
    try:
        # Test FlexConfigGen
        config = quick_config(['fast'], ['delay'])
        randomizers = config.build()
        values = randomizers['fast'].next()
        print(f"FlexConfigGen validation: {values}")
        
        # Test RandomizationConfig
        rc = RandomizationConfig("Test")
        rc.create_constrained_config("field", [(1, 5)], [1])
        values = rc.generate_values(["field"])
        print(f"RandomizationConfig validation: {values}")
        
        # Test FlexRandomizer
        fr = FlexRandomizer({'test': ([(1, 10)], [1])})
        values = fr.next()
        print(f"FlexRandomizer validation: {values}")
        
        return True
    except Exception as e:
        print(f"Validation failed: {e}")
        return False
```

### 2. Profile Analysis

```python
def analyze_profile(randomizer, iterations=1000):
    """Analyze the distribution of a randomizer profile."""
    results = []
    for _ in range(iterations):
        values = randomizer.next()
        results.append(values)
    
    # Analyze distribution
    for field_name in results[0].keys():
        field_values = [r[field_name] for r in results]
        print(f"{field_name}: min={min(field_values)}, max={max(field_values)}, avg={sum(field_values)/len(field_values):.2f}")

# Usage
config = quick_config(['constrained'], ['delay'])
randomizer = config.build()['constrained']
analyze_profile(randomizer)
```

## Migration Guide

### From Basic Random to FlexRandomizer

```python
# Before: Basic random
delay = random.randint(1, 10)

# After: FlexRandomizer with constraints
randomizer = FlexRandomizer({'delay': ([(1, 5), (8, 10)], [0.7, 0.3])})
delay = randomizer.next()['delay']
```

### From Hard-coded to Profile-based

```python
# Before: Hard-coded timing
if test_mode == 'fast':
    delay = 0
elif test_mode == 'slow':
    delay = random.randint(10, 20)

# After: Profile-based
config = quick_config(['fast', 'slow'], ['delay'])
randomizers = config.build()
delay = randomizers[test_mode].next()['delay']
```

This overview provides a comprehensive guide to using the randomization suite effectively in protocol verification environments. Choose the right tool for your specific needs and combine them as appropriate for maximum flexibility and maintainability.