# RandomizationConfig Documentation

## Overview

RandomizationConfig provides a high-level, flexible framework for configuring randomization behavior in protocol verification environments. It uses FlexRandomizer as the underlying engine while adding features like dependency management, field grouping, and structured configuration modes.

## Key Features

- **Multiple Randomization Modes**: DETERMINISTIC, CONSTRAINED, SEQUENCE, CUSTOM
- **Field Dependencies**: Handle inter-field relationships
- **Group Configuration**: Configure multiple fields simultaneously
- **Seed Management**: Reproducible randomization
- **Method Chaining**: Fluent API for configuration

## Installation

```python
from CocoTBFramework.components.randomization_config import (
    RandomizationConfig, 
    FieldRandomizationConfig, 
    RandomizationMode
)
```

## Basic Usage

### 1. Simple Field Configuration

```python
# Create config for a protocol
config = RandomizationConfig(protocol_name="AXI4")

# Configure individual fields
from dataclasses import dataclass

# Method 1: Using FieldRandomizationConfig
delay_config = FieldRandomizationConfig(
    enabled=True,
    mode=RandomizationMode.CONSTRAINED,
    constraints={"bins": [(0, 5), (10, 20)], "weights": [0.8, 0.2]}
)

config.configure_field("awready_delay", delay_config)

# Method 2: Using convenience methods
config.create_constrained_config(
    "arready_delay", 
    bins=[(1, 3), (5, 10)], 
    weights=[0.7, 0.3]
)

# Generate values
values = config.generate_values(["awready_delay", "arready_delay"])
print(values)  # {'awready_delay': 2, 'arready_delay': 5}
```

### 2. Sequence-Based Configuration

```python
config = RandomizationConfig("APB")

# Configure field to cycle through values
config.create_sequence_config("pready_cycles", [1, 1, 2, 3, 1])

# Generate sequence values
for i in range(7):
    value = config.generate_value("pready_cycles")
    print(f"Cycle {i}: {value}")
# Output: 1, 1, 2, 3, 1, 1, 1 (cycles back to start)
```

### 3. Custom Generator Functions

```python
config = RandomizationConfig("Memory")

# Simple custom generator
config.create_custom_config(
    "burst_size",
    generator=lambda vals: random.choice([4, 8, 16])
)

# Dependent custom generator
config.create_custom_config(
    "latency",
    generator=lambda vals: vals.get("burst_size", 4) // 2 + random.randint(1, 3)
)

values = config.generate_values(["burst_size", "latency"])
print(values)  # {'burst_size': 8, 'latency': 7}
```

## Advanced Features

### 1. Field Dependencies

```python
config = RandomizationConfig("PCIe")

# Configure base field
config.create_constrained_config(
    "payload_size",
    bins=[(64, 128), (256, 512)],
    weights=[0.6, 0.4]
)

# Configure dependent field
dependent_config = FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM,
    custom_generator=lambda vals: (vals.get("payload_size", 64) // 32) + 1,
    dependencies=["payload_size"]  # Depends on payload_size
)

config.configure_field("dword_count", dependent_config)

# Dependencies are automatically resolved
values = config.generate_values(["payload_size", "dword_count"])
print(values)  # {'payload_size': 128, 'dword_count': 5}
```

### 2. Field Grouping

```python
config = RandomizationConfig("Ethernet")

# Add fields to groups
config.add_to_group("timing", "tx_delay")
config.add_to_group("timing", "rx_delay")
config.add_to_group("timing", "inter_frame_gap")

config.add_to_group("control", "flow_control")
config.add_to_group("control", "error_injection")

# Configure entire groups
config.configure_group(
    "timing",
    mode=RandomizationMode.CONSTRAINED,
    constraints={"bins": [(1, 5), (8, 15)], "weights": [0.8, 0.2]}
)

config.configure_group(
    "control", 
    mode=RandomizationMode.SEQUENCE,
    sequence=[True, False, False, False]  # 25% control events
)

# Generate values for all fields
all_fields = ["tx_delay", "rx_delay", "inter_frame_gap", "flow_control", "error_injection"]
values = config.generate_values(all_fields)
```

### 3. Multiple Randomization Modes

```python
config = RandomizationConfig("Mixed_Protocol")

# Deterministic values
deterministic_config = FieldRandomizationConfig(
    mode=RandomizationMode.DETERMINISTIC,
    sequence=[100]  # Always returns 100
)
config.configure_field("fixed_delay", deterministic_config)

# Constrained random
config.create_constrained_config(
    "variable_delay",
    bins=[(1, 10), (20, 50)],
    weights=[0.9, 0.1]
)

# Sequence mode
config.create_sequence_config("pattern", ["A", "B", "C", "A"])

# Custom generator
config.create_custom_config(
    "computed",
    generator=lambda vals: vals.get("variable_delay", 0) * 2
)

values = config.generate_values(["fixed_delay", "variable_delay", "pattern", "computed"])
print(values)  # {'fixed_delay': 100, 'variable_delay': 7, 'pattern': 'A', 'computed': 14}
```

## Configuration Patterns

### 1. Protocol-Specific Configurations

```python
def create_axi4_config():
    """Create AXI4-specific randomization configuration."""
    config = RandomizationConfig("AXI4")
    
    # Address channel delays
    config.create_constrained_config("awready_delay", [(0, 0), (1, 3)], [0.8, 0.2])
    config.create_constrained_config("arready_delay", [(0, 0), (1, 3)], [0.8, 0.2])
    
    # Data channel patterns
    config.create_sequence_config("wready_pattern", [1, 1, 0, 1])  # Occasional backpressure
    
    # Response delays with dependency
    response_gen = lambda vals: max(1, vals.get("awready_delay", 1) + random.randint(0, 2))
    config.create_custom_config("bresp_delay", response_gen)
    
    return config

def create_apb_config():
    """Create APB-specific randomization configuration.""" 
    config = RandomizationConfig("APB")
    
    # Simple ready patterns
    config.create_sequence_config("pready_cycles", [1, 1, 1, 2])
    
    # Occasional errors
    config.create_constrained_config("error_rate", [(0, 0), (1, 1)], [0.95, 0.05])
    
    return config
```

### 2. Test Phase Configuration

```python
def configure_for_test_phase(config, phase):
    """Reconfigure randomization based on test phase."""
    if phase == "directed":
        # Use deterministic values for directed tests
        config.configure_group("all_fields", mode=RandomizationMode.DETERMINISTIC)
        
    elif phase == "constrained_random":
        # Use constrained random for coverage
        config.configure_group("all_fields", mode=RandomizationMode.CONSTRAINED)
        
    elif phase == "stress":
        # Use aggressive patterns for stress testing
        stress_constraints = {"bins": [(0, 1), (10, 50)], "weights": [0.3, 0.7]}
        config.configure_group("all_fields", constraints=stress_constraints)
        
    return config
```

### 3. Dependency Chains

```python
config = RandomizationConfig("Complex_Protocol")

# Create dependency chain: base -> derived1 -> derived2
config.create_constrained_config("base_freq", [(100, 200), (300, 400)], [0.7, 0.3])

derived1_config = FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM,
    custom_generator=lambda vals: vals.get("base_freq", 100) // 2,
    dependencies=["base_freq"]
)
config.configure_field("clock_div", derived1_config)

derived2_config = FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM, 
    custom_generator=lambda vals: vals.get("clock_div", 50) + random.randint(1, 5),
    dependencies=["clock_div"]
)
config.configure_field("sample_rate", derived2_config)

# Dependencies automatically resolved in correct order
values = config.generate_values(["base_freq", "clock_div", "sample_rate"])
```

## Seed Management and Reproducibility

```python
# Set seed for reproducible results
config = RandomizationConfig("Test_Protocol", seed=12345)

# Generate same sequence each time
config.create_constrained_config("delay", [(1, 10)], [1])

# First run
config.set_seed(42)
values1 = [config.generate_value("delay") for _ in range(5)]

# Second run with same seed
config.set_seed(42) 
values2 = [config.generate_value("delay") for _ in range(5)]

assert values1 == values2  # Same sequence
```

## Dynamic Reconfiguration

```python
config = RandomizationConfig("Dynamic_Protocol")

# Start with constrained random
config.create_constrained_config("delay", [(1, 5), (10, 20)], [0.8, 0.2])

# Switch to sequence mode mid-test
config.create_sequence_config("delay", [2, 4, 6, 8])

# Switch to custom generator
config.create_custom_config("delay", lambda vals: random.choice([1, 5, 10]))

# Reset sequences
config.reset_sequences()

# Enable/disable randomization
config.disable()  # Returns default values
config.enable()   # Resume randomization
```

## Configuration Validation and Debugging

```python
config = RandomizationConfig("Debug_Protocol")

# Configure fields
config.create_constrained_config("field1", [(1, 5)], [1])
config.create_sequence_config("field2", [10, 20, 30])

# Get configuration details
field_config = config.get_field_config("field1")
print(f"Mode: {field_config.mode}")
print(f"Enabled: {field_config.enabled}")
print(f"Constraints: {field_config.constraints}")

# Check dependencies
dependent_config = FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM,
    custom_generator=lambda vals: vals.get("field1", 0) * 2,
    dependencies=["field1"]
)
config.configure_field("field3", dependent_config)

# Verify dependency resolution
values = config.generate_values(["field1", "field2", "field3"])
assert values["field3"] == values["field1"] * 2
```

## Error Handling

```python
try:
    config = RandomizationConfig("Test")
    
    # Invalid dependency
    bad_config = FieldRandomizationConfig(
        mode=RandomizationMode.CUSTOM,
        custom_generator=lambda vals: vals["nonexistent_field"],
        dependencies=["nonexistent_field"]
    )
    config.configure_field("bad_field", bad_config)
    
    # This will handle the missing dependency gracefully
    value = config.generate_value("bad_field")  # Returns default (0)
    
except Exception as e:
    print(f"Configuration error: {e}")
```

## Integration with Test Environment

```python
class ProtocolTestBase:
    def __init__(self, config_name="generic"):
        self.rand_config = RandomizationConfig(config_name)
        self.setup_randomization()
    
    def setup_randomization(self):
        """Override in derived classes."""
        pass
    
    def randomize_transaction(self, field_names):
        """Generate randomized transaction."""
        return self.rand_config.generate_values(field_names)

class AXI4Test(ProtocolTestBase):
    def setup_randomization(self):
        # Configure AXI4-specific randomization
        self.rand_config.create_constrained_config(
            "awready_delay", [(0, 2), (5, 10)], [0.9, 0.1]
        )
        self.rand_config.create_sequence_config(
            "wready_pattern", [1, 1, 0, 1, 1]
        )
    
    async def write_transaction(self):
        # Generate randomized delays
        delays = self.randomize_transaction(["awready_delay", "wready_pattern"])
        
        # Use in transaction
        await self.write_addr_phase(ready_delay=delays["awready_delay"])
        await self.write_data_phase(ready_pattern=delays["wready_pattern"])
```

## API Reference

### RandomizationConfig Class

```python
RandomizationConfig(protocol_name: str = "generic", seed: Optional[int] = None)
```

#### Configuration Methods
- `configure_field(field_name, config) -> RandomizationConfig`
- `add_to_group(group_name, field_name) -> RandomizationConfig`  
- `configure_group(group_name, **kwargs) -> RandomizationConfig`
- `get_field_config(field_name) -> FieldRandomizationConfig`

#### Convenience Methods
- `create_constrained_config(field_name, bins, weights) -> RandomizationConfig`
- `create_sequence_config(field_name, sequence) -> RandomizationConfig`
- `create_custom_config(field_name, generator) -> RandomizationConfig`

#### Generation Methods
- `generate_value(field_name) -> Any`
- `generate_values(field_names) -> Dict[str, Any]`

#### Control Methods
- `enable() -> RandomizationConfig`
- `disable() -> RandomizationConfig`
- `set_seed(seed) -> RandomizationConfig`
- `reset_sequences() -> RandomizationConfig`

### FieldRandomizationConfig Dataclass

```python
@dataclass
class FieldRandomizationConfig:
    enabled: bool = True
    mode: RandomizationMode = RandomizationMode.CONSTRAINED
    constraints: Optional[Dict] = None
    sequence: Optional[List[Any]] = None
    custom_generator: Optional[Callable] = None
    dependencies: List[str] = field(default_factory=list)
```

### RandomizationMode Enum

- `DETERMINISTIC`: Fixed values
- `CONSTRAINED`: Weighted random selection
- `DIRECTED`: Directed test patterns  
- `SEQUENCE`: Sequential value cycling
- `CUSTOM`: Custom generator functions

## Best Practices

1. **Use Method Chaining**: Leverage fluent API for clean configuration
2. **Group Related Fields**: Use groups for coherent configuration
3. **Handle Dependencies**: Ensure dependencies are properly declared
4. **Seed for Reproducibility**: Use seeds for debugging and regression
5. **Validate Configurations**: Check field configs before test runs
6. **Protocol-Specific Patterns**: Create reusable configuration functions

This documentation provides a comprehensive guide to using RandomizationConfig for flexible, maintainable randomization in protocol verification environments.