# randomization_config.py

Randomization Configuration for Protocol Verification that provides a flexible configuration framework for controlling randomization behavior in protocol verification environments, using FlexRandomizer as the underlying randomization engine.

## Overview

The `randomization_config.py` module provides a high-level configuration framework for managing complex randomization scenarios. It supports multiple randomization modes, field dependencies, and adaptive configuration patterns while leveraging FlexRandomizer for the underlying randomization engine.

### Key Features
- **Multiple randomization modes**: Deterministic, constrained, directed, sequence, and custom
- **Field dependency management**: Handle complex inter-field relationships
- **Adaptive configuration**: Dynamic randomization based on test conditions
- **Protocol independence**: Works across GAXI, FIFO, APB, AXI4, etc.
- **Integration with FlexRandomizer**: Leverages proven randomization engine

## Enums and Data Classes

### RandomizationMode

Defines possible randomization modes.

```python
class RandomizationMode(Enum):
    DETERMINISTIC = auto()  # Fixed values, not random
    CONSTRAINED = auto()    # Constrained random with weights
    DIRECTED = auto()       # Directed test patterns  
    SEQUENCE = auto()       # Sequence of values in order
    CUSTOM = auto()         # Custom generator function
```

### FieldRandomizationConfig

Configuration for randomizing a specific field using dataclass structure.

#### Constructor

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

**Parameters:**
- `enabled`: Whether randomization is enabled for this field
- `mode`: Randomization mode to use
- `constraints`: Constraints for constrained random mode
- `sequence`: Sequence values for sequence mode
- `custom_generator`: Custom generator function for custom mode
- `dependencies`: List of field names this field depends on

```python
# Constrained random configuration
config = FieldRandomizationConfig(
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0, 10), (20, 30)],
        "weights": [0.7, 0.3]
    }
)

# Sequence configuration
seq_config = FieldRandomizationConfig(
    mode=RandomizationMode.SEQUENCE,
    sequence=[1, 2, 4, 8, 16]
)

# Custom generator configuration
def custom_gen(current_values):
    base = current_values.get('base_field', 0)
    return base * 2 + random.randint(0, 5)

custom_config = FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM,
    custom_generator=custom_gen,
    dependencies=['base_field']
)
```

## Core Class

### RandomizationConfig

Main configuration class for randomizing protocol fields with comprehensive dependency management.

#### Constructor

```python
RandomizationConfig(protocol_name: str = "generic", seed: Optional[int] = None)
```

**Parameters:**
- `protocol_name`: Name of the protocol (e.g., "AXI4", "APB")
- `seed`: Master random seed for reproducibility

```python
# Create randomization config
config = RandomizationConfig(protocol_name="AXI4", seed=12345)
```

#### Core Properties

- **`protocol_name`**: Protocol identifier
- **`master_seed`**: Master seed for reproducible randomization
- **`field_configs`**: Dictionary mapping field names to configurations
- **`group_configs`**: Dictionary grouping fields for collective configuration
- **`enabled`**: Global enable/disable flag
- **`current_values`**: Dictionary of current field values

## Field Configuration

### `configure_field(field_name: str, config: FieldRandomizationConfig) -> 'RandomizationConfig'`

Configure randomization for a specific field.

**Parameters:**
- `field_name`: Name of the field to configure
- `config`: Field randomization configuration

**Returns:** Self for method chaining

```python
# Configure address field with constrained random
addr_config = FieldRandomizationConfig(
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0x1000, 0x1FFF), (0x2000, 0x2FFF)],
        "weights": [0.6, 0.4]
    }
)
config.configure_field("addr", addr_config)

# Configure data field with sequence
data_config = FieldRandomizationConfig(
    mode=RandomizationMode.SEQUENCE,
    sequence=[0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF00]
)
config.configure_field("data", data_config)
```

## Group Configuration

### `add_to_group(group_name: str, field_name: str) -> 'RandomizationConfig'`

Add a field to a named group for collective configuration.

```python
# Create timing group
config.add_to_group("timing", "setup_delay")
config.add_to_group("timing", "hold_delay")
config.add_to_group("timing", "clock_delay")

# Create address group
config.add_to_group("addressing", "addr")
config.add_to_group("addressing", "addr_mask")
```

### `configure_group(group_name: str, **config_kwargs) -> 'RandomizationConfig'`

Configure all fields in a group with the same settings.

**Parameters:**
- `group_name`: Group to configure
- `**config_kwargs`: Configuration parameters to apply to all fields

```python
# Configure all timing fields as sequences
config.configure_group(
    "timing",
    mode=RandomizationMode.SEQUENCE,
    sequence=[0, 1, 2, 5, 10]
)

# Configure all addressing fields as constrained random
config.configure_group(
    "addressing", 
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0x0000, 0xFFFF)],
        "weights": [1.0]
    }
)
```

## Value Generation

### `generate_value(field_name: str) -> Any`

Generate a random value for a field based on its configuration.

**Parameters:**
- `field_name`: Name of the field

**Returns:** Generated value according to the field's configuration

```python
# Generate values for configured fields
addr_value = config.generate_value("addr")
data_value = config.generate_value("data")
delay_value = config.generate_value("setup_delay")

print(f"Generated: addr=0x{addr_value:X}, data=0x{data_value:X}, delay={delay_value}")
```

### `generate_values(field_names: List[str]) -> Dict[str, Any]`

Generate values for multiple fields at once, respecting dependencies.

**Parameters:**
- `field_names`: List of field names

**Returns:** Dictionary mapping field names to generated values

```python
# Generate all values in dependency order
field_names = ["base_field", "dependent_field", "addr", "data"]
values = config.generate_values(field_names)

print(f"Generated values: {values}")
# Output: {'base_field': 10, 'dependent_field': 25, 'addr': 0x1500, 'data': 0xDEADBEEF}
```

## Control Methods

### `enable() -> 'RandomizationConfig'`

Enable randomization.

```python
config.enable()
```

### `disable() -> 'RandomizationConfig'`

Disable randomization (returns default values).

```python
config.disable()
```

### `set_seed(seed: int) -> 'RandomizationConfig'`

Set the master random seed.

```python
config.set_seed(54321)  # Set new seed for reproducibility
```

### `reset_sequences() -> 'RandomizationConfig'`

Reset all sequence positions to start.

```python
config.reset_sequences()  # Reset all sequences to beginning
```

## Convenience Methods

### `create_constrained_config(field_name: str, bins: List[Union[Tuple[int, int], List[Any]]], weights: Optional[List[float]] = None) -> 'RandomizationConfig'`

Create a constrained randomization configuration for a field.

```python
# Create constrained address field
config.create_constrained_config(
    "addr",
    bins=[(0x1000, 0x1FFF), (0x8000, 0x8FFF)],
    weights=[0.8, 0.2]
)
```

### `create_sequence_config(field_name: str, sequence: List[Any]) -> 'RandomizationConfig'`

Create a sequence-based configuration for a field.

```python
# Create burst length sequence
config.create_sequence_config("burst_len", [1, 2, 4, 8, 16])
```

### `create_custom_config(field_name: str, generator: Callable) -> 'RandomizationConfig'`

Create a custom randomization configuration for a field.

```python
def address_generator(current_values):
    """Generate aligned addresses based on transfer size"""
    size = current_values.get('transfer_size', 4)
    base = random.randint(0x1000, 0x8000)
    return (base // size) * size  # Align to transfer size

config.create_custom_config("addr", address_generator)
```

## Usage Patterns

### Basic Protocol Randomization

```python
# Set up AXI4 randomization
axi_config = RandomizationConfig(protocol_name="AXI4", seed=12345)

# Configure write address channel
axi_config.create_constrained_config(
    "awaddr",
    bins=[(0x00000000, 0x7FFFFFFF), (0x80000000, 0xFFFFFFFF)],
    weights=[0.8, 0.2]  # Favor lower addresses
)

axi_config.create_sequence_config("awlen", [0, 1, 3, 7, 15])  # Common burst lengths
axi_config.create_sequence_config("awsize", [0, 1, 2, 3])     # 1, 2, 4, 8 bytes

# Configure write data with dependencies
def data_generator(current_values):
    """Generate data based on transfer size"""
    size = current_values.get('awsize', 2)
    bytes_per_beat = 1 << size
    
    if bytes_per_beat == 1:
        return random.randint(0, 0xFF)
    elif bytes_per_beat == 2:
        return random.randint(0, 0xFFFF)
    elif bytes_per_beat == 4:
        return random.randint(0, 0xFFFFFFFF)
    else:
        return random.randint(0, 0xFFFFFFFFFFFFFFFF)

axi_config.create_custom_config("wdata", data_generator)

# Generate transaction
field_names = ["awaddr", "awlen", "awsize", "wdata"]
transaction_values = axi_config.generate_values(field_names)
```

### Advanced Dependency Management

```python
class ProtocolRandomizer:
    def __init__(self):
        self.config = RandomizationConfig("Advanced", seed=None)
        self._setup_dependencies()
    
    def _setup_dependencies(self):
        """Set up complex field dependencies"""
        
        # Base configuration fields
        self.config.create_sequence_config("mode", ["SINGLE", "BURST", "WRAP"])
        self.config.create_constrained_config("base_addr", [(0x1000, 0x8000)], [1.0])
        
        # Address depends on mode and base address
        def address_generator(values):
            mode = values.get("mode", "SINGLE")
            base = values.get("base_addr", 0x1000)
            
            if mode == "SINGLE":
                return base
            elif mode == "BURST":
                # Burst addresses are sequential
                offset = random.randint(0, 64) * 4
                return base + offset
            else:  # WRAP
                # Wrap addresses within boundary
                boundary = 256
                offset = random.randint(0, boundary-4)
                return (base & ~(boundary-1)) + offset
        
        self.config.create_custom_config("addr", address_generator)
        
        # Length depends on mode
        def length_generator(values):
            mode = values.get("mode", "SINGLE")
            
            if mode == "SINGLE":
                return 1
            elif mode == "BURST":
                return random.choice([2, 4, 8, 16])
            else:  # WRAP
                return random.choice([4, 8, 16])  # Power of 2 only
        
        self.config.create_custom_config("length", length_generator)
        
        # Data pattern depends on mode
        def data_generator(values):
            mode = values.get("mode", "SINGLE")
            length = values.get("length", 1)
            
            if mode == "SINGLE":
                return [random.randint(0, 0xFFFFFFFF)]
            elif mode == "BURST":
                # Sequential data
                base = random.randint(0, 0xFFFF0000)
                return [base + i for i in range(length)]
            else:  # WRAP
                # Pattern data
                pattern = random.choice([0xAAAAAAAA, 0x55555555, 0xDEADBEEF])
                return [pattern] * length
        
        self.config.create_custom_config("data_pattern", data_generator)
    
    def generate_transaction(self):
        """Generate a complete transaction with dependencies"""
        fields = ["mode", "base_addr", "addr", "length", "data_pattern"]
        return self.config.generate_values(fields)
    
    def set_test_mode(self, test_mode):
        """Adapt randomization based on test mode"""
        if test_mode == "directed":
            # Use more deterministic patterns
            self.config.create_sequence_config("mode", ["BURST"])
            self.config.create_sequence_config("base_addr", [0x1000, 0x2000, 0x4000])
            
        elif test_mode == "stress":
            # Use more random patterns
            self.config.create_constrained_config(
                "mode", 
                bins=[("SINGLE",), ("BURST",), ("WRAP",)],
                weights=[0.2, 0.5, 0.3]
            )
            
        elif test_mode == "corner_case":
            # Focus on edge cases
            self.config.create_sequence_config("length", [1, 2, 15, 16, 255, 256])
```

### Protocol-Specific Configuration

```python
class GAXIRandomizationConfig(RandomizationConfig):
    """GAXI-specific randomization configuration"""
    
    def __init__(self, seed=None):
        super().__init__("GAXI", seed)
        self._setup_gaxi_fields()
    
    def _setup_gaxi_fields(self):
        """Set up GAXI-specific field randomization"""
        
        # Valid/Ready timing
        self.create_sequence_config("valid_delay", [0, 0, 0, 1, 2])  # Mostly back-to-back
        self.create_sequence_config("ready_delay", [0, 1, 2, 5])
        
        # Address patterns
        self.create_constrained_config(
            "addr",
            bins=[(0x1000, 0x1FFF), (0x2000, 0x3FFF), (0x8000, 0x8FFF)],
            weights=[0.5, 0.3, 0.2]
        )
        
        # Data patterns
        data_patterns = [
            0x00000000, 0xFFFFFFFF, 0xAAAAAAAA, 0x55555555,
            0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0x87654321
        ]
        self.create_sequence_config("data", data_patterns)
    
    def set_traffic_pattern(self, pattern):
        """Set specific traffic patterns"""
        if pattern == "bursty":
            self.create_sequence_config("valid_delay", [0, 0, 0, 0, 10, 15, 20])
            
        elif pattern == "throttled":
            self.create_sequence_config("valid_delay", [2, 3, 4, 5])
            self.create_sequence_config("ready_delay", [1, 2, 3])
            
        elif pattern == "streaming":
            self.create_sequence_config("valid_delay", [0])
            self.create_sequence_config("ready_delay", [0])

class FIFORandomizationConfig(RandomizationConfig):
    """FIFO-specific randomization configuration"""
    
    def __init__(self, seed=None):
        super().__init__("FIFO", seed)
        self._setup_fifo_fields()
    
    def _setup_fifo_fields(self):
        """Set up FIFO-specific field randomization"""
        
        # Write/Read timing
        self.create_constrained_config(
            "write_interval",
            bins=[(0, 0), (1, 3), (10, 20)],
            weights=[0.6, 0.3, 0.1]
        )
        
        self.create_constrained_config(
            "read_interval", 
            bins=[(0, 0), (1, 5), (20, 50)],
            weights=[0.5, 0.4, 0.1]
        )
        
        # Data generation based on FIFO depth utilization
        def data_based_on_utilization(values):
            # This would require integration with FIFO monitor
            # For now, return random data
            return random.randint(0, 0xFFFFFFFF)
        
        self.create_custom_config("data", data_based_on_utilization)
```

### Test Framework Integration

```python
@cocotb.test()
def randomized_protocol_test(dut):
    """Test using randomization configuration"""
    
    # Set up randomization
    rand_config = RandomizationConfig("TestProtocol", seed=12345)
    
    # Configure fields
    rand_config.create_constrained_config("cmd", bins=[(1, 3)], weights=[1.0])
    rand_config.create_constrained_config("addr", bins=[(0x1000, 0x8000)], weights=[1.0])
    rand_config.create_sequence_config("data", [0xDEADBEEF, 0xCAFEBABE, 0x12345678])
    
    # Generate and run test transactions
    for i in range(100):
        # Generate random transaction
        values = rand_config.generate_values(["cmd", "addr", "data"])
        
        # Drive transaction
        yield drive_transaction(dut, values)
        
        # Capture and validate response
        response = yield capture_response(dut)
        validate_response(values, response)
        
        # Adaptive configuration based on results
        if i == 50:  # Switch pattern halfway through
            rand_config.create_sequence_config("cmd", [2])  # Focus on writes
            rand_config.reset_sequences()  # Reset sequences

@cocotb.coroutine
def drive_transaction(dut, values):
    """Drive transaction with randomized values"""
    dut.cmd.value = values["cmd"]
    dut.addr.value = values["addr"] 
    dut.data.value = values["data"]
    dut.valid.value = 1
    
    yield RisingEdge(dut.clk)
    dut.valid.value = 0

def validate_response(values, response):
    """Validate response against input"""
    if values["cmd"] == 1:  # READ
        assert response.data != -1, "Read returned undefined data"
    elif values["cmd"] == 2:  # WRITE
        assert response.status == 0, "Write failed"
```

### Performance Optimization

```python
class OptimizedRandomizationConfig:
    """Optimized randomization for high-performance testing"""
    
    def __init__(self, field_names, seed=None):
        self.config = RandomizationConfig("Optimized", seed)
        self.field_names = field_names
        self.cached_generators = {}
        
        # Pre-configure all fields
        self._setup_optimized_fields()
        
        # Pre-generate FlexRandomizer instances
        self._create_randomizer_cache()
    
    def _setup_optimized_fields(self):
        """Set up fields for optimal generation"""
        for field_name in self.field_names:
            # Use simple constrained random for performance
            self.config.create_constrained_config(
                field_name,
                bins=[(0, 0xFFFFFFFF)],
                weights=[1.0]
            )
    
    def _create_randomizer_cache(self):
        """Create cached randomizers for performance"""
        # This would create optimized FlexRandomizer instances
        # for high-throughput value generation
        pass
    
    def generate_batch(self, batch_size=1000):
        """Generate batch of randomized values for performance"""
        batch = []
        for _ in range(batch_size):
            values = self.config.generate_values(self.field_names)
            batch.append(values)
        return batch
```

## Advanced Patterns

### Conditional Randomization

```python
def setup_conditional_randomization(config):
    """Set up randomization that changes based on conditions"""
    
    # Phase-based randomization
    current_phase = "setup"  # Would be set by test framework
    
    if current_phase == "setup":
        config.create_sequence_config("delay", [10, 15, 20])
        config.create_constrained_config("addr", [(0x1000, 0x1FFF)], [1.0])
        
    elif current_phase == "data_transfer":
        config.create_sequence_config("delay", [0, 0, 1])
        config.create_constrained_config("addr", [(0x2000, 0x8FFF)], [1.0])
        
    elif current_phase == "cleanup":
        config.create_sequence_config("delay", [5, 10])
        config.create_constrained_config("addr", [(0x9000, 0x9FFF)], [1.0])
```

### Adaptive Randomization

```python
class AdaptiveRandomizer:
    def __init__(self):
        self.config = RandomizationConfig("Adaptive")
        self.performance_history = []
        self.adaptation_threshold = 10
    
    def record_performance(self, metric):
        """Record performance metric for adaptation"""
        self.performance_history.append(metric)
        
        if len(self.performance_history) > self.adaptation_threshold:
            self._adapt_configuration()
    
    def _adapt_configuration(self):
        """Adapt configuration based on performance"""
        recent_performance = self.performance_history[-self.adaptation_threshold:]
        avg_performance = sum(recent_performance) / len(recent_performance)
        
        if avg_performance < 0.5:  # Low performance
            # Switch to simpler patterns
            self.config.create_sequence_config("delay", [0, 0, 0, 1])
            
        elif avg_performance > 0.9:  # High performance  
            # Switch to more complex patterns
            self.config.create_constrained_config(
                "delay",
                bins=[(0, 2), (5, 10), (20, 50)],
                weights=[0.5, 0.3, 0.2]
            )
```

## Best Practices

### 1. **Use Appropriate Randomization Modes**
```python
# Deterministic for debug
config.create_deterministic_config("debug_field", 0x1000)

# Constrained for normal testing  
config.create_constrained_config("normal_field", [(0, 100)], [1.0])

# Sequence for specific patterns
config.create_sequence_config("pattern_field", [1, 2, 4, 8])

# Custom for complex dependencies
config.create_custom_config("complex_field", complex_generator)
```

### 2. **Handle Dependencies Carefully**
```python
# Always list dependencies
dependent_config = FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM,
    custom_generator=dependent_generator,
    dependencies=["base_field", "size_field"]  # Explicit dependencies
)
```

### 3. **Use Seeds for Reproducibility**
```python
# Always set seed for reproducible tests
config = RandomizationConfig("Protocol", seed=12345)
```

### 4. **Group Related Fields**
```python
# Group related fields for easier management
config.add_to_group("timing", "setup_delay")
config.add_to_group("timing", "hold_delay")
config.configure_group("timing", mode=RandomizationMode.SEQUENCE, sequence=[0, 1, 2])
```

### 5. **Monitor and Adapt**
```python
# Monitor randomization effectiveness
def check_randomization_coverage():
    values_generated = []
    for _ in range(1000):
        values_generated.append(config.generate_value("test_field"))
    
    # Analyze distribution
    unique_values = len(set(values_generated))
    if unique_values < 10:
        log.warning("Low randomization diversity")
```

The RandomizationConfig provides a powerful framework for managing complex randomization scenarios while maintaining clarity and control over the verification process.
