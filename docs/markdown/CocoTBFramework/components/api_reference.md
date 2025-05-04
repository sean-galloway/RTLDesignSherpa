# CocoTBFramework Components API Reference

This document provides a consolidated API reference for all core components in the CocoTBFramework.

## ArbiterMonitor

### ArbiterTransaction

```python
ArbiterTransaction = namedtuple('ArbiterTransaction', [
    'req_vector',      # Request vector from clients
    'gnt_vector',      # Grant vector indicating which client was selected
    'gnt_id',          # ID of the granted client
    'cycle_count',     # Number of cycles between request and grant
    'timestamp',       # Timestamp when grant was issued
    'weights',         # Optional weights (for weighted arbiters)
    'metadata'         # Dictionary for any additional metadata
])
```

### ArbiterMonitor

```python
class ArbiterMonitor:
    def __init__(self, dut, title, clock, reset_n, req_signal, gnt_valid_signal, gnt_signal,
                 gnt_id_signal, gnt_ack_signal=None, block_arb_signal=None,
                 max_thresh_signal=None, is_weighted=False, clients=None, log=None,
                 clock_period_ns=(10, "ns"))
    
    def add_transaction_callback(self, callback)
    def add_reset_callback(self, callback)
    def get_transaction_count(self)
    def get_client_stats(self, client_id)
    def get_fairness_index(self)
```

### RoundRobinArbiterMonitor

```python
class RoundRobinArbiterMonitor(ArbiterMonitor):
    def __init__(self, dut, title, clock, reset_n,
                 req_signal, gnt_valid_signal, gnt_signal, gnt_id_signal,
                 gnt_ack_signal=None, block_arb_signal=None, clients=None,
                 log=None, clock_period_ns=10)
    
    def get_priority_changes(self)
```

### WeightedRoundRobinArbiterMonitor

```python
class WeightedRoundRobinArbiterMonitor(ArbiterMonitor):
    def __init__(self, dut, title, clock, reset_n,
                 req_signal, gnt_valid_signal, gnt_signal, gnt_id_signal,
                 gnt_ack_signal=None, block_arb_signal=None,
                 max_thresh_signal=None, clients=None, log=None,
                 clock_period_ns=10)
    
    def get_inferred_weights(self)
    def get_weight_distribution(self)
```

## ConstrainedRandom

```python
class ConstrainedRandom:
    def __init__(self, constraints, weights, is_integer=True)
    def next(self)
```

## DebugObject

```python
def get_object_details(obj)
def print_object_details(obj, log, name="Object", max_value_length=5000)
def print_dict_to_log(name, d, log, prefix="")
```

## FieldConfig

### FieldDefinition

```python
@dataclass
class FieldDefinition:
    name: str
    bits: int
    default: int = 0
    format: str = "hex"
    display_width: int = 0
    active_bits: Optional[Tuple[int, int]] = None
    description: Optional[str] = None
    
    def to_dict(self) -> Dict[str, Any]
    @classmethod
    def from_dict(cls, name: str, field_dict: Dict[str, Any]) -> 'FieldDefinition'
```

### FieldConfig

```python
class FieldConfig:
    def __init__(self)
    def add_field(self, field_def: FieldDefinition) -> 'FieldConfig'
    def add_field_dict(self, name: str, field_dict: Dict[str, Any]) -> 'FieldConfig'
    def remove_field(self, name: str) -> 'FieldConfig'
    def get_field(self, name: str) -> FieldDefinition
    def has_field(self, name: str) -> bool
    def field_names(self) -> List[str]
    def fields(self) -> List[FieldDefinition]
    def items(self)
    def to_dict(self) -> Dict[str, Dict[str, Any]]
    def debug_str(self, indent=0) -> str
    def update_field_width(self, field_name: str, new_bits: int, update_active_bits: bool = True) -> 'FieldConfig'
    def get_total_bits(self) -> int
    
    @classmethod
    def from_dict(cls, field_dict: Dict[str, Dict[str, Any]]) -> 'FieldConfig'
    @classmethod
    def validate_and_create(cls, field_dict: Dict[str, Dict[str, Any]], raise_errors: bool = False) -> 'FieldConfig'
    @classmethod
    def create_data_only(cls, data_width: int = 32) -> 'FieldConfig'
    @classmethod
    def create_standard(cls, addr_width: int = 32, data_width: int = 32) -> 'FieldConfig'
    @classmethod
    def create_multi_data(cls, addr_width: int = 4, ctrl_width: int = 4, data_width: int = 8, num_data: int = 2) -> 'FieldConfig'
```

## FlexRandomizer

```python
class FlexRandomizer(Randomized):
    def __init__(self, constraints: Dict)
    def next(self)
    def set_sequence(self, delay_name: str, sequence: List)
    def set_generator(self, delay_name: str, generator: Callable)
    def reset_to_random(self, delay_name: str)
```

## MemoryModel

```python
class MemoryModel:
    def __init__(self, num_lines, bytes_per_line, log, preset_values=None, debug=None)
    def write(self, address, data, strobe)
    def read(self, address, length)
    def reset(self, to_preset=False)
    def expand(self, additional_lines)
    def dump(self)
    def integer_to_bytearray(self, value, byte_length=None)
    def bytearray_to_integer(self, byte_array)
```

## Packet

### Global Functions

```python
def get_field_cache_stats() -> Dict[str, Any]
def clear_field_cache()
```

### Packet Class

```python
class Packet:
    def __init__(self, field_config: Union[FieldConfig, Dict[str, Dict[str, Any]]],
                 skip_compare_fields: Optional[List[str]] = None, **kwargs)
    
    def mask_field_value(self, value, field_name)
    def shift_for_fifo(self, value, field_name)
    def expand_from_fifo(self, value, field_name)
    def pack_for_fifo(self)
    def unpack_from_fifo(self, fifo_data)
    def get_total_bits(self)
    def formatted(self, compact=False, show_fifo=False)
    def copy(self)
```

## RandomizationConfig

### Enumerations

```python
class RandomizationMode(Enum):
    DETERMINISTIC = auto()  # Fixed values, not random
    CONSTRAINED = auto()    # Constrained random with weights
    DIRECTED = auto()       # Directed test patterns
    SEQUENCE = auto()       # Sequence of values in order
    CUSTOM = auto()         # Custom generator function
```

### Configuration Classes

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

### Main Configuration Class

```python
class RandomizationConfig:
    def __init__(self, protocol_name: str = "generic", seed: Optional[int] = None)
    
    def configure_field(self, field_name: str, config: FieldRandomizationConfig) -> 'RandomizationConfig'
    def add_to_group(self, group_name: str, field_name: str) -> 'RandomizationConfig'
    def configure_group(self, group_name: str, **config_kwargs) -> 'RandomizationConfig'
    def get_field_config(self, field_name: str) -> FieldRandomizationConfig
    def generate_value(self, field_name: str) -> Any
    def generate_values(self, field_names: List[str]) -> Dict[str, Any]
    def enable(self) -> 'RandomizationConfig'
    def disable(self) -> 'RandomizationConfig'
    def set_seed(self, seed: int) -> 'RandomizationConfig'
    def reset_sequences(self) -> 'RandomizationConfig'
    
    # Helper methods
    def create_constrained_config(self, field_name: str, bins: List[Union[Tuple[int, int], List[Any]]],
                                 weights: Optional[List[float]] = None) -> 'RandomizationConfig'
    def create_sequence_config(self, field_name: str, sequence: List[Any]) -> 'RandomizationConfig'
    def create_custom_config(self, field_name: str, generator: Callable) -> 'RandomizationConfig'
```

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
