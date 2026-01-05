<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# debug_object.py

Simple debugging utilities for object inspection and detailed logging. This module provides helpful functions for examining object attributes, types, and values during development and debugging.

## Overview

The `debug_object.py` module contains utility functions for introspecting Python objects, making it easier to debug complex objects in verification environments. It's particularly useful for examining signal objects, packet contents, and component states.

## Functions

### `get_object_details(obj) -> Dict[str, Dict[str, Any]]`

Returns a dictionary with all attributes of the given object, including their types and values.

**Parameters:**
- `obj`: The object to inspect

**Returns:** Dictionary with attribute names as keys, and dictionaries containing 'type' and 'value' as values

**Features:**
- Skips private attributes (those starting with `_`)
- Skips methods and callable objects
- Handles attributes that may raise exceptions when accessed
- Provides type information for each attribute

```python
# Example usage
class MyComponent:
    def __init__(self):
        self.address = 0x1000
        self.data = 0xDEADBEEF
        self.enabled = True
        self.name = "TestComponent"

component = MyComponent()
details = get_object_details(component)

# Returns:
# {
#     'address': {'type': 'int', 'value': 4096},
#     'data': {'type': 'int', 'value': 3735928559}, 
#     'enabled': {'type': 'bool', 'value': True},
#     'name': {'type': 'str', 'value': 'TestComponent'}
# }
```

### `print_object_details(obj, log, name="Object", max_value_length=5000)`

Prints formatted details of all attributes of the given object to a logger.

**Parameters:**
- `obj`: The object to inspect
- `log`: Logger instance to write output to
- `name`: A name to identify the object in the output (default: "Object")
- `max_value_length`: Maximum length for printing attribute values (default: 5000)

**Output Format:**
```
=== {name} Details ===
Class: {ClassName}
Total attributes: {count}
--------------------------------------------------------------------------------
attribute_name: type_name = value
...
--------------------------------------------------------------------------------
```

```python
# Example usage
import logging
log = logging.getLogger(__name__)

class SignalContainer:
    def __init__(self):
        self.clock = None
        self.reset = None
        self.valid = True
        self.data = bytearray([0xDE, 0xAD, 0xBE, 0xEF])

signals = SignalContainer()
print_object_details(signals, log, "Signal Container")

# Output:
# === Signal Container Details ===
# Class: SignalContainer
# Total attributes: 4
# --------------------------------------------------------------------------------
# clock: NoneType = None
# data: bytearray = bytearray(b'\xde\xad\xbe\xef')
# reset: NoneType = None
# valid: bool = True
# --------------------------------------------------------------------------------
```

### `print_dict_to_log(name, d, log, prefix="")`

Print dictionary to logger with each key-value pair on its own line.

**Parameters:**
- `name`: Name/title for the dictionary output
- `d`: Dictionary to print
- `log`: Logger instance to write output to
- `prefix`: Optional prefix for each line (default: "")

**Output Format:**
```
=== {name} Details ===
{prefix}::{key}: {value}
...
```

```python
# Example usage
config_dict = {
    'addr_width': 32,
    'data_width': 64, 
    'protocol': 'AXI4',
    'endianness': 'little'
}

print_dict_to_log("Configuration", config_dict, log, prefix="CONFIG")

# Output:
# === Configuration Details ===
# CONFIG::addr_width: 32
# CONFIG::data_width: 64
# CONFIG::endianness: little
# CONFIG::protocol: AXI4
```

## Usage Patterns

### Basic Object Inspection

```python
def debug_component_state(component, log):
    """Debug helper to inspect component state"""
    log.info("=== Component State Debug ===")
    
    # Get detailed attribute information
    details = get_object_details(component)
    
    # Print formatted details
    print_object_details(component, log, "Component State")
    
    # Print specific attribute if needed
    if 'status' in details:
        log.info(f"Component status: {details['status']['value']} ({details['status']['type']})")
```

### Signal Debugging

```python
def debug_bus_signals(bus, log):
    """Debug all signals on a bus object"""
    print_object_details(bus, log, "Bus Signals")
    
    # Get raw details for programmatic inspection
    details = get_object_details(bus)
    
    # Check for specific signal types
    signal_attrs = []
    for attr_name, info in details.items():
        if 'signal' in info['type'].lower():
            signal_attrs.append(attr_name)
    
    if signal_attrs:
        log.info(f"Found {len(signal_attrs)} signals: {signal_attrs}")
    else:
        log.warning("No signal attributes found on bus")
```

### Configuration Debugging

```python
def debug_field_config(field_config, log):
    """Debug field configuration contents"""
    config_dict = {}
    
    # Extract field information
    for field_name in field_config.field_names():
        field_def = field_config.get_field(field_name)
        config_dict[field_name] = {
            'bits': field_def.bits,
            'format': field_def.format,
            'default': field_def.default
        }
    
    print_dict_to_log("Field Configuration", config_dict, log, "FIELD")
```

### Transaction Debugging

```python
def debug_transaction(packet, log):
    """Debug transaction packet contents"""
    log.info("=== Transaction Debug ===")
    
    # Print full packet details
    print_object_details(packet, log, "Transaction Packet")
    
    # Print FIFO representation
    if hasattr(packet, 'pack_for_fifo'):
        fifo_data = packet.pack_for_fifo()
        print_dict_to_log("FIFO Data", fifo_data, log, "FIFO")
    
    # Check for timing information
    details = get_object_details(packet)
    timing_attrs = ['start_time', 'end_time', 'duration']
    
    for attr in timing_attrs:
        if attr in details and details[attr]['value'] != 0:
            log.info(f"Timing - {attr}: {details[attr]['value']}")
```

### Error Handling in Object Inspection

```python
def safe_object_debug(obj, log, obj_name="Unknown"):
    """Safely debug an object with error handling"""
    try:
        print_object_details(obj, log, obj_name)
    except Exception as e:
        log.error(f"Failed to debug {obj_name}: {e}")
        
        # Fallback - basic information
        log.info(f"{obj_name} type: {type(obj)}")
        log.info(f"{obj_name} dir: {[attr for attr in dir(obj) if not attr.startswith('_')]}")
```

### Comparative Debugging

```python
def compare_objects(obj1, obj2, log, name1="Object1", name2="Object2"):
    """Compare two objects and highlight differences"""
    details1 = get_object_details(obj1)
    details2 = get_object_details(obj2)
    
    # Find common attributes
    common_attrs = set(details1.keys()) & set(details2.keys())
    only_in_1 = set(details1.keys()) - set(details2.keys())
    only_in_2 = set(details2.keys()) - set(details1.keys())
    
    log.info(f"=== Comparing {name1} vs {name2} ===")
    
    # Report differences
    differences = []
    for attr in common_attrs:
        if details1[attr]['value'] != details2[attr]['value']:
            differences.append(attr)
            log.info(f"DIFF {attr}: {name1}={details1[attr]['value']} vs {name2}={details2[attr]['value']}")
    
    if only_in_1:
        log.info(f"Only in {name1}: {list(only_in_1)}")
    
    if only_in_2:
        log.info(f"Only in {name2}: {list(only_in_2)}")
        
    if not differences and not only_in_1 and not only_in_2:
        log.info("Objects are identical")
    
    return {
        'differences': differences,
        'only_in_1': list(only_in_1),
        'only_in_2': list(only_in_2)
    }
```

## Integration with CocoTB

### Signal State Debugging

```python
@cocotb.coroutine
def debug_signal_states(dut, log):
    """Debug all DUT signal states"""
    log.info("=== DUT Signal States ===")
    
    # Get all top-level signals
    signals = {}
    for attr_name in dir(dut):
        if not attr_name.startswith('_'):
            try:
                attr = getattr(dut, attr_name)
                if hasattr(attr, 'value'):
                    signals[attr_name] = {
                        'value': str(attr.value),
                        'type': type(attr).__name__
                    }
            except:
                pass
    
    print_dict_to_log("DUT Signals", signals, log, "SIG")
```

### Component State Snapshots

```python
def create_debug_snapshot(component, log, snapshot_name=""):
    """Create a debug snapshot of component state"""
    timestamp = cocotb.utils.get_sim_time()
    log.info(f"=== Debug Snapshot: {snapshot_name} at {timestamp} ===")
    
    print_object_details(component, log, f"Component Snapshot ({snapshot_name})")
    
    # Include statistics if available
    if hasattr(component, 'stats') and hasattr(component.stats, 'get_stats'):
        stats = component.stats.get_stats()
        print_dict_to_log("Component Statistics", stats, log, "STAT")
```

## Error Handling

The debug functions include robust error handling:

- **Attribute Access Errors**: Safely handle attributes that raise exceptions
- **Type Conversion Errors**: Gracefully handle objects that can't be converted to strings
- **Missing Logger**: Functions can work even if logger is None (will use print as fallback)
- **Large Objects**: Automatic truncation of large string representations

## Best Practices

1. **Use During Development**: Enable detailed debugging during test development, then reduce verbosity for production runs

2. **Snapshot Key States**: Take debug snapshots at important test milestones

3. **Compare Before/After**: Use object comparison to understand state changes

4. **Filter Output**: Use `max_value_length` to control output size for large objects

5. **Conditional Debugging**: Use log levels to control when debugging is active

```python
if log.isEnabledFor(logging.DEBUG):
    print_object_details(complex_object, log, "Debug State")
```
