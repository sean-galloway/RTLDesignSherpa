# DebugObject

## Overview

The `debug_object.py` module provides utility functions for debugging and inspecting Python objects during verification. It offers capabilities to extract, format, and display object attributes and their values in a structured way, which is particularly useful for complex verification components.

## Functions

### get_object_details

```python
def get_object_details(obj)
```

Returns a dictionary with all attributes of the given object, including their types and values.

#### Parameters

- `obj`: The object to inspect

#### Returns

A dictionary with attribute names as keys, and dictionaries containing 'type' and 'value' as values.

#### Features

- Skips private attributes (those starting with underscore)
- Excludes methods and callable objects
- Handles exceptions when accessing attributes
- Provides both type and value information

### print_object_details

```python
def print_object_details(obj, log, name="Object", max_value_length=5000)
```

Prints formatted details of all attributes of the given object to a logger.

#### Parameters

- `obj`: The object to inspect
- `log`: Logger object to print details to
- `name`: A name to identify the object in the output (default: "Object")
- `max_value_length`: Maximum length for printing attribute values (default: 5000)

#### Features

- Formats output with clear section headers
- Limits output length for large values
- Sorts attributes by name for easier lookup
- Provides class information and attribute count

### print_dict_to_log

```python
def print_dict_to_log(name, d, log, prefix="")
```

Prints a dictionary to a logger with each key on its own line.

#### Parameters

- `name`: Name for the dictionary in the output
- `d`: Dictionary to print
- `log`: Logger object to print details to
- `prefix`: Optional prefix for each line (default: "")

## Example Usage

### Basic Object Inspection

```python
from CocoTBFramework.components.debug_object import get_object_details, print_object_details
import logging

# Create a logger
log = logging.getLogger("test_logger")
log.setLevel(logging.DEBUG)

# Example class for demonstration
class TestComponent:
    def __init__(self):
        self.name = "test_component"
        self.value = 42
        self.enabled = True
        self.config = {"mode": "normal", "timeout": 100}
    
    def do_something(self):
        pass

# Create an instance
component = TestComponent()

# Get object details as a dictionary
details = get_object_details(component)
print(f"Component has {len(details)} public attributes")

# Print full details to the logger
print_object_details(component, log, "TestComponent")
```

### Using with Verification Components

```python
from CocoTBFramework.components.debug_object import print_object_details
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Create a randomizer
constraints = {
    'delay': ([(1, 10), (20, 30)], [0.8, 0.2]),
    'mode': ([(0, 3)], [1.0])
}
randomizer = FlexRandomizer(constraints)

# Generate some random values
randomizer.next()
randomizer.next()

# Debug the randomizer state
print_object_details(randomizer, log, "FlexRandomizer")
```

### Dictionary Debugging

```python
from CocoTBFramework.components.debug_object import print_dict_to_log

# Example configuration dictionary
config = {
    "data_width": 32,
    "addr_width": 64,
    "timeout": 1000,
    "retries": 3,
    "modes": ["normal", "bypass", "loopback"]
}

# Print to logger
print_dict_to_log("Configuration", config, log)
```

## Notes

- These utilities are particularly useful for debugging complex verification environments
- Using a structured approach to debug information makes it easier to find issues
- The functions handle large objects gracefully with truncation and selective display
- Intended for development and debug only, not for production code paths

## See Also

- [ArbiterMonitor](arbiter_monitor.md) - Can be debugged with these utilities
- [FlexRandomizer](flex_randomizer.md) - Complex object for which debugging might be useful

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
