# Debug Utilities Documentation

## Overview
The Debug Utilities module provides functions for examining and logging object attributes and structures during verification debugging. These utilities assist in understanding the internal state of objects, logging complex structures in a readable format, and troubleshooting verification issues.

## Functions

### `get_object_details(obj)`

```python
def get_object_details(obj):
    """
    Returns a dictionary with all attributes of the given object,
    including their types and values.

    Args:
        obj: The object to inspect

    Returns:
        Dictionary with attribute names as keys, and dictionaries containing
        'type' and 'value' as values
    """
```

This function creates a detailed mapping of an object's attributes, providing their types and values. It's useful for understanding complex objects without needing to add print statements throughout the code.

#### Key Features:
- Inspects all non-private attributes (excluding those starting with `_`)
- Skips methods and callable objects
- Handles exceptions when accessing attributes
- Returns a structured dictionary for easy processing

### `print_object_details(obj, log, name="Object", max_value_length=5000)`

```python
def print_object_details(obj, log, name="Object", max_value_length=5000):
    """
    Prints formatted details of all attributes of the given object.

    Args:
        obj: The object to inspect
        name: A name to identify the object in the output
        max_value_length: Maximum length for printing attribute values
    """
```

This function prints a formatted representation of an object's attributes to a log. It's particularly useful for debugging verification components during test execution.

#### Key Features:
- Formats output with section headers and separators
- Truncates long attribute values for readability
- Sorts attributes alphabetically
- Includes the object's class information

### `print_dict_to_log(name, d, log, prefix="")`

```python
def print_dict_to_log(name, d, log, prefix=""):
    """Print dictionary to logger with each key on its own line"""
```

This function prints a dictionary to a logger, formatting each key-value pair on its own line. It's useful for logging structured data.

#### Key Features:
- Formats output with a header
- Prefixes each line for hierarchical organization
- Places each key-value pair on a separate line for readability

## Usage Examples

### Basic Object Inspection

```python
# Create a logger
import logging
logger = logging.getLogger("debug")
logger.setLevel(logging.DEBUG)

# Create a handler
handler = logging.StreamHandler()
handler.setLevel(logging.DEBUG)
logger.addHandler(handler)

# Inspect an object
class TestObject:
    def __init__(self):
        self.int_val = 42
        self.str_val = "test string"
        self.list_val = [1, 2, 3]
        self.dict_val = {"key1": "value1", "key2": "value2"}
    
    def method(self):
        pass

# Create the object
test_obj = TestObject()

# Get object details
details = get_object_details(test_obj)
print(details)
# Output:
# {
#     'int_val': {'type': 'int', 'value': 42},
#     'str_val': {'type': 'str', 'value': 'test string'},
#     'list_val': {'type': 'list', 'value': [1, 2, 3]},
#     'dict_val': {'type': 'dict', 'value': {'key1': 'value1', 'key2': 'value2'}}
# }

# Print object details to log
print_object_details(test_obj, logger, name="TestObject")
# Output in log:
# === TestObject Details ===
# Class: TestObject
# Total attributes: 4
# --------------------------------------------------------------------------------
# dict_val: dict = {'key1': 'value1', 'key2': 'value2'}
# int_val: int = 42
# list_val: list = [1, 2, 3]
# str_val: str = test string
# --------------------------------------------------------------------------------
```

### Inspecting Verification Components

```python
# Create a verification component
class APBMonitor:
    def __init__(self, dut, log):
        self.dut = dut
        self.log = log
        self.transactions = []
        self.current_transaction = None
        self.state = "IDLE"
        self.stats = {
            "write_count": 0,
            "read_count": 0,
            "error_count": 0
        }
        self.settings = {
            "capture_data": True,
            "check_timing": True,
            "max_transactions": 1000
        }
    
    def add_transaction(self, transaction):
        self.transactions.append(transaction)

# Create an instance
monitor = APBMonitor("dut", logger)

# Fill with some test data
for i in range(5):
    monitor.add_transaction(f"Transaction {i}")
monitor.state = "ACTIVE"
monitor.stats["write_count"] = 3
monitor.stats["read_count"] = 2

# Inspect the monitor
print_object_details(monitor, logger, name="APBMonitor")
# Output in log:
# === APBMonitor Details ===
# Class: APBMonitor
# Total attributes: 6
# --------------------------------------------------------------------------------
# current_transaction: NoneType = None
# dut: str = dut
# log: Logger = <Logger ...>
# settings: dict = {'capture_data': True, 'check_timing': True, 'max_transactions': 1000}
# state: str = ACTIVE
# stats: dict = {'write_count': 3, 'read_count': 2, 'error_count': 0}
# transactions: list = ['Transaction 0', 'Transaction 1', 'Transaction 2', 'Transaction 3', 'Transaction 4']
# --------------------------------------------------------------------------------

# Print just the stats dictionary
print_dict_to_log("Monitor Stats", monitor.stats, logger, prefix="APBMonitor")
# Output in log:
# === Monitor Stats Details ===
# APBMonitor::write_count: 3
# APBMonitor::read_count: 2
# APBMonitor::error_count: 0
```

### Debugging Complex Verification Scenarios

```python
# Create a transaction class
class APBTransaction:
    def __init__(self, addr=0, data=0, direction="WRITE"):
        self.paddr = addr
        self.pwdata = data if direction == "WRITE" else 0
        self.prdata = data if direction == "READ" else 0
        self.direction = direction
        self.psel = 1
        self.penable = 1
        self.pwrite = 1 if direction == "WRITE" else 0
        self.pready = 1
        self.pslverr = 0
        self.start_time = 0
        self.end_time = 0

# Create a scoreboard class
class APBScoreboard:
    def __init__(self, log):
        self.log = log
        self.expected = []
        self.actual = []
        self.matches = 0
        self.mismatches = 0

    def add_expected(self, transaction):
        self.expected.append(transaction)

    def add_actual(self, transaction):
        self.actual.append(transaction)
        self._check_match(transaction)

    def _check_match(self, transaction):
        # Simple matching logic for demonstration
        if self.expected:
            expected = self.expected.pop(0)
            if (expected.paddr == transaction.paddr and
                expected.direction == transaction.direction):
                if expected.direction == "WRITE":
                    if expected.pwdata == transaction.pwdata:
                        self.matches += 1
                    else:
                        self.mismatches += 1
                else:  # READ
                    if expected.prdata == transaction.prdata:
                        self.matches += 1
                    else:
                        self.mismatches += 1
            else:
                self.mismatches += 1
        else:
            self.mismatches += 1

# Create transactions and scoreboard
scoreboard = APBScoreboard(logger)

# Add expected transactions
for i in range(5):
    tx = APBTransaction(addr=0x1000 + i*4, data=0xA000 + i, direction="WRITE")
    scoreboard.add_expected(tx)

# Add actual transactions (with one mismatch)
for i in range(5):
    data = 0xA000 + i
    if i == 2:  # Create a mismatch
        data = 0xFFFF
    tx = APBTransaction(addr=0x1000 + i*4, data=data, direction="WRITE")
    scoreboard.add_actual(tx)

# Debug the scoreboard
print_object_details(scoreboard, logger, name="APBScoreboard")
# Output in log:
# === APBScoreboard Details ===
# Class: APBScoreboard
# Total attributes: 5
# --------------------------------------------------------------------------------
# actual: list = [<APBTransaction object at 0x...>, ...]
# expected: list = []
# log: Logger = <Logger ...>
# matches: int = 4
# mismatches: int = 1
# --------------------------------------------------------------------------------

# Debug a specific transaction
tx = scoreboard.actual[2]  # The mismatched transaction
print_object_details(tx, logger, name="Mismatched Transaction")
# Output in log:
# === Mismatched Transaction Details ===
# Class: APBTransaction
# Total attributes: 11
# --------------------------------------------------------------------------------
# direction: str = WRITE
# end_time: int = 0
# paddr: int = 0x1008
# penable: int = 1
# pready: int = 1
# prdata: int = 0
# psel: int = 1
# pslverr: int = 0
# pwdata: int = 0xFFFF  # Note the incorrect data
# pwrite: int = 1
# start_time: int = 0
# --------------------------------------------------------------------------------
```

## Best Practices

### Selective Debugging

For large objects, filter attributes to focus on relevant information:

```python
# Custom filtering function
def filter_attributes(obj, prefix):
    """Return a filtered dictionary of attributes starting with prefix"""
    result = {}
    for attr_name in dir(obj):
        if attr_name.startswith(prefix) and not attr_name.startswith('_'):
            try:
                attr_value = getattr(obj, attr_name)
                if not callable(attr_value):
                    result[attr_name] = {
                        'type': type(attr_value).__name__,
                        'value': attr_value
                    }
            except Exception as e:
                result[attr_name] = {
                    'type': 'Error',
                    'value': f"Error accessing attribute: {str(e)}"
                }
    return result

# Use with large objects
axi_master = AXI4Master(dut, logger)
# Only examine the configuration attributes
config_attrs = filter_attributes(axi_master, "config_")
print_dict_to_log("AXI4Master Configuration", config_attrs, logger)
```

### Logging Levels

Use appropriate logging levels to control debug output:

```python
# Debug version with detailed information
if logger.isEnabledFor(logging.DEBUG):
    print_object_details(transaction, logger, name="New Transaction")

# Information version with summarized information
if logger.isEnabledFor(logging.INFO):
    logger.info(f"Transaction: addr=0x{transaction.paddr:X}, data=0x{transaction.pwdata:X}")
```

### Integration with Test Flow

Integrate debug utilities at key points in the test flow:

```python
class APBTest(TBBase):
    async def run_test(self):
        # Initialize test
        self.log.info("Initializing test")
        self.monitor = APBMonitor(self.dut, self.log)
        self.driver = APBDriver(self.dut, self.log)
        
        # Debug initial state
        print_object_details(self.monitor, self.log, name="Initial Monitor State")
        print_object_details(self.driver, self.log, name="Initial Driver State")
        
        # Run test
        self.log.info("Running test")
        await self.driver.send_transactions(10)
        
        # Debug after test
        print_object_details(self.monitor, self.log, name="Final Monitor State")
        
        # Analyze results
        self.log.info("Analyzing results")
        results = self.analyze_results()
        print_dict_to_log("Test Results", results, self.log)
```

### Performance Considerations

Be mindful of performance impact when debugging large objects:

```python
# Use max_value_length to truncate long values
print_object_details(large_object, logger, max_value_length=100)

# Skip large attributes when not needed
def get_filtered_object_details(obj, skip_attrs=None):
    """Get object details, skipping specified attributes"""
    skip_attrs = skip_attrs or []
    result = {}
    
    for attr_name in dir(obj):
        if attr_name.startswith('_') or attr_name in skip_attrs:
            continue
            
        try:
            attr_value = getattr(obj, attr_name)
            if not callable(attr_value):
                result[attr_name] = {
                    'type': type(attr_value).__name__,
                    'value': attr_value
                }
        except Exception as e:
            result[attr_name] = {
                'type': 'Error',
                'value': f"Error accessing attribute: {str(e)}"
            }
            
    return result

# Use with large objects
large_object_details = get_filtered_object_details(large_object, 
                                                 skip_attrs=['huge_data_array', 'transaction_history'])
print_dict_to_log("Large Object", large_object_details, logger)
```

## Integration with Test Framework

### Automatic State Dumping

```python
class TestCase(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.components = {}
        
    def register_component(self, name, component):
        """Register a component for automatic state dumping"""
        self.components[name] = component
        
    def dump_state(self, prefix=""):
        """Dump state of all registered components"""
        self.log.info(f"{prefix} Dumping test state")
        for name, component in self.components.items():
            print_object_details(component, self.log, name=f"{prefix}{name}")
    
    async def run_test(self):
        # Initialize test
        self.log.info("Initializing test")
        monitor = APBMonitor(self.dut, self.log)
        driver = APBDriver(self.dut, self.log)
        scoreboard = APBScoreboard(self.log)
        
        self.register_component("Monitor", monitor)
        self.register_component("Driver", driver)
        self.register_component("Scoreboard", scoreboard)
        
        # Dump initial state
        self.dump_state("Initial ")
        
        # Run test
        self.log.info("Running test")
        await driver.send_transactions(10)
        
        # Dump final state
        self.dump_state("Final ")
```

### Error Handling Enhancement

```python
def enhanced_print_object_details(obj, log, name="Object", error_only=False):
    """
    Print object details, optionally focusing only on error values
    
    Args:
        obj: Object to inspect
        log: Logger to use
        name: Name to identify the object
        error_only: If True, only print attributes containing 'error', 'fail', etc.
    """
    details = get_object_details(obj)
    
    # Filter for error-related attributes if requested
    if error_only:
        error_terms = ['error', 'fail', 'mismatch', 'invalid', 'exception']
        filtered_details = {}
        
        for attr_name, attr_info in details.items():
            # Check attribute name
            if any(term in attr_name.lower() for term in error_terms):
                filtered_details[attr_name] = attr_info
                continue
                
            # Check attribute value for error indicators
            value = str(attr_info['value']).lower()
            if any(term in value for term in error_terms):
                filtered_details[attr_name] = attr_info
                continue
                
            # For numeric values, check if non-zero error counts
            if attr_name.lower().endswith(('_errors', '_error_count')) and attr_info['value'] != 0:
                filtered_details[attr_name] = attr_info
                
        details = filtered_details
    
    # Format header based on error status
    header = f"=== {name} Error Details ===" if error_only else f"=== {name} Details ==="
    log.debug(header)
    
    if not details:
        log.debug("No error information found" if error_only else "No attributes found")
        return
        
    log.debug(f"Total attributes: {len(details)}")
    log.debug("-" * 80)
    
    # Print attributes
    for attr_name, info in sorted(details.items()):
        log.debug(f"{attr_name}: {info['type']} = {info['value']}")
        
    log.debug("-" * 80)
    
# Usage
def check_for_errors(component, logger):
    """Check component for errors and log details if found"""
    # Check basic error condition
    if hasattr(component, 'error_count') and component.error_count > 0:
        logger.error(f"{component.__class__.__name__} has {component.error_count} errors")
        # Print error details
        enhanced_print_object_details(component, logger, 
                                     name=component.__class__.__name__, 
                                     error_only=True)
        return True
    return False
```
