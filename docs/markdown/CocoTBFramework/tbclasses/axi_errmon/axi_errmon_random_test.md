# AXI Error Monitor Random Test

## Overview

The `AXIErrorMonRandomTest` class implements randomized traffic tests for the AXI Error Monitor. It generates varied transaction patterns with controlled randomization to stress test the error detection functionality. This class inherits from the base test class and provides comprehensive testing with randomized parameters.

## Class Definition

```python
class AXIErrorMonRandomTest(AXIErrorMonBaseTest):
    """
    Random traffic tests for AXI Error Monitor.
    Tests behavior under randomized traffic patterns.
    """

    def __init__(self, tb):
        """
        Initialize with a reference to the testbench
        
        Args:
            tb: Reference to the AXIErrorMonitorTB wrapper class
        """
        super().__init__(tb)
        
        # Initialize random seed
        self.seed = int(cocotb.utils.get_sim_time('ns')) & 0xFFFFFFFF
        random.seed(self.seed)
        
        # Transaction statistics
        self.transaction_count = 0
        self.error_transaction_count = 0
        self.normal_transaction_count = 0
```

## Key Features

- Randomized transaction parameters
- Controlled mix of normal and error transactions
- Configurable number of transactions
- Transaction statistics tracking
- Random burst testing
- Simulation seed for reproducibility

## Primary Methods

### run

Runs random traffic test with specified number of transactions.

```python
async def run(self, num_transactions=20):
    """
    Run random traffic test
    
    Args:
        num_transactions: Number of transactions to generate
        
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Reset statistics
    self.transaction_count = 0
    self.error_transaction_count = 0
    self.normal_transaction_count = 0
    self.tb.errors_detected = []
    
    # Generate a random sequence of transactions
    initial_error_count = 0
    test_passed = await self.generate_random_traffic(num_transactions)
    final_error_count = len(self.tb.errors_detected)
    
    # Report statistics
    self.log.info(f"Random traffic test statistics:")
    self.log.info(f"  Total transactions: {self.transaction_count}")
    self.log.info(f"  Normal transactions: {self.normal_transaction_count}")
    self.log.info(f"  Error transactions: {self.error_transaction_count}")
    self.log.info(f"  Errors detected: {final_error_count - initial_error_count}")
    
    return test_passed
```

### generate_random_traffic

Generates random traffic pattern with a mix of normal and response error transactions.

```python
async def generate_random_traffic(self, num_transactions):
    """
    Generate random traffic pattern focusing only on response errors
    
    Updated for write mode to account for the single shared FIFO.
    
    Args:
        num_transactions: Number of transactions to generate
        
    Returns:
        True if test passed, False otherwise
    """
    # Transaction types
    NORMAL = 0
    RESP_ERROR = 1
    
    # Define the probability of each transaction type
    transaction_probabilities = [
        (NORMAL, 0.7),            # 70% normal transactions
        (RESP_ERROR, 0.3)         # 30% response errors
    ]
    
    # Create weights for random choices
    transaction_types = [t[0] for t in transaction_probabilities]
    weights = [t[1] for t in transaction_probabilities]
    
    # Implementation differs between read and write modes
    # ...
```

### test_random_burst

Tests random burst of transactions.

```python
async def test_random_burst(self):
    """
    Test random burst of transactions
    
    This test generates a burst of transactions with random IDs and
    addresses to simulate heavy traffic.
    
    Returns:
        True if test passed, False otherwise
    """
    # Number of transactions in the burst
    burst_size = 20
    
    # Generate random IDs and addresses
    ids = [random.randrange(0, self.tb.channels) for _ in range(burst_size)]
    addresses = [random.randrange(0, 0xF000, 0x100) for _ in range(burst_size)]
    
    # Launch all transactions concurrently
    tasks = []
    
    for i in range(burst_size):
        task = cocotb.start_soon(self.drive_basic_transaction(
            addr=addresses[i],
            id_value=ids[i],
            data_value=random.randrange(0, 0xFFFFFFFF),
            resp_value=0,  # All OKAY
            control_ready=False,  # Default ready behavior
            pipeline_phases=True,  # Enable pipelining for write mode
            wait_for_completion=False
        ))
        tasks.append(task)
        
        # Small delay between launches
        await self.tb.wait_clocks('aclk', 1)
        
    # Wait for tasks to complete and check results
    # ...
```

## Random Transaction Generation

### Transaction Types

The test generates a mix of transaction types with controlled probabilities:

```python
transaction_probabilities = [
    (NORMAL, 0.7),            # 70% normal transactions
    (RESP_ERROR, 0.3)         # 30% response errors
]
```

### Randomized Parameters

For each transaction, the following parameters are randomized:
- **Channel/ID**: Random channel selection (within available channels)
- **Address**: Random address values
- **Data**: Random data values
- **Response**: Appropriate response values (OKAY for normal, SLVERR/DECERR for errors)

## Read vs. Write Mode Implementation

### Read Mode
- Simple sequential transaction generation
- Each transaction processed to completion before starting the next
- Statistics tracked for verification

### Write Mode
- Transactions managed in active/completed lists
- Limited active transactions to avoid shared FIFO overflow
- Dynamic management of transaction lifecycle
- Parallel processing where possible

## Implementation Notes

- Random seed is based on simulation time for reproducibility
- Transaction statistics are tracked for verification
- Normal transactions use OKAY (0) response
- Error transactions use SLVERR (2) or DECERR (3) response
- Transactions use different addresses to avoid interference
- Read and write modes use different implementation approaches
- Error verification checks that all expected errors are detected

## Example Usage

```python
# Create AXI Error Monitor testbench
tb = AXIErrorMonitorTB(dut, ...)

# Create random test class
random_test = AXIErrorMonRandomTest(tb)

# Run random test with 50 transactions
passed = await random_test.run(num_transactions=50)

# Test random burst
burst_passed = await random_test.test_random_burst()

# Check statistics
print(f"Total: {random_test.transaction_count}")
print(f"Normal: {random_test.normal_transaction_count}")
print(f"Error: {random_test.error_transaction_count}")
```

## See Also

- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test utilities
- [AXI Error Monitor Error Test](axi_errmon_error_test.md) - Error scenario tests

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
