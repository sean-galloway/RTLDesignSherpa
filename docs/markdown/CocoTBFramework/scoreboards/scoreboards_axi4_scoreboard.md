# axi4_scoreboard.py

AXI4 protocol scoreboard implementation for verifying AXI4 transactions with ID-based tracking, channel separation, and protocol compliance checking. This module provides comprehensive verification for complex AXI4 systems with multiple outstanding transactions.

## Overview

The AXI4 scoreboard system provides:
- **ID-based Transaction Tracking**: Separate transaction queues per AXI4 ID
- **Channel Separation**: Independent handling of read and write channels
- **Master/Slave Monitoring**: Dual-side transaction verification
- **Protocol Compliance**: Built-in AXI4 protocol violation detection
- **Performance Analysis**: Transaction timing and throughput metrics

## Classes

### AXI4Scoreboard

Advanced AXI4 transaction verification with full protocol support.

```python
class AXI4Scoreboard(BaseScoreboard):
    def __init__(self, name, id_width=8, addr_width=32, data_width=32, user_width=1, log=None)
```

**Parameters:**
- `name`: Scoreboard name for identification
- `id_width`: Width of ID fields in bits (default: 8)
- `addr_width`: Width of address fields in bits (default: 32)
- `data_width`: Width of data fields in bits (default: 32)
- `user_width`: Width of user fields in bits (default: 1)
- `log`: Logger instance for detailed reporting

**Key Attributes:**
- `write_count`: Number of write transactions processed
- `read_count`: Number of read transactions processed
- `protocol_error_count`: Number of protocol violations detected
- `master_writes`: Dictionary mapping IDs to master-side write transactions
- `slave_writes`: Dictionary mapping IDs to slave-side write transactions
- `master_reads`: Dictionary mapping IDs to master-side read transactions
- `slave_reads`: Dictionary mapping IDs to slave-side read transactions

## Monitor Integration

### Master Monitor Connection

#### `add_master_monitor(monitor)`
Connect master-side AXI4 monitor to scoreboard.

**Parameters:**
- `monitor`: AXI4 monitor instance observing master interface

**Behavior:**
- Registers write callback: `_handle_master_write`
- Registers read callback: `_handle_master_read`
- Enables automatic transaction capture from master side

```python
# Connect master monitor
axi4_scoreboard.add_master_monitor(master_monitor)

# Monitor automatically feeds transactions to scoreboard
```

### Slave Monitor Connection

#### `add_slave_monitor(monitor)`
Connect slave-side AXI4 monitor to scoreboard.

**Parameters:**
- `monitor`: AXI4 monitor instance observing slave interface

**Behavior:**
- Registers write callback: `_handle_slave_write`
- Registers read callback: `_handle_slave_read`
- Enables automatic transaction capture from slave side

```python
# Connect slave monitor
axi4_scoreboard.add_slave_monitor(slave_monitor)

# Complete master-slave verification setup
```

## Transaction Processing

### Write Transaction Handling

#### `_handle_master_write(id_value, transaction)`
Process completed write transaction from master side.

**Parameters:**
- `id_value`: AXI4 ID of the transaction
- `transaction`: Completed write transaction

**Behavior:**
- Stores transaction in `master_writes[id_value]`
- Checks for matching slave-side transaction
- Triggers comparison if both sides available
- Updates write transaction counters

#### `_handle_slave_write(id_value, transaction)`
Process completed write transaction from slave side.

**Parameters:**
- `id_value`: AXI4 ID of the transaction
- `transaction`: Completed write transaction

**Behavior:**
- Stores transaction in `slave_writes[id_value]`
- Checks for matching master-side transaction
- Triggers comparison if both sides available
- Validates write response compliance

### Read Transaction Handling

#### `_handle_master_read(id_value, transaction)`
Process completed read transaction from master side.

**Parameters:**
- `id_value`: AXI4 ID of the transaction
- `transaction`: Completed read transaction

**Behavior:**
- Stores transaction in `master_reads[id_value]`
- Checks for matching slave-side transaction
- Triggers comparison if both sides available
- Updates read transaction counters

#### `_handle_slave_read(id_value, transaction)`
Process completed read transaction from slave side.

**Parameters:**
- `id_value`: AXI4 ID of the transaction
- `transaction`: Completed read transaction

**Behavior:**
- Stores transaction in `slave_reads[id_value]`
- Checks for matching master-side transaction
- Triggers comparison if both sides available
- Validates read data and response codes

## Transaction Verification

### Write Transaction Matching

#### `_check_write_match(id_value, master_transaction, slave_transaction)`
Compare master and slave write transactions for specific ID.

**Parameters:**
- `id_value`: Transaction ID
- `master_transaction`: Master-side write transaction
- `slave_transaction`: Slave-side write transaction

**Verification Checks:**
- Address field consistency
- Data payload matching
- Write strobe validation
- Burst parameters compliance
- Response code verification

```python
# Example write verification
# Master: AWADDR=0x1000, WDATA=[0xDEADBEEF, 0x12345678], WSTRB=[0xF, 0xF]
# Slave:  AWADDR=0x1000, WDATA=[0xDEADBEEF, 0x12345678], BRESP=OKAY
# Result: MATCH - addresses align, data matches, response is OKAY
```

### Read Transaction Matching

#### `_check_read_match(id_value, master_transaction, slave_transaction)`
Compare master and slave read transactions for specific ID.

**Parameters:**
- `id_value`: Transaction ID
- `master_transaction`: Master-side read transaction
- `slave_transaction`: Slave-side read transaction

**Verification Checks:**
- Address field consistency
- Burst length matching
- Read data validation
- Response code checking
- Timing constraint compliance

```python
# Example read verification
# Master: ARADDR=0x2000, ARLEN=3, ARID=5
# Slave:  ARADDR=0x2000, RDATA=[0x11, 0x22, 0x33, 0x44], RID=5, RRESP=OKAY
# Result: MATCH - address correct, data length matches, ID preserved
```

## Protocol Compliance Checking

### Built-in Validation

The AXI4 scoreboard automatically checks for:
- **ID Consistency**: Transaction IDs match between request and response
- **Burst Alignment**: Address alignment matches burst size requirements
- **Response Codes**: Valid RESP field values (OKAY, EXOKAY, SLVERR, DECERR)
- **Outstanding Limits**: Configurable limits on outstanding transactions per ID
- **Ordering Requirements**: AXI4 ordering model compliance

### Protocol Error Detection

```python
# Protocol errors automatically logged:
# - Mismatched transaction IDs
# - Invalid burst parameters
# - Out-of-order responses
# - Response timeout violations
# - Invalid response codes

if axi4_scoreboard.protocol_error_count > 0:
    print(f"Protocol violations detected: {axi4_scoreboard.protocol_error_count}")
```

## Performance Analysis

### Transaction Statistics

The scoreboard automatically tracks:
- **Transaction Counts**: Read and write transaction totals
- **ID Utilization**: Distribution of transactions across ID space
- **Channel Efficiency**: Bandwidth utilization analysis
- **Latency Metrics**: Average response times per transaction type

### Performance Reporting

```python
# Access performance statistics
stats = {
    'total_transactions': axi4_scoreboard.transaction_count,
    'write_transactions': axi4_scoreboard.write_count,
    'read_transactions': axi4_scoreboard.read_count,
    'protocol_errors': axi4_scoreboard.protocol_error_count,
    'id_utilization': len(axi4_scoreboard.master_writes) + len(axi4_scoreboard.master_reads)
}

print(f"AXI4 Performance: {stats['total_transactions']} transactions")
print(f"Read/Write Ratio: {stats['read_transactions']}/{stats['write_transactions']}")
print(f"Protocol Compliance: {stats['protocol_errors']} violations")
```

## Usage Examples

### Basic AXI4 Verification Setup

```python
from CocoTBFramework.scoreboards.axi4_scoreboard import AXI4Scoreboard
from CocoTBFramework.components.axi4.axi4_monitor import AXI4Monitor

# Create scoreboard for 64-bit AXI4 with 4-bit IDs
scoreboard = AXI4Scoreboard(
    name="AXI4_Memory",
    id_width=4,
    addr_width=64,
    data_width=64,
    user_width=4,
    log=logger
)

# Create and connect monitors
master_monitor = AXI4Monitor(dut.master_axi, "Master", clock)
slave_monitor = AXI4Monitor(dut.slave_axi, "Slave", clock)

scoreboard.add_master_monitor(master_monitor)
scoreboard.add_slave_monitor(slave_monitor)

# Scoreboard automatically captures and verifies transactions
await Timer(1000, units='ns')  # Run test

# Generate verification report
error_count = scoreboard.report()
success_rate = scoreboard.result()
print(f"AXI4 Verification: {'PASS' if error_count == 0 else 'FAIL'} ({success_rate:.2%})")
```

### Advanced Multi-ID Verification

```python
# Test with multiple outstanding transactions
async def test_multi_id_axi4():
    # Configure for high-performance testing
    scoreboard = AXI4Scoreboard(
        name="HighPerf_AXI4",
        id_width=8,  # 256 possible IDs
        addr_width=32,
        data_width=128,  # Wide data bus
        log=logger
    )
    
    # Connect monitors
    scoreboard.add_master_monitor(master_monitor)
    scoreboard.add_slave_monitor(slave_monitor)
    
    # Generate transactions with different IDs
    master = AXI4Master(dut.master_axi, clock)
    
    # Launch multiple concurrent transactions
    for i in range(16):
        write_transaction = master.create_write_transaction(
            addr=0x10000 + (i * 0x1000),
            data=[0xDEADBEEF + i],
            id=i,
            burst_len=4
        )
        await master.send_write(write_transaction)
    
    # Wait for completion and verify
    await Timer(5000, units='ns')
    
    # Analyze results by ID
    print(f"Write transactions: {scoreboard.write_count}")
    print(f"Active IDs: {len(scoreboard.master_writes)}")
    print(f"Protocol errors: {scoreboard.protocol_error_count}")
```

### Memory System Verification

```python
# Verify AXI4 memory controller
async def test_memory_controller():
    scoreboard = AXI4Scoreboard("MemCtrl", log=logger)
    
    # Connect to memory controller interfaces
    cpu_monitor = AXI4Monitor(dut.cpu_axi, "CPU", clock)
    ddr_monitor = AXI4Monitor(dut.ddr_axi, "DDR", clock)
    
    scoreboard.add_master_monitor(cpu_monitor)
    scoreboard.add_slave_monitor(ddr_monitor)
    
    # Generate realistic memory access patterns
    cpu_master = AXI4Master(dut.cpu_axi, clock)
    
    # Test different access patterns
    patterns = [
        # Sequential reads
        [(0x0000 + i*8, 'READ') for i in range(64)],
        # Random writes  
        [(random.randint(0x1000, 0x2000) & ~7, 'WRITE') for _ in range(32)],
        # Burst transfers
        [(0x3000 + i*64, 'BURST_READ', 8) for i in range(8)]
    ]
    
    for pattern in patterns:
        for access in pattern:
            if access[1] == 'READ':
                await cpu_master.read(access[0], id=random.randint(0, 15))
            elif access[1] == 'WRITE':
                await cpu_master.write(access[0], random.randint(0, 0xFFFFFFFF), id=random.randint(0, 15))
            elif access[1] == 'BURST_READ':
                await cpu_master.burst_read(access[0], access[2], id=random.randint(0, 15))
        
        # Check intermediate results
        if scoreboard.protocol_error_count > 0:
            print(f"Protocol errors after pattern: {scoreboard.protocol_error_count}")
            break
    
    # Final verification
    final_errors = scoreboard.report()
    print(f"Memory controller verification: {final_errors} errors")
```

### Cross-Clock Domain Verification

```python
# Verify AXI4 clock domain crossing
async def test_clock_domain_crossing():
    # Separate scoreboards for each clock domain
    fast_scoreboard = AXI4Scoreboard("FastDomain", log=logger)
    slow_scoreboard = AXI4Scoreboard("SlowDomain", log=logger)
    
    # Connect monitors on both sides of CDC
    fast_monitor = AXI4Monitor(dut.fast_axi, "Fast", fast_clock)
    slow_monitor = AXI4Monitor(dut.slow_axi, "Slow", slow_clock)
    
    fast_scoreboard.add_master_monitor(fast_monitor)
    slow_scoreboard.add_slave_monitor(slow_monitor)
    
    # Create cross-domain transaction tracker
    class CDCTracker:
        def __init__(self):
            self.fast_transactions = {}
            self.slow_transactions = {}
        
        def on_fast_transaction(self, id_val, transaction):
            self.fast_transactions[id_val] = transaction
            self.check_matching()
        
        def on_slow_transaction(self, id_val, transaction):
            self.slow_transactions[id_val] = transaction
            self.check_matching()
        
        def check_matching(self):
            # Verify transactions cross domains correctly
            for id_val in self.fast_transactions:
                if id_val in self.slow_transactions:
                    fast_tx = self.fast_transactions[id_val]
                    slow_tx = self.slow_transactions[id_val]
                    # Compare transactions accounting for CDC latency
                    if not self.compare_cdc_transactions(fast_tx, slow_tx):
                        print(f"CDC mismatch for ID {id_val}")
    
    tracker = CDCTracker()
    
    # Connect tracker to monitors
    fast_monitor.add_callback(tracker.on_fast_transaction)
    slow_monitor.add_callback(tracker.on_slow_transaction)
    
    # Run test with clock domain crossing
    await Timer(10000, units='ns')
```

## Best Practices

### Monitor Configuration
- Connect both master and slave monitors for complete verification
- Use appropriate ID width for system requirements
- Configure timeout values for protocol compliance checking

### Performance Optimization
- Clear completed transactions periodically in long tests
- Monitor memory usage with high transaction volumes
- Use ID-based filtering for targeted verification

### Error Analysis
- Enable detailed logging for protocol violation analysis
- Use transaction timestamps for timing analysis
- Preserve failed transaction pairs for debugging

### Integration Guidelines
- Connect monitors before starting transaction generation
- Use scoreboard statistics for test coverage analysis
- Implement custom callbacks for specialized verification

## Integration Points

### Test Environment Integration
```python
# Integration with test sequence
class AXI4TestEnvironment:
    def __init__(self, dut, clock):
        self.scoreboard = AXI4Scoreboard("TestEnv", log=logger)
        self.master_monitor = AXI4Monitor(dut.master, "Master", clock)
        self.slave_monitor = AXI4Monitor(dut.slave, "Slave", clock)
        
        self.scoreboard.add_master_monitor(self.master_monitor)
        self.scoreboard.add_slave_monitor(self.slave_monitor)
    
    def run_verification(self):
        return self.scoreboard.report()
```

### Coverage Integration
```python
# Functional coverage with scoreboard
def calculate_id_coverage():
    used_ids = set(scoreboard.master_writes.keys()) | set(scoreboard.master_reads.keys())
    total_ids = 2 ** scoreboard.id_width
    coverage = len(used_ids) / total_ids * 100
    print(f"ID Coverage: {coverage:.1f}% ({len(used_ids)}/{total_ids})")
```

The AXI4 scoreboard provides comprehensive verification for complex AXI4 systems with robust protocol compliance checking, performance analysis, and multi-ID transaction tracking capabilities.