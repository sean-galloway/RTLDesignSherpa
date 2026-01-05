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

# apb_gaxi_scoreboard.py

APB-GAXI bridge scoreboard implementation for verifying protocol conversion between APB and GAXI protocols. This module provides specialized verification for APB-GAXI bridge systems with comprehensive transaction matching and response validation.

## Overview

The APB-GAXI scoreboard system provides:
- **Three-Phase Transaction Matching**: APB transaction → GAXI command → GAXI response
- **Protocol-Aware Verification**: Understands both APB and GAXI protocol semantics
- **Response Handling**: Proper matching of both read and write responses
- **Enhanced Error Classification**: Detailed error categorization and field-level analysis
- **Timeout-Based Matching**: Robust verification with configurable timeouts

## Classes

### APBGAXIScoreboard

Comprehensive APB-GAXI bridge verification with three-queue transaction matching.

```python
class APBGAXIScoreboard:
    def __init__(self, name, log=None)
```

**Parameters:**
- `name`: Scoreboard name for identification
- `log`: Logger instance for detailed reporting

**Key Features:**
- Separate transaction queues for APB, GAXI commands, and GAXI responses
- Automatic timeout-based transaction matching
- Comprehensive statistics tracking
- Enhanced error reporting with field extraction

**Transaction Queues:**
- `apb_queue`: APB transactions from master/slave interface
- `gaxi_cmd_queue`: GAXI command transactions
- `gaxi_rsp_queue`: GAXI response transactions

## Core Methods

### Transaction Management

#### `add_apb_transaction(transaction)`
Add APB transaction to the scoreboard for verification.

**Parameters:**
- `transaction`: APB transaction to be matched

**Behavior:**
- Extracts APB transaction fields using `APBTransactionExtractor`
- Stores transaction with timestamp for timeout management
- Increments APB transaction counter
- Triggers automatic matching attempt

```python
# Add APB transaction
apb_transaction = create_apb_write(addr=0x1000, data=0xDEADBEEF)
scoreboard.add_apb_transaction(apb_transaction)
```

#### `add_gaxi_command(transaction)`
Add GAXI command transaction for bridge verification.

**Parameters:**
- `transaction`: GAXI command transaction

**Behavior:**
- Extracts command fields (address, data, operation type)
- Stores in GAXI command queue with timestamp
- Updates command transaction statistics
- Attempts transaction matching

```python
# Add GAXI command
gaxi_command = create_gaxi_command(addr=0x1000, data=0xDEADBEEF, cmd=1)
scoreboard.add_gaxi_command(gaxi_command)
```

#### `add_gaxi_response(transaction)`
Add GAXI response transaction for completion verification.

**Parameters:**
- `transaction`: GAXI response transaction

**Behavior:**
- Extracts response fields (data, status, error indicators)
- Stores in GAXI response queue with timestamp
- Tracks error transactions based on response status
- Triggers comprehensive matching

```python
# Add GAXI response
gaxi_response = create_gaxi_response(data=0xDEADBEEF, status='OKAY')
scoreboard.add_gaxi_response(gaxi_response)
```

### Transaction Matching

#### `_match_transactions()`
Core matching algorithm for three-phase transaction verification.

**Matching Logic:**
1. **APB-GAXI Command Matching**: Matches APB transactions with corresponding GAXI commands based on address and operation type
2. **Command-Response Pairing**: Links GAXI commands with their responses using transaction identifiers
3. **End-to-End Verification**: Ensures complete APB→GAXI→Response flow integrity

**Timeout Handling:**
- Configurable timeout (`match_timeout_ns`) for transaction completion
- Automatic cleanup of expired transactions
- Timeout error reporting and statistics

```python
# Configure timeout (default: 10μs)
scoreboard.match_timeout_ns = 50000  # 50μs timeout
```

### Field Extraction and Formatting

The scoreboard uses `APBTransactionExtractor` for robust field extraction:

#### APB Transaction Fields
- **Command Fields**: Address, data, write enable, strobe
- **Response Fields**: Read data, error status, completion status
- **Timing Fields**: Start time, end time, duration

#### GAXI Transaction Fields
- **Command Fields**: Address, data, command type, strobe
- **Response Fields**: Response data, status codes, error indicators

```python
# Example field extraction
apb_fields = APBTransactionExtractor.extract_command_fields(apb_transaction)
# Returns: {'addr': 0x1000, 'data': 0xDEADBEEF, 'is_write': True, 'strb': 0xF}

gaxi_fields = APBTransactionExtractor.extract_response_fields(gaxi_response)
# Returns: {'data': 0xDEADBEEF, 'has_error': False, 'status': 'OKAY'}
```

## Statistics and Reporting

### Comprehensive Statistics Tracking

The scoreboard maintains detailed statistics:

```python
stats = {
    'apb_transactions': 0,           # Total APB transactions
    'gaxi_cmd_transactions': 0,      # Total GAXI commands
    'gaxi_rsp_transactions': 0,      # Total GAXI responses
    'matched_pairs': 0,              # Successfully matched complete flows
    'matched_write_responses': 0,    # Matched write responses
    'matched_read_responses': 0,     # Matched read responses
    'unmatched_apb': 0,              # Unmatched APB transactions
    'unmatched_gaxi_cmd': 0,         # Unmatched GAXI commands
    'unmatched_gaxi_rsp': 0,         # Unmatched GAXI responses
    'error_transactions': 0,         # Transactions with errors
    'field_extraction_errors': 0,   # Field extraction failures
    'transaction_type_errors': 0     # Invalid transaction types
}
```

### Reporting Methods

#### `report()`
Generate comprehensive scoreboard report.

**Returns:**
- `str`: Detailed report with all statistics and analysis

**Report Contents:**
- Transaction counts for all three phases
- Match success rates for reads and writes
- Error analysis and unmatched transaction counts
- Field extraction and type error statistics

```python
print(scoreboard.report())
# Output:
# === APB-GAXI Scoreboard Report (BridgeTest) ===
# APB Transactions: 150
# GAXI Commands: 148
# GAXI Responses: 147
# Matched Pairs: 145
#   - Write Responses: 85
#   - Read Responses: 60
# Error Transactions: 2
# Unmatched APB: 5
# Unmatched GAXI CMD: 3
# Unmatched GAXI RSP: 2
```

#### `get_stats()`
Get detailed statistics dictionary for programmatic analysis.

**Returns:**
- `dict`: Complete statistics dictionary

```python
stats = scoreboard.get_stats()
success_rate = stats['matched_pairs'] / stats['apb_transactions'] * 100
print(f"Bridge success rate: {success_rate:.2f}%")
```

### Utility Methods

#### `clear()`
Reset scoreboard state for new test phase.

**Behavior:**
- Clears all transaction queues
- Resets all statistics counters
- Preserves configuration settings

```python
# Reset between test phases
scoreboard.clear()
```

## Usage Examples

### Basic APB-GAXI Bridge Verification

```python
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket

# Create bridge scoreboard
scoreboard = APBGAXIScoreboard("APB_GAXI_Bridge", log=logger)

# Configure timeout for bridge latency
scoreboard.match_timeout_ns = 1000  # 1μs timeout

# Test write transaction flow
apb_write = APBPacket()
apb_write.direction = 'WRITE'
apb_write.paddr = 0x2000
apb_write.pwdata = 0x12345678
apb_write.pstrb = 0xF

gaxi_cmd = GAXIPacket(field_config)
gaxi_cmd.fields['addr'] = 0x2000
gaxi_cmd.fields['data'] = 0x12345678
gaxi_cmd.fields['cmd'] = 1  # Write
gaxi_cmd.fields['strb'] = 0xF

gaxi_rsp = GAXIPacket(field_config)
gaxi_rsp.fields['data'] = 0x0  # Write response (no data)
gaxi_rsp.fields['status'] = 0  # OKAY

# Add transactions in sequence
scoreboard.add_apb_transaction(apb_write)
scoreboard.add_gaxi_command(gaxi_cmd)
scoreboard.add_gaxi_response(gaxi_rsp)

# Verify bridge operation
report = scoreboard.report()
print(report)

# Check success rate
stats = scoreboard.get_stats()
if stats['matched_pairs'] == stats['apb_transactions']:
    print("Bridge verification: PASS")
else:
    print(f"Bridge verification: FAIL ({stats['matched_pairs']}/{stats['apb_transactions']} matched)")
```

### Read Transaction Verification

```python
# Test read transaction flow
async def test_bridge_read_flow():
    scoreboard = APBGAXIScoreboard("Read_Bridge", log=logger)
    
    # APB read request
    apb_read = APBPacket()
    apb_read.direction = 'READ'
    apb_read.paddr = 0x3000
    apb_read.prdata = 0xABCDEF00  # Expected read data
    
    # Corresponding GAXI command
    gaxi_cmd = GAXIPacket(field_config)
    gaxi_cmd.fields['addr'] = 0x3000
    gaxi_cmd.fields['cmd'] = 0  # Read
    
    # GAXI response with read data
    gaxi_rsp = GAXIPacket(field_config)
    gaxi_rsp.fields['data'] = 0xABCDEF00
    gaxi_rsp.fields['status'] = 0  # OKAY
    
    # Simulate bridge operation timing
    scoreboard.add_apb_transaction(apb_read)
    await Timer(100, units='ns')  # Bridge processing delay
    
    scoreboard.add_gaxi_command(gaxi_cmd)
    await Timer(50, units='ns')   # Memory access delay
    
    scoreboard.add_gaxi_response(gaxi_rsp)
    
    # Verify read flow
    stats = scoreboard.get_stats()
    assert stats['matched_read_responses'] == 1, "Read response not matched"
    assert stats['error_transactions'] == 0, "Unexpected errors detected"
    
    print("Read bridge verification: PASS")
```

### High-Throughput Bridge Testing

```python
# Test bridge with multiple concurrent transactions
async def test_high_throughput_bridge():
    scoreboard = APBGAXIScoreboard("HighThroughput", log=logger)
    scoreboard.match_timeout_ns = 10000  # 10μs for high throughput
    
    # Generate transaction patterns
    num_transactions = 100
    transaction_pairs = []
    
    for i in range(num_transactions):
        # Alternating read/write pattern
        is_write = (i % 2 == 0)
        addr = 0x10000 + (i * 4)
        data = 0xDEAD0000 + i
        
        # APB transaction
        apb_tx = APBPacket()
        apb_tx.direction = 'WRITE' if is_write else 'READ'
        apb_tx.paddr = addr
        if is_write:
            apb_tx.pwdata = data
            apb_tx.pstrb = 0xF
        else:
            apb_tx.prdata = data
        
        # GAXI command
        gaxi_cmd = GAXIPacket(field_config)
        gaxi_cmd.fields['addr'] = addr
        gaxi_cmd.fields['cmd'] = 1 if is_write else 0
        if is_write:
            gaxi_cmd.fields['data'] = data
            gaxi_cmd.fields['strb'] = 0xF
        
        # GAXI response
        gaxi_rsp = GAXIPacket(field_config)
        gaxi_rsp.fields['data'] = data if not is_write else 0
        gaxi_rsp.fields['status'] = 0  # OKAY
        
        transaction_pairs.append((apb_tx, gaxi_cmd, gaxi_rsp))
    
    # Simulate concurrent bridge operation
    for apb_tx, gaxi_cmd, gaxi_rsp in transaction_pairs:
        scoreboard.add_apb_transaction(apb_tx)
        
        # Small delay for bridge processing
        await Timer(10, units='ns')
        scoreboard.add_gaxi_command(gaxi_cmd)
        
        # Memory response delay
        await Timer(5, units='ns')
        scoreboard.add_gaxi_response(gaxi_rsp)
    
    # Wait for all matching to complete
    await Timer(1000, units='ns')
    
    # Analyze results
    stats = scoreboard.get_stats()
    print(f"High-throughput test results:")
    print(f"  APB transactions: {stats['apb_transactions']}")
    print(f"  Matched pairs: {stats['matched_pairs']}")
    print(f"  Success rate: {stats['matched_pairs']/stats['apb_transactions']*100:.1f}%")
    print(f"  Write responses: {stats['matched_write_responses']}")
    print(f"  Read responses: {stats['matched_read_responses']}")
    
    # Verify performance
    assert stats['matched_pairs'] >= num_transactions * 0.95, "Insufficient match rate"
    assert stats['error_transactions'] == 0, "Unexpected error transactions"
    
    print("High-throughput bridge verification: PASS")
```

### Error Injection and Recovery Testing

```python
# Test bridge error handling
async def test_bridge_error_handling():
    scoreboard = APBGAXIScoreboard("ErrorTest", log=logger)
    
    # Normal transaction
    normal_apb = create_apb_write(addr=0x1000, data=0x11111111)
    normal_cmd = create_gaxi_command(addr=0x1000, data=0x11111111, cmd=1)
    normal_rsp = create_gaxi_response(status='OKAY')
    
    # Error transaction
    error_apb = create_apb_write(addr=0x2000, data=0x22222222)
    error_cmd = create_gaxi_command(addr=0x2000, data=0x22222222, cmd=1)
    error_rsp = create_gaxi_response(status='SLVERR')  # Slave error
    
    # Timeout transaction (no response)
    timeout_apb = create_apb_write(addr=0x3000, data=0x33333333)
    timeout_cmd = create_gaxi_command(addr=0x3000, data=0x33333333, cmd=1)
    # No response - will timeout
    
    # Add transactions
    scoreboard.add_apb_transaction(normal_apb)
    scoreboard.add_gaxi_command(normal_cmd)
    scoreboard.add_gaxi_response(normal_rsp)
    
    scoreboard.add_apb_transaction(error_apb)
    scoreboard.add_gaxi_command(error_cmd)
    scoreboard.add_gaxi_response(error_rsp)
    
    scoreboard.add_apb_transaction(timeout_apb)
    scoreboard.add_gaxi_command(timeout_cmd)
    # No response added
    
    # Wait for timeout
    await Timer(scoreboard.match_timeout_ns + 1000, units='ns')
    
    # Analyze error handling
    stats = scoreboard.get_stats()
    print("Error handling test results:")
    print(f"  Total APB transactions: {stats['apb_transactions']}")
    print(f"  Matched pairs: {stats['matched_pairs']}")
    print(f"  Error transactions: {stats['error_transactions']}")
    print(f"  Unmatched responses: {stats['unmatched_gaxi_rsp']}")
    
    # Verify error detection
    assert stats['error_transactions'] >= 1, "Error transaction not detected"
    assert stats['unmatched_gaxi_rsp'] >= 1, "Timeout not detected"
    
    print("Error handling verification: PASS")
```

### Multi-Bridge System Verification

```python
# Test system with multiple APB-GAXI bridges
class MultiBridgeTestEnvironment:
    def __init__(self, num_bridges):
        self.scoreboards = {}
        for i in range(num_bridges):
            self.scoreboards[i] = APBGAXIScoreboard(f"Bridge_{i}", log=logger)
    
    def add_bridge_transaction(self, bridge_id, apb_tx, gaxi_cmd, gaxi_rsp):
        if bridge_id in self.scoreboards:
            sb = self.scoreboards[bridge_id]
            sb.add_apb_transaction(apb_tx)
            sb.add_gaxi_command(gaxi_cmd)
            sb.add_gaxi_response(gaxi_rsp)
    
    def generate_comprehensive_report(self):
        total_stats = {
            'apb_transactions': 0,
            'matched_pairs': 0,
            'error_transactions': 0
        }
        
        print("=== Multi-Bridge System Report ===")
        for bridge_id, scoreboard in self.scoreboards.items():
            stats = scoreboard.get_stats()
            total_stats['apb_transactions'] += stats['apb_transactions']
            total_stats['matched_pairs'] += stats['matched_pairs']
            total_stats['error_transactions'] += stats['error_transactions']
            
            success_rate = stats['matched_pairs'] / stats['apb_transactions'] * 100 if stats['apb_transactions'] > 0 else 0
            print(f"Bridge {bridge_id}: {stats['matched_pairs']}/{stats['apb_transactions']} ({success_rate:.1f}%)")
        
        overall_success = total_stats['matched_pairs'] / total_stats['apb_transactions'] * 100 if total_stats['apb_transactions'] > 0 else 0
        print(f"Overall System: {total_stats['matched_pairs']}/{total_stats['apb_transactions']} ({overall_success:.1f}%)")
        print(f"Total Errors: {total_stats['error_transactions']}")
        
        return total_stats

# Usage
async def test_multi_bridge_system():
    test_env = MultiBridgeTestEnvironment(num_bridges=4)
    
    # Generate transactions for each bridge
    for bridge_id in range(4):
        for addr_offset in range(10):
            addr = 0x10000 + (bridge_id * 0x1000) + (addr_offset * 4)
            data = 0xB0000000 + (bridge_id << 16) + addr_offset
            
            apb_tx = create_apb_write(addr=addr, data=data)
            gaxi_cmd = create_gaxi_command(addr=addr, data=data, cmd=1)
            gaxi_rsp = create_gaxi_response(status='OKAY')
            
            test_env.add_bridge_transaction(bridge_id, apb_tx, gaxi_cmd, gaxi_rsp)
            
            await Timer(50, units='ns')
    
    # Generate system report
    system_stats = test_env.generate_comprehensive_report()
    
    # Verify system performance
    assert system_stats['error_transactions'] == 0, "System errors detected"
    assert system_stats['matched_pairs'] == system_stats['apb_transactions'], "Incomplete transaction matching"
    
    print("Multi-bridge system verification: PASS")
```

## Best Practices

### Timeout Configuration
- Configure appropriate timeouts based on bridge latency characteristics
- Use shorter timeouts for low-latency bridges
- Account for memory access delays in timeout calculations

### Transaction Ordering
- Add transactions in realistic temporal order
- Ensure APB transactions are added before corresponding GAXI commands
- Add GAXI responses promptly after commands for timing accuracy

### Error Analysis
- Enable detailed logging for field extraction debugging
- Monitor timeout statistics for performance analysis
- Use error classification for systematic debugging

### Performance Optimization
- Clear scoreboards between major test phases
- Monitor queue sizes in high-throughput scenarios
- Use appropriate timeout values to balance accuracy and performance

## Integration Points

### Monitor Integration
```python
# Connect monitors to scoreboard
def on_apb_transaction(packet):
    scoreboard.add_apb_transaction(packet)

def on_gaxi_command(packet):
    scoreboard.add_gaxi_command(packet)

def on_gaxi_response(packet):
    scoreboard.add_gaxi_response(packet)

apb_monitor.add_callback(on_apb_transaction)
gaxi_cmd_monitor.add_callback(on_gaxi_command)
gaxi_rsp_monitor.add_callback(on_gaxi_response)
```

### Test Environment Integration
```python
# Complete bridge test environment
class APBGAXIBridgeTestEnv:
    def __init__(self, dut, clock):
        self.scoreboard = APBGAXIScoreboard("BridgeEnv", log=logger)
        
        # Connect monitors
        self.apb_monitor = APBMonitor(dut.apb, clock)
        self.gaxi_cmd_monitor = GAXIMonitor(dut.gaxi_cmd, clock)
        self.gaxi_rsp_monitor = GAXIMonitor(dut.gaxi_rsp, clock)
        
        # Connect callbacks
        self.apb_monitor.add_callback(self.scoreboard.add_apb_transaction)
        self.gaxi_cmd_monitor.add_callback(self.scoreboard.add_gaxi_command)
        self.gaxi_rsp_monitor.add_callback(self.scoreboard.add_gaxi_response)
    
    def get_verification_results(self):
        return {
            'report': self.scoreboard.report(),
            'stats': self.scoreboard.get_stats()
        }
```

The APB-GAXI scoreboard provides comprehensive verification for protocol bridge systems with robust transaction matching, detailed error analysis, and extensive configuration options for complex multi-bridge verification scenarios.