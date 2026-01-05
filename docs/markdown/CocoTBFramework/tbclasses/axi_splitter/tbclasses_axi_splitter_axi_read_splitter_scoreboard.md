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

# axi_read_splitter_scoreboard.py

This module provides the AXI Read Splitter Scoreboard for tracking and verifying AXI read transaction splits. The scoreboard monitors the flow from original transactions through splitting to response consolidation, ensuring data integrity and proper protocol compliance.

## Purpose

The scoreboard serves as the verification engine for AXI read splitter functionality by:
- Tracking upstream (original) and downstream (split) transactions
- Correlating split transactions with original requests
- Verifying data integrity across split boundaries
- Monitoring response consolidation
- Providing comprehensive error detection and reporting

## Key Features

### Fixed Timing Implementation
- Uses `cocotb.get_sim_time()` directly for accurate timing
- Consistent timing in all error reports
- Proper simulation time formatting
- No dependency on external timing updates

### Comprehensive Transaction Tracking
- Upstream transaction monitoring (original requests)
- Downstream transaction monitoring (split requests)  
- Response correlation and consolidation verification
- Split information tracking and validation

## Core Class: AxiReadSplitterScoreboard

### Initialization

```python
def __init__(self, alignment_mask=0xFFF, log=None, component_name="AXI_RD_SPLITTER_SB",
             id_width=8, addr_width=32, data_width=32, user_width=1)
```

**Parameters:**
- `alignment_mask`: Boundary alignment mask (default: 0xFFF for 4KB boundaries)
- `log`: Logger instance for debug output
- `component_name`: Component name for logging
- `id_width`: Transaction ID width in bits
- `addr_width`: Address width in bits
- `data_width`: Data width in bits
- `user_width`: User signal width in bits

**Setup Actions:**
- Creates field configurations for all packet types
- Initializes transaction tracking dictionaries
- Sets up statistics and error tracking
- Configures timing tracking using cocotb simulation time

### Transaction Recording Methods

#### `record_upstream_transaction(packet)`

Records an upstream read address transaction (original AR from testbench).

**Purpose:** Track original transaction requests before splitting

**Actions:**
- Converts packet to AXIAddressPacket format
- Records transaction start time
- Creates split transaction tracker
- Updates statistics
- Logs transaction details with timestamp

**Usage:**
```python
# Record original AR transaction
scoreboard.record_upstream_transaction(ar_packet)
```

#### `record_downstream_transaction(packet)`

Records downstream transactions (split ARs to DUT and R responses from DUT).

**Purpose:** Track split address requests and data responses

**Packet Handling:**
- **Address Packets (AR)**: Records split address transactions
- **Data Packets (R)**: Records response data and tracks completion

**Actions for Address Packets:**
- Adds to downstream transaction list
- Updates split transaction tracker
- Logs split transaction details

**Actions for Data Packets:**
- Records response data
- Tracks completion on LAST transfer
- Updates split transaction state
- Logs response details with timing

**Usage:**
```python
# Record split AR
scoreboard.record_downstream_transaction(split_ar_packet)

# Record R response  
scoreboard.record_downstream_transaction(r_packet)
```

#### `record_split_info(packet)`

Records split information from the DUT indicating how transactions will be split.

**Purpose:** Track expected split behavior for verification

**Actions:**
- Converts to SplitInfoPacket format
- Updates split transaction tracker
- Records split count and boundary information
- Updates statistics

**Usage:**
```python
# Record split information
scoreboard.record_split_info(split_info_packet)
```

### Verification Methods

#### `verify_transaction_completion(txn_id)`

Comprehensive verification of a completed transaction.

**Verification Checks:**
1. **Split Count Verification**: Confirms expected vs actual split count
2. **Data Integrity**: Verifies data consistency across splits
3. **Response Consolidation**: Checks proper response handling
4. **Boundary Compliance**: Validates boundary crossing behavior
5. **Timing Constraints**: Verifies proper timing relationships

**Returns:** Verification result with detailed analysis

**Usage:**
```python
# Verify completed transaction
result = scoreboard.verify_transaction_completion(0x42)
if not result.passed:
    print(f"Verification failed: {result.errors}")
```

#### `verify_all_pending_transactions()`

Verifies all pending transactions and generates comprehensive report.

**Actions:**
- Iterates through all active transactions
- Performs individual verification on each
- Aggregates results and statistics
- Generates final verification report

**Returns:** Complete verification report with:
- Overall pass/fail status
- Individual transaction results
- Error summary and categorization
- Performance statistics

### Error Handling and Reporting

#### `_add_error_with_context(error_msg, txn_id, error_category, severity)`

Enhanced error reporting with comprehensive context.

**Error Context Includes:**
- Transaction ID and timing information
- Current transaction state
- Split information and boundary analysis  
- Expected vs actual behavior
- Full transaction history

**Error Categories:**
- `SPLIT_MISMATCH`: Split count discrepancies
- `DATA_INTEGRITY`: Data corruption or inconsistency
- `RESPONSE_ERROR`: Response protocol violations
- `TIMING_VIOLATION`: Timing constraint failures
- `BOUNDARY_ERROR`: Boundary crossing violations

**Usage:**
```python
# Add error with context
scoreboard._add_error_with_context(
    "Data mismatch detected",
    txn_id=0x42,
    error_category="DATA_INTEGRITY", 
    severity="ERROR"
)
```

### Statistics and Monitoring

#### Statistics Tracking

The scoreboard maintains comprehensive statistics:

```python
stats = {
    'upstream_transactions': 0,      # Original transactions
    'downstream_transactions': 0,    # Split transactions  
    'responses_received': 0,         # Data responses
    'splits_detected': 0,           # Split operations
    'boundary_crossings_detected': 0, # Boundary violations
    'verification_checks': 0,        # Verification operations
    'total_errors': 0               # Error count
}
```

#### `get_stats()`

Returns current statistics dictionary.

#### `get_transaction_history(txn_id)`

Returns complete history for a specific transaction ID.

### Timing and Performance

#### `get_current_time_ns()`

Gets current simulation time in nanoseconds using cocotb.

#### `get_time_str()`

Returns formatted time string for logging (format: ` @ 123.4ns`).

#### Transaction Duration Tracking

- Records start time on upstream transaction
- Records completion time on final response
- Calculates transaction duration for performance analysis

## Integration Patterns

### With Testbench

```python
from .axi_read_splitter_scoreboard import AxiReadSplitterScoreboard

class AxiReadSplitterTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        
        # Create scoreboard
        self.scoreboard = AxiReadSplitterScoreboard(
            alignment_mask=0xFFF,  # 4KB boundaries
            log=self.log,
            id_width=8,
            data_width=self.DW
        )
        
    async def monitor_transactions(self):
        # Monitor and record transactions
        await self.scoreboard.record_upstream_transaction(ar_packet)
        await self.scoreboard.record_downstream_transaction(split_packet)
```

### With Monitors

```python
# Connect monitor callbacks to scoreboard
def setup_monitor_callbacks(self):
    # Upstream monitoring
    self.s_axi_ar_monitor.add_callback(
        self.scoreboard.record_upstream_transaction
    )
    
    # Downstream monitoring  
    self.m_axi_ar_monitor.add_callback(
        self.scoreboard.record_downstream_transaction
    )
    self.m_axi_r_monitor.add_callback(
        self.scoreboard.record_downstream_transaction
    )
    
    # Split info monitoring
    self.split_info_monitor.add_callback(
        self.scoreboard.record_split_info
    )
```

## Advanced Features

### Custom Verification Rules

```python
class CustomAxiReadSplitterScoreboard(AxiReadSplitterScoreboard):
    def verify_custom_constraint(self, txn_id):
        # Add custom verification logic
        txn = self.active_split_transactions[txn_id]
        
        # Custom checks
        if self.custom_boundary_check(txn):
            self._add_error_with_context(
                "Custom boundary violation",
                txn_id,
                "CUSTOM_ERROR",
                "WARNING"
            )
```

### Performance Analysis

```python
# Analyze transaction performance
def analyze_performance(self):
    results = self.scoreboard.verify_all_pending_transactions()
    
    # Extract timing data
    for txn_id, history in results.transaction_histories.items():
        duration = history.get_duration()
        split_count = len(history.split_ars)
        
        print(f"Transaction {txn_id}: {duration:.2f}ns, {split_count} splits")
```

## Error Analysis and Debugging

### Common Error Patterns

**Split Count Mismatches:**
- Expected splits don't match actual splits
- Usually indicates boundary calculation errors
- Check alignment mask and address ranges

**Data Integrity Violations:**
- Data corruption across split boundaries
- Response data doesn't match expected patterns
- Verify data generation and consolidation logic

**Response Correlation Failures:**
- Responses can't be correlated with requests
- Transaction ID mismatches or losses
- Check ID management in splitter logic

**Timing Violations:**
- Responses arrive in wrong order
- Timing constraints not met
- Analyze transaction timing with get_time_str()

### Debugging Workflow

1. **Enable Verbose Logging**: Set detailed log level
2. **Monitor Statistics**: Check stats for anomalies  
3. **Analyze Error Context**: Review error messages with full context
4. **Examine Transaction History**: Use get_transaction_history()
5. **Verify Timing**: Check timing relationships
6. **Custom Verification**: Add specific checks for suspected issues

This scoreboard provides comprehensive verification capabilities for AXI read splitter functionality with detailed error analysis, performance monitoring, and robust transaction tracking.