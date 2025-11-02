# axi_read_splitter_tb.py

This module provides the main AXI Master Read Splitter Testbench for comprehensive verification of AXI transaction splitting functionality. The testbench focuses on safe address testing with realistic boundary crossing scenarios while avoiding impossible edge cases.

## Purpose

The testbench serves as the primary verification environment for AXI read splitter components by:
- Generating realistic boundary crossing test scenarios
- Providing safe address testing without wraparound complications
- Supporting multiple data widths with dynamic test generation
- Implementing comprehensive verification flows
- Offering detailed error reporting and analysis

## Key Features

### Safe Address Testing Approach
- **NO WRAPAROUND TESTING**: All addresses stay in safe region (< MAX_ADDR/2)
- **Proper Address Alignment**: Addresses aligned to data width boundaries
- **Dynamic Test Generation**: Test cases generated based on actual data width
- **Comprehensive Address Validation**: Safety checks with enhanced error reporting
- **Correct AXI Size Field Usage**: Proper size field calculation for data widths

### Realistic Testing Philosophy
- No address wraparound scenarios (transactions never wrap 0xFFFFFFFF → 0x00000000)
- Focus on legitimate boundary crossing scenarios
- Comprehensive coverage while avoiding impossible edge cases
- Data width aware test scenarios

## Core Class: AxiReadSplitterTB

### Initialization

```python
class AxiReadSplitterTB(TBBase):
    def __init__(self, dut, **kwargs)
```

**Automatic Configuration:**
- Extracts data width (DW) from DUT parameters
- Calculates bytes per beat and AXI size field
- Sets up safe address ranges
- Configures boundary sizes and alignment
- Initializes components and scoreboards

**Key Attributes:**
- `DW`: Data width in bits (extracted from DUT)
- `BYTES_PER_BEAT`: Bytes per data beat (DW/8)
- `AXI_SIZE`: AXI size field value (log2(BYTES_PER_BEAT))
- `MAX_SAFE_ADDR`: Maximum safe address (0x7FFFFFFF)
- `BOUNDARY_SIZE`: Memory boundary size (default: 0x1000)

### Component Setup

#### AXI Interface Components

```python
def setup_axi_components(self):
```

**Slave AXI Interface (S_AXI):**
- Connects to testbench traffic generators
- Receives original transactions from test cases
- Monitors upstream transaction flow

**Master AXI Interface (M_AXI):**
- Connects to memory model or slave responder
- Receives split transactions from DUT
- Provides response data for verification

**Split Information Interface:**
- Monitors split information from DUT
- Tracks expected split behavior
- Correlates splits with original transactions

#### Monitor Setup

```python
def setup_monitors(self):
```

**S_AXI Monitors:**
- `s_axi_ar_monitor`: Monitors original AR requests
- `s_axi_r_monitor`: Monitors consolidated R responses

**M_AXI Monitors:**
- `m_axi_ar_monitor`: Monitors split AR requests
- `m_axi_r_monitor`: Monitors split R responses

**Split Info Monitor:**
- Tracks split information packets
- Correlates with transaction IDs

### Test Generation

#### `generate_boundary_crossing_address(data_width, boundary_size)`

Generates addresses that will cross specified boundaries.

**Algorithm:**
1. Calculate bytes per beat based on data width
2. Find suitable boundary crossing point
3. Generate address near boundary
4. Ensure transaction will cross boundary
5. Validate address is in safe range

**Safety Checks:**
- Address must be < MAX_SAFE_ADDR
- Transaction must not wrap around
- Address must be properly aligned
- Boundary crossing must be achievable

**Usage:**
```python
# Generate boundary crossing scenario
addr = self.generate_boundary_crossing_address(
    data_width=64,
    boundary_size=0x1000  # 4KB boundary
)
```

#### `create_test_transaction(addr, length, **kwargs)`

Creates test transaction with comprehensive parameter validation.

**Parameters:**
- `addr`: Transaction address (validated for safety)
- `length`: Burst length (0-255)
- `**kwargs`: Additional AXI parameters

**Validation:**
- Address alignment to data width
- Safe address range checking
- Burst length bounds checking
- Size field calculation and validation

**Returns:** AXIAddressPacket ready for transmission

### Test Execution Methods

#### `run_boundary_crossing_tests(num_tests=10)`

Executes comprehensive boundary crossing test suite.

**Test Scenarios:**
1. **Single Boundary Crossing**: Transactions crossing one boundary
2. **Multiple Boundary Crossing**: Large transactions crossing multiple boundaries  
3. **Edge Case Testing**: Transactions starting near boundaries
4. **Variable Length Testing**: Different burst lengths and patterns
5. **Data Width Variations**: Tests across supported data widths

**Execution Flow:**
```python
async def run_boundary_crossing_tests(self, num_tests=10):
    for test_num in range(num_tests):
        # Generate test scenario
        addr = self.generate_boundary_crossing_address(self.DW, self.BOUNDARY_SIZE)
        length = random.randint(1, 16)
        
        # Create and send transaction
        test_txn = self.create_test_transaction(addr, length)
        await self.send_test_transaction(test_txn)
        
        # Wait for completion and verify
        await self.wait_for_transaction_completion(test_txn.id)
        result = self.scoreboard.verify_transaction_completion(test_txn.id)
        
        # Report results
        self.report_test_result(test_num, result)
```

#### `run_split_verification_tests()`

Specialized tests for split behavior verification.

**Test Focus:**
- Split count accuracy
- Split boundary alignment
- Data integrity across splits
- Response consolidation
- Timing relationships

#### `run_stress_tests(duration_ms=1000)`

High-throughput stress testing with concurrent transactions.

**Features:**
- Multiple concurrent transactions
- Randomized parameters within safe bounds
- Sustained traffic generation
- Performance monitoring
- Error rate analysis

### Memory Model Integration

#### Built-in Memory Responder

```python
def setup_memory_model(self):
```

**Features:**
- Deterministic data generation for verification
- Address-based data patterns
- Proper AXI protocol compliance
- Response timing control

**Data Generation:**
```python
def generate_deterministic_data(self, addr, beat, txn_id):
    # Generate predictable data pattern
    base_pattern = (addr & 0xFFFF) | ((beat & 0xFF) << 16) | ((txn_id & 0xFF) << 24)
    return base_pattern
```

### Transaction Context and Error Reporting

#### TransactionContext Class

Enhanced context tracking for detailed error reporting:

```python
class TransactionContext:
    def __init__(self, ar_packet, boundary_size, data_width):
        self.ar_packet = ar_packet
        self.boundary_size = boundary_size
        self.data_width = data_width
        self.expected_splits = self.calculate_expected_splits()
        self.safety_analysis = self.analyze_safety_constraints()
```

**Context Information:**
- Original transaction parameters
- Boundary analysis and split predictions
- Safety constraint verification
- Data width considerations
- Timing expectations

### Verification and Analysis

#### `verify_all_transactions()`

Comprehensive verification of all completed transactions.

**Verification Stages:**
1. **Transaction Completion**: All transactions finished
2. **Split Verification**: Split counts and boundaries correct
3. **Data Integrity**: Data consistency across splits
4. **Protocol Compliance**: Proper AXI protocol adherence
5. **Performance Analysis**: Timing and throughput metrics

#### Error Categories and Handling

**Safety Violations:**
- Address wraparound detection
- Unsafe address range usage
- Alignment constraint violations

**Protocol Errors:**
- AXI protocol compliance failures
- Response correlation errors
- Timing constraint violations

**Data Integrity Issues:**
- Data corruption across splits
- Response consolidation errors
- Pattern verification failures

### Advanced Configuration

#### Custom Boundary Sizes

```python
# Configure different boundary sizes
tb.configure_boundary_size(0x2000)  # 8KB boundaries
tb.configure_boundary_size(0x4000)  # 16KB boundaries
```

#### Data Width Support

**Supported Data Widths:**
- 32-bit (DW=32, BYTES_PER_BEAT=4, AXI_SIZE=2)
- 64-bit (DW=64, BYTES_PER_BEAT=8, AXI_SIZE=3)
- 128-bit (DW=128, BYTES_PER_BEAT=16, AXI_SIZE=4)
- 256-bit (DW=256, BYTES_PER_BEAT=32, AXI_SIZE=5)
- 512-bit (DW=512, BYTES_PER_BEAT=64, AXI_SIZE=6)

#### Address Range Configuration

```python
# Configure safe address ranges
tb.configure_address_range(
    min_addr=0x1000,     # Start address
    max_addr=0x7FFFFFFF  # Maximum safe address
)
```

## Usage Examples

### Basic Boundary Crossing Test

```python
@cocotb.test()
async def test_basic_boundary_crossing(dut):
    tb = AxiReadSplitterTB(dut)
    await tb.initialize()
    
    # Run boundary crossing tests
    await tb.run_boundary_crossing_tests(num_tests=5)
    
    # Verify all transactions
    results = await tb.verify_all_transactions()
    
    # Check results
    assert results.all_passed, f"Verification failed: {results.error_summary}"
```

### Custom Test Scenario

```python
@cocotb.test()
async def test_custom_scenario(dut):
    tb = AxiReadSplitterTB(dut)
    await tb.initialize()
    
    # Create custom boundary crossing transaction
    addr = 0x0FFE  # Will cross 4KB boundary
    length = 7     # 8 transfers, 32 bytes total
    
    test_txn = tb.create_test_transaction(addr, length)
    await tb.send_test_transaction(test_txn)
    
    # Wait and verify
    await tb.wait_for_transaction_completion(test_txn.id)
    result = tb.scoreboard.verify_transaction_completion(test_txn.id)
    
    assert result.passed, f"Custom test failed: {result.errors}"
```

### Stress Testing

```python
@cocotb.test()
async def test_stress_scenario(dut):
    tb = AxiReadSplitterTB(dut)
    await tb.initialize()
    
    # Run stress test for 1 second
    await tb.run_stress_tests(duration_ms=1000)
    
    # Analyze performance
    stats = tb.get_performance_statistics()
    tb.log.info(f"Transactions/sec: {stats.transactions_per_second}")
    tb.log.info(f"Error rate: {stats.error_rate:.2%}")
```

## Benefits and Applications

**Comprehensive Coverage**: Tests all aspects of AXI read splitting with realistic scenarios.

**Safety Focus**: Eliminates impossible edge cases while maintaining thorough coverage.

**Data Width Flexibility**: Supports multiple data widths with automatic configuration.

**Detailed Analysis**: Provides comprehensive error reporting and performance metrics.

**Easy Integration**: Simple integration with existing verification environments.

**Debugging Support**: Rich context information for efficient debugging.

This testbench provides a robust foundation for verifying AXI read splitter functionality with comprehensive coverage, realistic testing scenarios, and detailed analysis capabilities.