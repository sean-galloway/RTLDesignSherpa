# axi_write_splitter_tb.py

This module provides the main AXI Master Write Splitter Testbench for comprehensive verification of AXI write transaction splitting functionality. The testbench handles the complex three-channel write flow (AW → W → B) with safe address testing and realistic boundary crossing scenarios.

## Purpose

The write splitter testbench serves as the primary verification environment for AXI write splitter components by:
- Generating realistic write boundary crossing test scenarios
- Coordinating three-channel write flow verification (AW → W → B)
- Providing safe address testing without wraparound complications
- Supporting write data generation and distribution testing
- Implementing comprehensive write transaction verification flows
- Offering detailed write-specific error reporting and analysis

## Key Features

### Write-Specific Testing Features
- **Three-Channel Flow**: AW (address) → W (data) → B (response) coordination
- **Write Data Generation**: Deterministic write data patterns for verification
- **WLAST Verification**: Validation of WLAST signals at split boundaries
- **Single Response Verification**: Ensures single response per transaction regardless of splits
- **Write Strobe Patterns**: Generation and verification of write strobe patterns
- **Data Integrity**: Write data integrity verification across splits

### Enhanced Timing and Flow Control
- **Proper Split Timing**: Correct timing for split information arrival
- **Sequential Data Transmission**: Coordinated write data transmission across splits
- **Response Consolidation**: Verification of write response consolidation

### Safe Write Address Testing
- **NO WRAPAROUND TESTING**: All write addresses stay in safe region (< MAX_ADDR/2)
- **Write Address Alignment**: Addresses aligned to write data width boundaries
- **Dynamic Write Test Generation**: Test cases generated based on actual write data width
- **Comprehensive Write Address Validation**: Safety checks with enhanced error reporting

## Core Class: AxiWriteSplitterTB

### Initialization and Configuration

```python
class AxiWriteSplitterTB(TBBase):
    def __init__(self, dut, **kwargs)
```

**Automatic Write Configuration:**
- Extracts write data width (DW) from DUT parameters
- Calculates write bytes per beat and AXI size field
- Sets up safe write address ranges
- Configures write boundary sizes and alignment
- Initializes write components and scoreboards

**Write-Specific Attributes:**
- `WRITE_DW`: Write data width in bits
- `WRITE_BYTES_PER_BEAT`: Bytes per write data beat
- `WRITE_AXI_SIZE`: AXI size field value for writes
- `MAX_SAFE_WRITE_ADDR`: Maximum safe write address
- `WRITE_BOUNDARY_SIZE`: Write memory boundary size

### Write Component Setup

#### Write AXI Interface Components

```python
def setup_write_axi_components(self):
```

**Slave Write AXI Interface (S_AXI Write Channels):**
- `S_AXI_AW`: Receives original write address transactions
- `S_AXI_W`: Receives original write data
- `S_AXI_B`: Sends consolidated write responses

**Master Write AXI Interface (M_AXI Write Channels):**
- `M_AXI_AW`: Sends split write address transactions
- `M_AXI_W`: Sends split write data
- `M_AXI_B`: Receives split write responses

**Write Split Information Interface:**
- Monitors write split information from DUT
- Tracks expected write split behavior
- Correlates write splits with original transactions

#### Write Monitor Setup

```python
def setup_write_monitors(self):
```

**S_AXI Write Monitors:**
- `s_axi_aw_monitor`: Monitors original AW requests
- `s_axi_w_monitor`: Monitors original W data
- `s_axi_b_monitor`: Monitors consolidated B responses

**M_AXI Write Monitors:**
- `m_axi_aw_monitor`: Monitors split AW requests
- `m_axi_w_monitor`: Monitors split W data
- `m_axi_b_monitor`: Monitors split B responses

**Write Split Info Monitor:**
- Tracks write split information packets
- Correlates with write transaction IDs

### Write Test Generation

#### `generate_write_boundary_crossing_address(data_width, boundary_size)`

Generates write addresses that will cross specified boundaries.

**Write-Specific Algorithm:**
1. Calculate write bytes per beat based on data width
2. Find suitable write boundary crossing point
3. Generate write address near boundary
4. Ensure write transaction will cross boundary
5. Validate write address is in safe range

**Write Safety Checks:**
- Write address must be < MAX_SAFE_WRITE_ADDR
- Write transaction must not wrap around
- Write address must be properly aligned for write operations
- Write boundary crossing must be achievable with data pattern

**Usage:**
```python
# Generate write boundary crossing scenario
write_addr = self.generate_write_boundary_crossing_address(
    data_width=64,
    boundary_size=0x1000  # 4KB boundary
)
```

#### `create_write_test_transaction(addr, length, write_data_pattern=None)`

Creates write test transaction with comprehensive parameter validation.

**Parameters:**
- `addr`: Write transaction address (validated for safety)
- `length`: Write burst length (0-255)
- `write_data_pattern`: Optional custom write data pattern

**Write Validation:**
- Write address alignment to data width
- Safe write address range checking
- Write burst length bounds checking
- Write size field calculation and validation
- Write data pattern generation if not provided

**Returns:** 
- `AXIWriteAddressPacket`: Ready for AW transmission
- `List[AXIWriteDataPacket]`: Corresponding W data packets

### Write Test Execution Methods

#### `run_write_boundary_crossing_tests(num_tests=10)`

Executes comprehensive write boundary crossing test suite.

**Write Test Scenarios:**
1. **Single Write Boundary Crossing**: Write transactions crossing one boundary
2. **Multiple Write Boundary Crossing**: Large write transactions crossing multiple boundaries
3. **Write Edge Case Testing**: Write transactions starting near boundaries
4. **Variable Write Length Testing**: Different write burst lengths and patterns
5. **Write Data Width Variations**: Write tests across supported data widths
6. **Write Strobe Pattern Testing**: Various write strobe patterns and partial writes

**Write Execution Flow:**
```python
async def run_write_boundary_crossing_tests(self, num_tests=10):
    for test_num in range(num_tests):
        # Generate write test scenario
        write_addr = self.generate_write_boundary_crossing_address(self.WRITE_DW, self.WRITE_BOUNDARY_SIZE)
        write_length = random.randint(1, 16)
        
        # Create write transaction and data
        aw_packet, w_packets = self.create_write_test_transaction(write_addr, write_length)
        
        # Send write address
        await self.send_write_address_transaction(aw_packet)
        
        # Send write data sequentially
        for w_packet in w_packets:
            await self.send_write_data_beat(w_packet)
        
        # Wait for write completion and verify
        await self.wait_for_write_transaction_completion(aw_packet.id)
        result = self.write_scoreboard.verify_write_transaction_completion(aw_packet.id)
        
        # Report write results
        self.report_write_test_result(test_num, result)
```

#### `run_write_split_verification_tests()`

Specialized tests for write split behavior verification.

**Write Split Test Focus:**
- Write split count accuracy for AW channel
- Write split boundary alignment
- Write data distribution across splits
- Write response consolidation verification
- Write timing relationships across AW, W, B channels

#### `run_write_stress_tests(duration_ms=1000)`

High-throughput write stress testing with concurrent write transactions.

**Write Stress Features:**
- Multiple concurrent write transactions
- Randomized write parameters within safe bounds
- Sustained write traffic generation
- Write performance monitoring
- Write error rate analysis

### Write Memory Model Integration

#### Built-in Write Memory Responder

```python
def setup_write_memory_model(self):
```

**Write Memory Features:**
- Write data storage and verification
- Address-based write data patterns
- Proper write AXI protocol compliance
- Write response timing control
- Write data integrity checking

**Write Data Storage:**
```python
def store_write_data(self, addr, data, strb):
    # Store write data with strobe-based masking
    for byte_idx in range(len(data) // 8):
        if strb & (1 << byte_idx):
            byte_addr = addr + byte_idx
            byte_data = (data >> (byte_idx * 8)) & 0xFF
            self.memory_model[byte_addr] = byte_data
```

### Write Transaction Context and Error Reporting

#### WriteTransactionContext Class

Enhanced context tracking for detailed write error reporting:

```python
class WriteTransactionContext:
    def __init__(self, aw_packet, w_packets, boundary_size, data_width):
        self.aw_packet = aw_packet
        self.w_packets = w_packets
        self.boundary_size = boundary_size
        self.data_width = data_width
        self.expected_write_splits = self.calculate_expected_write_splits()
        self.write_safety_analysis = self.analyze_write_safety_constraints()
        self.write_data_distribution = self.analyze_write_data_distribution()
```

**Write Context Information:**
- Original write transaction parameters (AW and W)
- Write boundary analysis and split predictions
- Write safety constraint verification
- Write data width considerations
- Write timing expectations across AW, W, B phases

### Write Verification and Analysis

#### `verify_all_write_transactions()`

Comprehensive verification of all completed write transactions.

**Write Verification Stages:**
1. **Write Transaction Completion**: All write transactions finished (AW, W, B)
2. **Write Split Verification**: Write split counts and boundaries correct
3. **Write Data Integrity**: Write data consistency across splits
4. **Write Protocol Compliance**: Proper AXI write protocol adherence
5. **Write Performance Analysis**: Write timing and throughput metrics
6. **Write Response Consolidation**: Single response per original write transaction

#### Write Error Categories and Handling

**Write Safety Violations:**
- Write address wraparound detection
- Unsafe write address range usage
- Write alignment constraint violations

**Write Protocol Errors:**
- AXI write protocol compliance failures
- Write response correlation errors
- Write timing constraint violations
- WLAST signal placement errors

**Write Data Integrity Issues:**
- Write data corruption across splits
- Write response consolidation errors
- Write data pattern verification failures
- Write strobe pattern violations

### Advanced Write Configuration

#### Custom Write Boundary Sizes

```python
# Configure different write boundary sizes
tb.configure_write_boundary_size(0x2000)  # 8KB write boundaries
tb.configure_write_boundary_size(0x4000)  # 16KB write boundaries
```

#### Write Data Width Support

**Supported Write Data Widths:**
- 32-bit writes (WRITE_DW=32, WRITE_BYTES_PER_BEAT=4, WRITE_AXI_SIZE=2)
- 64-bit writes (WRITE_DW=64, WRITE_BYTES_PER_BEAT=8, WRITE_AXI_SIZE=3)
- 128-bit writes (WRITE_DW=128, WRITE_BYTES_PER_BEAT=16, WRITE_AXI_SIZE=4)
- 256-bit writes (WRITE_DW=256, WRITE_BYTES_PER_BEAT=32, WRITE_AXI_SIZE=5)
- 512-bit writes (WRITE_DW=512, WRITE_BYTES_PER_BEAT=64, WRITE_AXI_SIZE=6)

#### Write Address Range Configuration

```python
# Configure safe write address ranges
tb.configure_write_address_range(
    min_write_addr=0x1000,     # Start write address
    max_write_addr=0x7FFFFFFF  # Maximum safe write address
)
```

### Write Data Generation and Patterns

#### `generate_write_data_pattern(base_addr, beat_num, txn_id, pattern_type="deterministic")`

Generates various write data patterns for comprehensive testing.

**Pattern Types:**
- `"deterministic"`: Address and beat-based predictable patterns
- `"random"`: Randomized data with fixed seed for reproducibility
- `"incremental"`: Incrementing data patterns
- `"alternating"`: Alternating bit patterns
- `"custom"`: User-defined custom patterns

**Usage:**
```python
# Generate deterministic write data pattern
write_data = self.generate_write_data_pattern(
    base_addr=0x1000,
    beat_num=5,
    txn_id=0x42,
    pattern_type="deterministic"
)
```

#### Write Strobe Pattern Generation

```python
def generate_write_strobe_pattern(data_width, valid_bytes, alignment_offset=0):
    """Generate appropriate write strobe patterns for partial writes"""
    strobe_width = data_width // 8
    strobe_pattern = 0
    
    for byte_idx in range(valid_bytes):
        strobe_bit = (alignment_offset + byte_idx) % strobe_width
        strobe_pattern |= (1 << strobe_bit)
    
    return strobe_pattern
```

## Usage Examples

### Basic Write Boundary Crossing Test

```python
@cocotb.test()
async def test_write_boundary_crossing(dut):
    tb = AxiWriteSplitterTB(dut)
    await tb.initialize()
    
    # Run write boundary crossing tests
    await tb.run_write_boundary_crossing_tests(num_tests=5)
    
    # Verify all write transactions
    results = await tb.verify_all_write_transactions()
    
    # Check write results
    assert results.all_write_passed, f"Write verification failed: {results.write_error_summary}"
```

### Custom Write Test Scenario

```python
@cocotb.test()
async def test_custom_write_scenario(dut):
    tb = AxiWriteSplitterTB(dut)
    await tb.initialize()
    
    # Create custom write boundary crossing transaction
    write_addr = 0x0FFE  # Will cross 4KB boundary
    write_length = 7     # 8 write transfers, 32 bytes total
    
    aw_packet, w_packets = tb.create_write_test_transaction(write_addr, write_length)
    
    # Send write transaction
    await tb.send_write_address_transaction(aw_packet)
    for w_packet in w_packets:
        await tb.send_write_data_beat(w_packet)
    
    # Wait and verify write completion
    await tb.wait_for_write_transaction_completion(aw_packet.id)
    result = tb.write_scoreboard.verify_write_transaction_completion(aw_packet.id)
    
    assert result.passed, f"Custom write test failed: {result.write_errors}"
```

### Write Stress Testing

```python
@cocotb.test()
async def test_write_stress_scenario(dut):
    tb = AxiWriteSplitterTB(dut)
    await tb.initialize()
    
    # Run write stress test for 1 second
    await tb.run_write_stress_tests(duration_ms=1000)
    
    # Analyze write performance
    write_stats = tb.get_write_performance_statistics()
    tb.log.info(f"Write Transactions/sec: {write_stats.write_transactions_per_second}")
    tb.log.info(f"Write Data throughput: {write_stats.write_data_mbps:.2f} MB/s")
    tb.log.info(f"Write Error rate: {write_stats.write_error_rate:.2%}")
```

## Benefits and Applications

**Comprehensive Write Coverage**: Tests all aspects of AXI write splitting with realistic write scenarios.

**Three-Channel Coordination**: Proper verification of AW, W, and B channel coordination in split transactions.

**Write Data Integrity**: Ensures write data integrity across split boundaries with comprehensive verification.

**Write Safety Focus**: Eliminates impossible write edge cases while maintaining thorough coverage.

**Write Data Width Flexibility**: Supports multiple write data widths with automatic configuration.

**Detailed Write Analysis**: Provides comprehensive write error reporting and performance metrics.

**Easy Write Integration**: Simple integration with existing verification environments for write testing.

**Write Debugging Support**: Rich context information for efficient write debugging.

This write testbench provides a robust foundation for verifying AXI write splitter functionality with comprehensive coverage, realistic write testing scenarios, and detailed write analysis capabilities.