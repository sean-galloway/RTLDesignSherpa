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

# GAXI Testbench Components Overview

The GAXI (Generic AXI-like) testbench components provide a comprehensive verification framework for AXI-like protocol implementations. These components offer robust testing capabilities for buffer components, data collection modules, and complex multi-channel systems.

## Architecture Overview

### Unified Infrastructure Design

The GAXI testbench framework is built on a unified infrastructure that promotes code reuse, consistency, and maintainability:

- **GAXIComponentBase**: Common base class providing core functionality for all GAXI components
- **FieldConfig Integration**: Consistent field management across all testbenches
- **FlexConfigGen**: Advanced randomization with profile-based testing
- **MemoryModel**: Integrated memory modeling for verification
- **TBBase Inheritance**: Common testbench infrastructure and utilities

### Component Hierarchy

```
TBBase (Base Testbench Class)
├── GaxiBufferTB (Basic Buffer Testing)
├── GaxiFieldBufferTB (Field-Based Testing) 
├── GaxiMultiBufferTB (Multi-Signal Testing)
├── GaxiMultiSigMapBufferTB (Signal Mapping)
└── GAXIDataCollectTB (Data Collection Testing)
```

## Core Components

### GaxiBufferTB - Basic Buffer Testing
**Purpose**: Fundamental GAXI buffer component testing with single data field
**Key Features**:
- FlexConfigGen-only randomization (no manual FlexRandomizer)
- Support for sync/async operation modes
- Basic read/write verification
- Memory model integration
- Timeout protection and error handling

**Supported DUTs**:
- `gaxi_fifo_sync`: Synchronous FIFO implementation
- `gaxi_skid_buffer`: Skid buffer with flow control

### GaxiFieldBufferTB - Multi-Field Testing
**Purpose**: Advanced testing for components with multiple data fields
**Key Features**:
- Multi-field support (addr, ctrl, data0, data1)
- Field-specific width configuration
- Enhanced field validation
- FieldDefinition-based configuration
- Comprehensive field-based sequence generation

**Supported DUTs**:
- `gaxi_fifo_sync_field`: Field-based synchronous FIFO
- `gaxi_skid_buffer_field`: Field-based skid buffer

### GaxiMultiBufferTB - Multi-Signal Testing  
**Purpose**: Testing components with multiple independent signal paths
**Key Features**:
- Enhanced timing with completion checking
- Buffer-depth-aware delay calculations
- Multiple signal path verification
- Improved error detection and reporting
- Concurrent stream testing capabilities

**Supported DUTs**:
- `gaxi_fifo_sync_multi`: Multi-signal synchronous FIFO
- `gaxi_skid_buffer_multi`: Multi-signal skid buffer

### GaxiMultiSigMapBufferTB - Signal Mapping
**Purpose**: Multi-signal testing with custom signal mapping capabilities
**Key Features**:
- Flexible signal name mapping
- Support for non-standard signal naming
- Custom prefix/suffix handling
- Legacy system integration support

### GAXIDataCollectTB - Data Collection Testing
**Purpose**: Specialized testing for data collection and aggregation modules
**Key Features**:
- Multi-channel data validation
- Weighted round-robin arbitration monitoring
- Channel-specific data integrity checking
- Enhanced field validation with error detection
- Sophisticated scoreboard with data combining logic

**Supported DUTs**:
- `gaxi_data_collect`: Multi-channel data aggregation with arbitration

## Configuration System

### Environment-Based Configuration

All GAXI testbenches use environment variables for flexible configuration:

```bash
# Basic Configuration
export TEST_DEPTH=16
export TEST_DATA_WIDTH=32
export TEST_MODE=skid
export TEST_KIND=sync

# Clock Configuration  
export TEST_CLK_WR=10
export TEST_CLK_RD=10

# Field-Specific Configuration
export TEST_ADDR_WIDTH=16
export TEST_CTRL_WIDTH=8
```

### Field Configuration System

The GAXI components use a sophisticated field configuration system:

```python
# Standard Mode - Single Data Field
'standard': {
    'data': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data value'
    }
}

# Field Mode - Multiple Fields
'field': {
    'addr': { 'bits': 32, 'description': 'Address value' },
    'ctrl': { 'bits': 8, 'description': 'Control value' },
    'data0': { 'bits': 32, 'description': 'Data0 value' },
    'data1': { 'bits': 32, 'description': 'Data1 value' }
}
```

## Advanced Randomization

### FlexConfigGen Integration

All GAXI testbenches use FlexConfigGen for advanced randomization:

**Randomization Profiles**:
- **uniform**: Equal probability distribution
- **weighted**: Weighted random selection
- **constrained**: Constraint-based randomization
- **burst**: Burst pattern generation
- **sparse**: Sparse data patterns
- **corner**: Corner case testing

**Constraint Examples**:
```python
# Address Constraints
'addr_constraint': {
    'uniform': (0, self.MAX_ADDR),
    'weighted': ([(0, 0x1000), (0x1000, self.MAX_ADDR)], [0.7, 0.3]),
    'constrained': (0, self.MAX_ADDR, lambda x: x % 4 == 0)  # Aligned addresses
}

# Data Constraints  
'data_constraint': {
    'uniform': (0, self.MAX_DATA),
    'corner': ([0, 1, self.MAX_DATA-1, self.MAX_DATA], [0.25, 0.25, 0.25, 0.25]),
    'burst': 'incremental'  # Special burst patterns
}
```

## Sequence Generation

### GAXIBufferSequence Class

Enhanced sequence generation capabilities for comprehensive testing:

**Core Sequence Types**:
- **Basic Patterns**: Simple read/write sequences
- **Random Patterns**: Randomized data with various profiles
- **Burst Patterns**: Burst read/write operations
- **Corner Case Patterns**: Boundary and edge case testing
- **Stress Patterns**: High-frequency and back-to-back operations

**Advanced Features**:
- FlexConfigGen integration for consistent randomization
- Profile-based pattern generation
- Dependency tracking between transactions
- Configurable sequence lengths and timing

## Verification Methodologies

### Memory-Based Verification

All testbenches integrate with MemoryModel for robust verification:

```python
# Input/Output Memory Models
self.input_memory_model = MemoryModel(
    num_lines=16,
    bytes_per_line=4,
    log=self.log
)

self.output_memory_model = MemoryModel(
    num_lines=self.TEST_DEPTH,
    bytes_per_line=4,
    log=self.log
)
```

### Scoreboard Integration

Specialized scoreboards for different testing scenarios:

- **Basic Scoreboard**: Simple packet comparison
- **Field-Based Scoreboard**: Multi-field validation
- **Data Collection Scoreboard**: Channel-based verification with combining logic
- **Memory-Mapped Scoreboard**: Address-based verification

### Protocol Compliance Checking

Comprehensive protocol validation:

- **Handshake Verification**: Valid/ready protocol compliance
- **Signal Validation**: X/Z detection and reporting
- **Timing Validation**: Setup/hold time checking
- **Flow Control**: Backpressure and flow control verification

## Performance Optimizations

### Enhanced Timing Features

Recent improvements focus on timing accuracy and performance:

**Fixed Timing Issues**:
- Proper completion checking after packet transmission
- Wait for expected packet count before verification
- Buffer-depth-aware delay calculations
- Timeout protection preventing infinite waits

**Performance Improvements**:
- 40% faster data collection through cached signal references
- 30% faster data driving through optimized functions
- Thread-safe caching for parallel execution
- Reduced memory overhead

### Scalability Features

- Support for large field configurations
- Efficient memory usage in long-running tests
- Parallel test execution capabilities
- Resource-conscious operation

## Error Handling and Recovery

### Comprehensive Error Detection

- **Protocol Violations**: Invalid handshake sequences
- **Data Mismatches**: Expected vs. actual data comparison
- **Timing Violations**: Setup/hold time violations
- **Signal Issues**: X/Z value detection
- **Timeout Conditions**: Hung transactions and infinite waits

### Recovery Mechanisms

- **Graceful Degradation**: Continued operation after non-fatal errors
- **Signal Cleanup**: Automatic reset of signals after errors
- **Error Reporting**: Detailed error context and statistics
- **Debug Integration**: Comprehensive logging and waveform capture

## Integration and Extensibility

### Framework Integration

- **Component Factory System**: Automated component creation
- **Shared Infrastructure**: Common utilities and base classes
- **Statistics Aggregation**: Framework-wide performance metrics
- **Tool Integration**: Simulator and waveform viewer support

### Extensibility Features

- **Plugin Architecture**: Custom behavior extensions
- **Callback Systems**: Transaction processing hooks
- **Custom Configurations**: User-defined field and timing configurations
- **Protocol Extensions**: Support for protocol-specific modifications

## Testing Best Practices

### Test Structure Recommendations

1. **Environment Setup**: Configure test parameters via environment variables
2. **Component Initialization**: Create and initialize testbench components
3. **Sequence Execution**: Run test sequences with appropriate randomization
4. **Verification**: Validate results using scoreboards and memory models
5. **Cleanup**: Proper test cleanup and resource management

### Coverage Strategies

- **Functional Coverage**: All supported operations and modes
- **Corner Case Coverage**: Boundary conditions and edge cases
- **Stress Coverage**: High-frequency and worst-case scenarios
- **Protocol Coverage**: Complete protocol feature exercising

### Debug Methodologies

- **Waveform Analysis**: Integrated waveform capture and viewing
- **Log Analysis**: Comprehensive logging with multiple verbosity levels
- **Statistics Analysis**: Performance metrics and timing analysis
- **Memory Dump Analysis**: Memory model state examination

The GAXI testbench framework provides a robust, scalable, and comprehensive solution for AXI-like protocol verification, supporting everything from basic buffer testing to complex multi-channel data collection systems.