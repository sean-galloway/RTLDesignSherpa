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

# Scoreboards Overview

The CocoTBFramework scoreboards directory provides a comprehensive verification infrastructure for automated transaction checking across multiple protocols. This system enables robust verification of protocol bridges, memory models, and complex multi-protocol designs through systematic comparison of expected versus actual transactions.

## Framework Philosophy

The scoreboard system is designed around the principles of **automated verification**, **cross-protocol support**, and **comprehensive analysis**. The framework provides:

**Automated Transaction Matching**: Intelligent queuing and comparison of expected versus actual transactions
**Protocol Abstraction**: Common interfaces that work across different bus protocols
**Cross-Protocol Verification**: Support for protocol bridges and mixed-protocol systems
**Comprehensive Reporting**: Detailed error analysis, statistics, and performance metrics
**Extensible Architecture**: Easy addition of new protocols and custom verification logic

## Architecture Overview

### Layered Verification Architecture

The scoreboard system follows a layered architecture that separates protocol-specific logic from common verification infrastructure:

```
┌─────────────────────────────────────────────────────────┐
│                 Application Layer                      │
│              (Test Scripts & Sequences)                │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│              Protocol-Specific Layer                   │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │     APB     │ │    GAXI     │ │    FIFO     │     │
│   │ Scoreboard  │ │ Scoreboard  │ │ Scoreboard  │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │    AXI4     │ │ APB-GAXI    │ │   Custom    │     │
│   │ Scoreboard  │ │   Bridge    │ │ Scoreboards │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│              Cross-Protocol Layer                      │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │ Protocol    │ │ Transform   │ │ Memory      │     │
│   │Transformers │ │ Scoreboards │ │ Adapters    │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                 Foundation Layer                       │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │    Base     │ │ Transaction │ │ Statistics  │     │
│   │ Scoreboard  │ │   Queuing   │ │& Reporting  │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
```

## Core Framework Components

### BaseScoreboard - Foundation Infrastructure

The `BaseScoreboard` class provides the fundamental verification infrastructure used by all protocol-specific scoreboards:

**Core Capabilities**:
- **Transaction Queuing**: Automatic management of expected vs actual transaction queues using efficient deque structures
- **Comparison Engine**: Framework for transaction matching and field-by-field validation
- **Error Tracking**: Comprehensive error counting, categorization, and detailed reporting
- **Statistics Generation**: Pass/fail rates, timing analysis, and performance metrics
- **Timeout Management**: Configurable timeout handling for transaction matching

**Advanced Features**:
- **Transformer Integration**: Interface for protocol conversion and cross-protocol verification
- **Memory Model Support**: Integration with memory adapters for memory-mapped verification
- **Flexible Matching**: Support for different matching strategies (FIFO, ID-based, custom)
- **Rich Reporting**: HTML and text-based reports with detailed analysis

### ProtocolTransformer - Cross-Protocol Support

The `ProtocolTransformer` base class enables seamless cross-protocol verification:

**Transformation Engine**:
- **Bidirectional Conversion**: Transform transactions between different protocols
- **Field Mapping**: Intelligent mapping of fields between protocol formats
- **Timing Preservation**: Maintain timing relationships during transformation
- **Error Handling**: Robust transformation with comprehensive failure tracking

**Extensibility**:
- **Custom Transformers**: Easy creation of protocol-specific transformers
- **Chaining Support**: Multiple transformation stages for complex conversions
- **Validation**: Built-in validation of transformation correctness
- **Performance Tracking**: Statistics on transformation overhead and success rates

## Protocol-Specific Scoreboards

### APB Scoreboard - Advanced Peripheral Bus

The APB scoreboard provides comprehensive verification for ARM's Advanced Peripheral Bus protocol:

**Single Slave Support (`APBScoreboard`)**:
- **Transaction Verification**: Complete APB read/write transaction checking
- **Field Validation**: Address, data, control signal verification
- **Protocol Compliance**: APB timing and signal relationship checking
- **Error Categorization**: Detailed classification of different error types

**Multi-Slave Support (`APBMultiSlaveScoreboard`)**:
- **Address-Based Routing**: Automatic transaction routing to appropriate slave scoreboards
- **Configurable Address Maps**: Flexible address range configuration for each slave
- **Aggregate Reporting**: Combined statistics across all slaves
- **Slave-Specific Analysis**: Individual slave performance and error tracking

### AXI4 Scoreboard - Advanced eXtensible Interface

The AXI4 scoreboard handles the complexity of the full AXI4 protocol:

**Advanced Transaction Management**:
- **ID-Based Tracking**: Separate transaction queues for each AXI4 ID
- **Channel Separation**: Independent handling of read (AR/R) and write (AW/W/B) channels
- **Out-of-Order Support**: Proper handling of AXI4's out-of-order transaction completion
- **Protocol Compliance**: Comprehensive AXI4 specification checking

**Performance Analysis**:
- **Throughput Measurement**: Real-time bandwidth calculation
- **Latency Tracking**: Per-transaction and statistical latency analysis
- **Outstanding Transaction Monitoring**: Track inflight transactions and resource utilization
- **Channel Utilization**: Individual channel efficiency metrics

### GAXI Scoreboard - Generic AXI-like Protocol

The GAXI scoreboard provides verification for simplified AXI-like protocols:

**Modern Architecture**:
- **FieldConfig Integration**: Full support for the CocoTBFramework field configuration system
- **Flexible Packet Handling**: Works with both legacy and modern packet formats
- **Memory Model Integration**: Seamless integration with memory verification
- **Transform Support**: Enhanced cross-protocol transformation capabilities

**Advanced Comparison**:
- **Field-by-Field Analysis**: Detailed comparison with configurable field precedence
- **Intelligent Matching**: Smart transaction correlation based on protocol semantics
- **Performance Optimization**: Efficient comparison algorithms for high-throughput testing

### FIFO Scoreboard - Buffer Verification

The FIFO scoreboard specializes in buffer and queue verification:

**Memory Integration**:
- **Built-in Memory Adapter**: Direct integration with CocoTBFramework memory models
- **Data Integrity Checking**: Automatic verification of data consistency
- **Access Pattern Analysis**: Track read/write patterns and detect anomalies

**FIFO-Specific Features**:
- **Order Verification**: Ensure FIFO ordering semantics are maintained
- **Depth Monitoring**: Track buffer utilization and overflow/underflow conditions
- **Flow Control**: Verify proper handshaking and backpressure handling

## Cross-Protocol Verification

### APB-GAXI Bridge Scoreboard

The `APBGAXIScoreboard` provides specialized verification for protocol bridge implementations:

**Three-Phase Verification**:
1. **APB Transaction Receipt**: Verify APB master transaction is properly received
2. **GAXI Command Generation**: Ensure correct transformation to GAXI format
3. **GAXI Response Processing**: Validate response transformation back to APB

**Bridge-Specific Features**:
- **Latency Analysis**: Measure bridge processing delays and overhead
- **Error Propagation**: Verify proper error handling across protocol boundaries
- **Resource Utilization**: Monitor bridge internal resource usage
- **Protocol Compliance**: Ensure both protocols remain compliant during bridging

### APB-GAXI Transformer

The transformer provides bidirectional APB ↔ GAXI conversion capabilities:

**Transformation Features**:
- **Field Mapping**: Intelligent mapping between APB and GAXI field structures
- **Timing Preservation**: Maintain critical timing relationships during conversion
- **Error Handling**: Robust error detection and recovery mechanisms
- **Adapter Classes**: High-level adapters for easy integration with existing components

## Advanced Verification Capabilities

### Memory Model Integration

Scoreboards integrate seamlessly with CocoTBFramework memory models:

**Memory Adapters**:
- **Automatic Memory Operations**: Transparent read/write operations during verification
- **Field Mapping Configuration**: Flexible mapping between packet fields and memory addresses
- **Data Integrity Verification**: Automatic comparison of expected vs actual memory contents
- **Access Pattern Tracking**: Monitor memory access patterns for coverage analysis

### Statistical Analysis

Comprehensive statistical capabilities provide deep insights into verification effectiveness:

**Real-Time Metrics**:
- **Transaction Throughput**: Transactions per second and bandwidth calculations
- **Error Rates**: Real-time error rate tracking with trend analysis
- **Latency Distribution**: Histogram analysis of transaction latencies
- **Resource Utilization**: Memory usage and processing overhead tracking

**Trend Analysis**:
- **Performance Regression**: Detection of performance degradation over time
- **Error Trend Tracking**: Identification of systematic error patterns
- **Coverage Metrics**: Functional and code coverage integration
- **Comparative Analysis**: Benchmarking against previous test runs

### Custom Verification Logic

The framework supports extensive customization for specific verification needs:

**Custom Comparators**:
- **Field-Specific Logic**: Custom comparison logic for special field types
- **Protocol Extensions**: Support for proprietary protocol extensions
- **Application-Specific Checks**: Domain-specific verification requirements
- **Performance Optimizations**: Custom optimizations for high-frequency testing

## Integration and Usage Patterns

### Monitor Integration

Scoreboards integrate naturally with CocoTBFramework monitor components:

```python
# Automatic transaction capture from monitors
master_monitor.add_callback(scoreboard.add_expected)
slave_monitor.add_callback(scoreboard.add_actual)

# Real-time verification during test execution
# Scoreboard automatically processes transactions as they arrive
```

### Test Framework Integration

Seamless integration with cocotb and other test frameworks:

```python
@cocotb.test()
async def comprehensive_verification_test(dut):
    # Create scoreboard with appropriate configuration
    scoreboard = create_protocol_scoreboard(protocol_type, configuration)
    
    # Connect to system under test
    connect_monitors_to_scoreboard(dut, scoreboard)
    
    # Execute test scenarios
    await run_test_scenarios(dut, test_configuration)
    
    # Analyze results
    results = scoreboard.generate_comprehensive_report()
    verify_test_success(results)
```

### Performance Optimization

The framework includes numerous optimizations for high-performance verification:

**Efficient Data Structures**:
- **Deque-Based Queues**: O(1) transaction insertion and removal
- **Hash-Based Lookup**: Fast transaction correlation for ID-based protocols
- **Memory-Mapped Storage**: Efficient handling of large transaction volumes
- **Lazy Evaluation**: Deferred computation of expensive analysis metrics

**Parallel Processing**:
- **Thread-Safe Operations**: Safe concurrent access to scoreboard data structures
- **Asynchronous Processing**: Non-blocking transaction processing
- **Pipeline Optimization**: Overlapped comparison and analysis operations
- **Resource Pooling**: Efficient reuse of comparison and analysis resources

## Future Extensibility

The scoreboard architecture is designed for easy extension and customization:

### New Protocol Support
- **Template-Based Creation**: Standard templates for new protocol scoreboards
- **Inheritance Patterns**: Consistent inheritance from base classes
- **Configuration Standards**: Standard configuration patterns for protocol-specific features
- **Integration Guidelines**: Clear guidelines for framework integration

### Advanced Features
- **Machine Learning Integration**: AI-powered error pattern recognition
- **Formal Verification**: Integration with formal verification tools
- **Cloud-Based Analysis**: Distributed verification and analysis capabilities
- **Real-Time Visualization**: Live dashboards and visualization tools

The CocoTBFramework scoreboards provide a comprehensive, scalable, and extensible verification infrastructure that can handle everything from simple protocol verification to complex multi-protocol system verification with advanced analysis and reporting capabilities.