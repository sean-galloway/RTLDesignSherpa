### CDC Handshake Testbench (cdc_handshake.py)

Comprehensive testbench for verifying clock domain crossing implementations with sophisticated randomization:

**Core Features:**
- **Dual clock domain support**: Independent source and destination clock domains
- **Advanced timing analysis**: CDC latency measurement and timing violation detection
- **Sophisticated randomization**: 20+ randomization profiles including CDC-specific patterns
- **Memory model integration**: Shared memory across clock domains for data integrity verification
- **Performance metrics**: Throughput analysis and CDC efficiency measurements

**Use Cases:**
- Clock domain crossing verification
- Multi-clock system validation
- CDC timing analysis and optimization
- Cross-domain data integrity verification
- Performance analysis of CDC implementations# AMBA Directory Overview

The AMBA (Advanced Microcontroller Bus Architecture) directory within the CocoTBFramework provides specialized testbench classes for AMBA protocol verification with a focus on power management, randomization control, and clock domain crossing verification.

## Purpose and Scope

The AMBA directory addresses three critical aspects of AMBA protocol verification:

1. **Power Management**: Through clock gating control that monitors protocol activity and manages power consumption
2. **Randomization Control**: Through predefined configuration sets that enable consistent and reproducible test scenarios
3. **Clock Domain Crossing (CDC)**: Through comprehensive CDC verification with dual-domain testing and timing analysis

These components work together to enable comprehensive verification of AMBA-based systems while maintaining control over power consumption and test stimulus generation.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────┐
│                 AMBA Testbench Layer                   │
├─────────────────────────────────────────────────────────┤
│  Clock Gating Control  │  Randomization Configurations │
│  (amba_cg_ctrl.py)     │  (amba_random_configs.py)     │
├─────────────────────────────────────────────────────────┤
│              CocoTBFramework TBBase                     │
├─────────────────────────────────────────────────────────┤
│              Protocol Components                        │
│         (APB, AXI4, GAXI, FIFO)                        │
└─────────────────────────────────────────────────────────┘
```

## Key Components

### Clock Gating Controller (amba_cg_ctrl.py)

The `AxiClockGateCtrl` class provides intelligent clock gating management for AMBA protocols:

**Core Features:**
- **Multi-signal monitoring**: Tracks activity on both user-side and AXI interface signals
- **Configurable thresholds**: Adjustable idle count thresholds for gating decisions
- **Real-time statistics**: Comprehensive activity monitoring and reporting
- **Protocol agnostic**: Works with any AMBA protocol implementation

**Use Cases:**
- Power consumption verification
- Clock gating validation
- Performance vs. power trade-off analysis
- Debug mode control (disable gating)

### Randomization Configurations (amba_random_configs.py)

Predefined randomization settings for consistent test execution across AMBA protocols:

**Supported Protocols:**
- **APB (Advanced Peripheral Bus)**: Master and slave configurations
- **AXI (Advanced eXtensible Interface)**: Master and slave configurations
- **Generic AMBA**: Extensible for other AMBA protocols

**Configuration Categories:**
- **Fixed**: Deterministic, non-random behavior
- **Constrained**: Weighted random within specified ranges
- **Fast**: Minimal delays for high-throughput testing
- **Backtoback**: Zero-delay for maximum throughput
- **Burst Pause**: Bursty traffic with idle periods
- **Slow**: Extended delays for timing verification
- **Error Injection**: Controlled error introduction

## Integration Philosophy

The AMBA directory follows a layered integration approach:

1. **Foundation Layer**: Built on TBBase for common testbench infrastructure
2. **Protocol Layer**: Integrates with specific protocol components (APB, AXI4, etc.)
3. **Application Layer**: Provides high-level abstractions for test scenarios

## Usage Patterns

### Power-Aware Testing
```python
# Set up power monitoring
clock_gate = AxiClockGateCtrl(dut, ...)
clock_gate.enable_clock_gating(True)
clock_gate.set_idle_count(8)

# Run test with power tracking
stats = await clock_gate.monitor_activity(duration, units)
power_efficiency = stats['gated_percent']
```

### Randomization Control
```python
# Apply consistent randomization
from amba_random_configs import AXI_RANDOMIZER_CONFIGS

# High throughput scenario
config = AXI_RANDOMIZER_CONFIGS['high_throughput']
randomizer.apply_config(config)

# Power testing scenario  
config = AXI_RANDOMIZER_CONFIGS['burst_pause']
randomizer.apply_config(config)
```

### Combined Power and CDC Verification
```python
# Set up CDC testbench with power monitoring
cdc_tb = CDCHandshakeTB(dut)
clock_gate = AxiClockGateCtrl(dut, ...)

# Configure for CDC power testing
clock_gate.set_idle_count(8)
clock_gate.enable_clock_gating(True)

# Run CDC test with power analysis
cdc_task = cocotb.start_soon(cdc_tb.run_stress_test(100, 'cdc_burst_stress'))
power_task = cocotb.start_soon(clock_gate.monitor_activity(20000, 'ns'))

cdc_success = await cdc_task
power_stats = await power_task

# Validate both CDC functionality and power efficiency
assert cdc_success and power_stats['gated_percent'] > 15
```

## Benefits

### For Verification Engineers
- **Simplified Power Testing**: Easy-to-use clock gating control without RTL knowledge
- **Consistent Randomization**: Predefined configurations ensure repeatable tests
- **CDC Verification**: Comprehensive clock domain crossing validation with timing analysis
- **Comprehensive Monitoring**: Built-in statistics and reporting
- **Protocol Independence**: Works across different AMBA protocols

### For Design Teams
- **Power Validation**: Verify clock gating implementations work correctly
- **Performance Analysis**: Understand power vs. performance trade-offs
- **CDC Validation**: Ensure clock domain crossing implementations meet timing requirements
- **Configuration Management**: Standardized test scenarios across teams
- **Debug Support**: Easy disable of clock gating for debugging

### For Project Management
- **Standardization**: Consistent verification approaches across projects
- **Reusability**: Common configurations can be shared between projects
- **CDC Compliance**: Systematic verification of multi-clock designs
- **Efficiency**: Reduced test development time
- **Quality**: Comprehensive coverage of power, functional, and timing scenarios

## Best Practices

1. **Start with predefined configurations** before creating custom randomization
2. **Monitor power consumption** in all performance tests
3. **Use CDC-specific configurations** for clock domain crossing verification
4. **Use burst pause configurations** for realistic traffic patterns
5. **Disable clock gating** during functional debug sessions
6. **Combine randomization scenarios** to create comprehensive test suites
7. **Validate CDC timing** against design specifications
8. **Document custom configurations** for future reuse
9. **Validate power efficiency** against design targets

## Future Extensions

The AMBA directory is designed for extensibility:

- **Additional Protocols**: Support for AHB, ACE, CHI protocols
- **Advanced Power Models**: Integration with power estimation tools
- **Enhanced CDC Features**: Support for more complex clock relationships
- **Machine Learning**: Adaptive randomization based on coverage feedback
- **Cross-Protocol**: Configurations spanning multiple AMBA protocols
- **Real-time Control**: Dynamic configuration changes during test execution

This architecture provides a solid foundation for comprehensive AMBA protocol verification while maintaining the flexibility to adapt to evolving verification requirements.