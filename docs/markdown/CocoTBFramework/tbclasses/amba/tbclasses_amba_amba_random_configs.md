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

# amba_random_configs.py

Predefined randomization configurations for APB, AXI, and other AMBA protocols that provide consistent and reproducible randomization patterns for verification scenarios.

## Overview

The `amba_random_configs.py` module contains predefined randomization configurations that standardize test stimulus generation across AMBA protocol verification. These configurations provide consistent timing behaviors, enable reproducible tests, and support various verification scenarios from high-performance to error injection.

### Key Features
- **Protocol-specific configurations**: Optimized for APB Master, APB Slave, and AXI protocols
- **Scenario-based patterns**: Configurations tailored for specific test scenarios
- **Weighted randomization**: Precise control over timing distribution patterns
- **Reproducible results**: Consistent behavior across test runs and teams
- **Easy integration**: Direct compatibility with FlexRandomizer and protocol components

## Configuration Format

All configurations use a consistent tuple-based format for defining randomization behavior:

```python
'field_name': (ranges, weights)
```

Where:
- **ranges**: List of (min, max) tuples defining value ranges
- **weights**: List of weights corresponding to each range (higher = more likely)

## APB Master Configurations

### APB_MASTER_RANDOMIZER_CONFIGS

Configurations for APB master timing behavior affecting `psel` and `penable` signal delays.

#### 'fixed'
Deterministic behavior with no randomization.
```python
'fixed': {
    'psel': ([(1, 1)], [1]),      # Always 1 cycle delay
    'penable': ([(1, 1)], [1])    # Always 1 cycle delay
}
```
**Use Cases:** Deterministic testing, protocol compliance verification, debug scenarios

#### 'constrained'
Balanced randomization with controlled timing variations.
```python
'constrained': {
    'psel': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),     # Mostly 0-5 cycles
    'penable': ([(0, 0), (1, 3)], [3, 1])               # Mostly immediate
}
```
**Use Cases:** General verification, realistic traffic patterns, performance testing

#### 'fast'
Optimized for high-throughput scenarios with minimal delays.
```python
'fast': {
    'psel': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0]),     # Heavily biased to 0 cycles
    'penable': ([(0, 0), (1, 3)], [3, 0])               # Always immediate
}
```
**Use Cases:** High-throughput testing, performance benchmarking, bandwidth validation

#### 'backtoback'
Zero-delay configuration for maximum throughput testing.
```python
'backtoback': {
    'psel': ([(0, 0)], [1]),      # No delay
    'penable': ([(0, 0)], [1])    # No delay
}
```
**Use Cases:** Maximum bandwidth testing, pipeline validation, worst-case scenarios

#### 'burst_pause'
Bursty traffic pattern with periods of activity and idle time.
```python
'burst_pause': {
    'psel': ([(0, 0), (5, 10)], [8, 1]),     # Mostly immediate, occasional pauses
    'penable': ([(0, 0), (2, 5)], [8, 1])    # Mostly immediate, short pauses
}
```
**Use Cases:** Realistic system traffic, power testing, cache behavior validation

#### 'slow_master'
Slow master behavior for timing verification.
```python
'slow_master': {
    'psel': ([(5, 15)], [1]),     # 5-15 cycle delays
    'penable': ([(3, 8)], [1])    # 3-8 cycle delays
}
```
**Use Cases:** Timing margin testing, slow peripheral simulation, debug scenarios

## APB Slave Configurations

### APB_SLAVE_RANDOMIZER_CONFIGS

Configurations for APB slave response behavior affecting `ready` and `error` signal timing.

#### 'fixed'
Deterministic slave response with no errors.
```python
'fixed': {
    'ready': ([(1, 1)], [1]),     # Always ready after 1 cycle
    'error': ([(0, 0)], [1])      # Never assert error
}
```
**Use Cases:** Basic functional testing, protocol compliance, deterministic scenarios

#### 'constrained'
Balanced slave behavior with occasional delays.
```python
'constrained': {
    'ready': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),   # Mostly quick response
    'error': ([(0, 0), (1, 1)], [10, 0])               # No errors
}
```
**Use Cases:** General verification, realistic peripheral behavior, performance testing

#### 'fast'
High-performance slave with immediate responses.
```python
'fast': {
    'ready': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0]),   # Immediate response bias
    'error': ([(0, 0)], [1])                            # No errors
}
```
**Use Cases:** High-performance testing, fast peripheral simulation, throughput validation

#### 'backtoback'
Zero-wait-state slave for maximum throughput.
```python
'backtoback': {
    'ready': ([(0, 0)], [1]),     # Always ready immediately
    'error': ([(0, 0)], [1])      # No errors
}
```
**Use Cases:** Maximum throughput testing, ideal peripheral behavior, best-case scenarios

#### 'burst_pause'
Slave with bursty response patterns.
```python
'burst_pause': {
    'ready': ([(0, 0), (8, 15)], [8, 1]),   # Quick response or longer pause
    'error': ([(0, 0)], [1])                # No errors
}
```
**Use Cases:** Cache-like behavior, memory controller testing, realistic system patterns

#### 'slow_consumer'
Slow peripheral simulation with extended ready delays.
```python
'slow_consumer': {
    'ready': ([(8, 20)], [1]),    # Always slow (8-20 cycles)
    'error': ([(0, 0)], [1])      # No errors
}
```
**Use Cases:** Slow peripheral testing, timing verification, worst-case analysis

#### 'error_injection'
Configuration for testing error handling paths.
```python
'error_injection': {
    'ready': ([(0, 2)], [1]),               # Quick response for error testing
    'error': ([(0, 0), (1, 1)], [8, 2])    # 20% error rate
}
```
**Use Cases:** Error handling verification, robustness testing, fault injection

## AXI Configurations

### AXI_RANDOMIZER_CONFIGS

Configurations for AXI protocol timing affecting master valid delays and slave ready delays.

#### 'fixed'
Deterministic AXI timing.
```python
'fixed': {
    'master': {'valid_delay': ([(1, 1)], [1])},    # Master always 1 cycle
    'slave': {'ready_delay': ([(1, 1)], [1])}      # Slave always 1 cycle
}
```

#### 'constrained'
Balanced AXI timing with controlled variations.
```python
'constrained': {
    'master': {'valid_delay': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1])},
    'slave': {'ready_delay': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1])}
}
```

#### 'fast'
High-performance AXI timing.
```python
'fast': {
    'master': {'valid_delay': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0])},
    'slave': {'ready_delay': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0])}
}
```

#### 'backtoback'
Zero-delay AXI for maximum bandwidth.
```python
'backtoback': {
    'master': {'valid_delay': ([(0, 0)], [1])},
    'slave': {'ready_delay': ([(0, 0)], [1])}
}
```

#### 'burst_pause'
Bursty AXI traffic patterns.
```python
'burst_pause': {
    'master': {'valid_delay': ([(0, 0), (10, 20)], [8, 1])},
    'slave': {'ready_delay': ([(0, 0), (12, 25)], [8, 1])}
}
```

#### 'slow_producer'
Slow AXI components for timing verification.
```python
'slow_producer': {
    'master': {'valid_delay': ([(8, 20)], [1])},
    'slave': {'ready_delay': ([(8, 20)], [1])}
}
```

#### 'high_throughput'
Optimized for maximum AXI throughput.
```python
'high_throughput': {
    'master': {'valid_delay': ([(0, 1)], [1])},
    'slave': {'ready_delay': ([(0, 1)], [1])}
}
```

## Usage Patterns

### Basic Configuration Application

```python
from CocoTBFramework.tbclasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)

# Apply APB master configuration
master_config = APB_MASTER_RANDOMIZER_CONFIGS['constrained']
master_randomizer.load_config(master_config)

# Apply APB slave configuration
slave_config = APB_SLAVE_RANDOMIZER_CONFIGS['fast']
slave_randomizer.load_config(slave_config)

# Apply AXI configuration
axi_config = AXI_RANDOMIZER_CONFIGS['high_throughput']
axi_randomizer.load_config(axi_config)
```

### Scenario-Based Testing

```python
class ScenarioTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut, "ScenarioTest")
        self.master_randomizer = self.create_master_randomizer()
        self.slave_randomizer = self.create_slave_randomizer()
    
    async def run_high_performance_scenario(self):
        """High-performance test scenario"""
        self.master_randomizer.load_config(
            APB_MASTER_RANDOMIZER_CONFIGS['fast']
        )
        self.slave_randomizer.load_config(
            APB_SLAVE_RANDOMIZER_CONFIGS['backtoback']
        )
        
        await self.run_transaction_sequence(count=1000)
        
    async def run_power_efficiency_scenario(self):
        """Power-aware test scenario with bursty traffic"""
        self.master_randomizer.load_config(
            APB_MASTER_RANDOMIZER_CONFIGS['burst_pause']
        )
        self.slave_randomizer.load_config(
            APB_SLAVE_RANDOMIZER_CONFIGS['burst_pause']
        )
        
        # Monitor power during test
        power_stats = await self.monitor_power()
        await self.run_transaction_sequence(count=500)
        
    async def run_robustness_scenario(self):
        """Error injection and slow timing scenario"""
        self.master_randomizer.load_config(
            APB_MASTER_RANDOMIZER_CONFIGS['slow_master']
        )
        self.slave_randomizer.load_config(
            APB_SLAVE_RANDOMIZER_CONFIGS['error_injection']
        )
        
        await self.run_transaction_sequence(count=200)
        # Verify error handling worked correctly
```

### Configuration Sweeping

```python
async def run_configuration_sweep(self, protocols=['APB', 'AXI']):
    """Test all configuration combinations"""
    results = {}
    
    if 'APB' in protocols:
        master_configs = APB_MASTER_RANDOMIZER_CONFIGS.keys()
        slave_configs = APB_SLAVE_RANDOMIZER_CONFIGS.keys()
        
        for master_config in master_configs:
            for slave_config in slave_configs:
                config_name = f"APB_{master_config}_{slave_config}"
                
                self.log.info(f"Testing configuration: {config_name}")
                
                # Apply configurations
                self.master_randomizer.load_config(
                    APB_MASTER_RANDOMIZER_CONFIGS[master_config]
                )
                self.slave_randomizer.load_config(
                    APB_SLAVE_RANDOMIZER_CONFIGS[slave_config]
                )
                
                # Run test
                result = await self.run_test_sequence()
                results[config_name] = result
    
    return results
```

### Integration with Clock Gating

```python
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl

class PowerAwareRandomTest(TBBase):
    def __init__(self, dut):
        super().__init__(dut, "PowerTest")
        self.clock_gate = AxiClockGateCtrl(dut, ...)
        self.setup_randomizers()
    
    async def run_power_optimized_test(self):
        """Test power efficiency with appropriate randomization"""
        
        # Use burst pause for realistic power behavior
        self.master_randomizer.load_config(
            APB_MASTER_RANDOMIZER_CONFIGS['burst_pause']
        )
        
        # Configure clock gating for bursty traffic
        self.clock_gate.set_idle_count(4)
        self.clock_gate.enable_clock_gating(True)
        
        # Run test with power monitoring
        power_task = cocotb.start_soon(
            self.clock_gate.monitor_activity(10000, 'ns')
        )
        test_task = cocotb.start_soon(
            self.run_transaction_sequence(500)
        )
        
        await test_task
        power_stats = await power_task
        
        # Validate power efficiency
        assert power_stats['gated_percent'] > 20
        
        return power_stats
```

### Custom Configuration Creation

```python
# Create custom configurations following the same pattern
CUSTOM_APB_CONFIGS = {
    'debug_mode': {
        'psel': ([(10, 20)], [1]),    # Very slow for debugging
        'penable': ([(5, 10)], [1])   # Slow enables
    },
    
    'stress_test': {
        'psel': ([(0, 0), (50, 100)], [1, 1]),    # Either immediate or very slow
        'penable': ([(0, 0), (25, 50)], [1, 1])   # Bimodal distribution
    }
}

# Register with existing configurations
APB_MASTER_RANDOMIZER_CONFIGS.update(CUSTOM_APB_CONFIGS)
```

## Configuration Selection Guidelines

### High Performance Testing
- **Master**: 'fast' or 'backtoback'
- **Slave**: 'fast' or 'backtoback'
- **AXI**: 'high_throughput' or 'backtoback'

### Power Efficiency Testing
- **Master**: 'burst_pause'
- **Slave**: 'burst_pause' 
- **AXI**: 'burst_pause'

### Robustness Testing
- **Master**: 'slow_master' or 'constrained'
- **Slave**: 'error_injection' or 'slow_consumer'
- **AXI**: 'slow_producer'

### Debug and Development
- **Master**: 'fixed'
- **Slave**: 'fixed'
- **AXI**: 'fixed'

### General Verification
- **Master**: 'constrained'
- **Slave**: 'constrained'
- **AXI**: 'constrained'

## Best Practices

1. **Start with 'fixed' configurations** for initial functional verification
2. **Use 'constrained' for general testing** to cover realistic scenarios
3. **Apply 'fast' configurations** when validating high-performance paths
4. **Combine 'burst_pause' with power monitoring** for realistic power analysis
5. **Use 'error_injection' systematically** to verify error handling
6. **Document configuration choices** in test plans and results
7. **Create custom configurations** for specific test requirements
8. **Validate configuration effectiveness** through coverage analysis

## Integration Notes

- **Compatible with FlexRandomizer**: Direct integration with the randomization engine
- **Protocol independent format**: Same structure works across all AMBA protocols
- **Extensible design**: Easy to add new configurations or protocols
- **Team consistency**: Standardized configurations across verification teams
- **Reproducible testing**: Consistent behavior with proper seed management

The randomization configurations provide a solid foundation for comprehensive AMBA protocol verification, enabling teams to achieve consistent, reproducible, and thorough testing across various scenarios and performance requirements.