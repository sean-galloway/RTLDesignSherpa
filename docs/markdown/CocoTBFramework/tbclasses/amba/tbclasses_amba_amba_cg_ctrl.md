# amba_cg_ctrl.py

Generic AXI Clock Gate Controller for managing clock gating based on AXI protocol activity with support for multiple valid signals from both user and interface sides.

## Overview

The `amba_cg_ctrl.py` module provides the `AxiClockGateCtrl` class, which enables intelligent clock gating management for AMBA protocols. It monitors activity on multiple valid signals from both user-side and AXI interface sides to make optimal clock gating decisions.

### Key Features
- **Multi-signal monitoring**: Tracks activity on user and AXI valid signals simultaneously
- **Configurable thresholds**: Adjustable idle count for gating decisions
- **Real-time statistics**: Comprehensive activity monitoring and power efficiency reporting
- **Protocol flexibility**: Works with any AXI-based implementation
- **Debug support**: Force wakeup and signal restore capabilities

## Class Definition

### AxiClockGateCtrl

Main class for controlling AXI clock gating based on protocol activity.

#### Constructor

```python
AxiClockGateCtrl(
    dut, 
    instance_path="", 
    clock_signal_name="clk_in", 
    user_valid_signals=None, 
    axi_valid_signals=None
)
```

**Parameters:**
- `dut`: Device under test (CocoTB DUT object)
- `instance_path`: Path to the clock gate controller instance (e.g., "i_amba_clock_gate_ctrl")
- `clock_signal_name`: Name of the clock signal (default: "clk_in")
- `user_valid_signals`: List of user-side valid signal names
- `axi_valid_signals`: List of AXI-side valid signal names

```python
# Basic setup
clock_gate = AxiClockGateCtrl(
    dut,
    instance_path="dut.clock_gate_ctrl",
    clock_signal_name="clk",
    user_valid_signals=["s_axi_arvalid", "s_axi_awvalid"],
    axi_valid_signals=["m_axi_arvalid", "m_axi_awvalid"]
)

# Minimal setup
clock_gate = AxiClockGateCtrl(dut)
```

## Configuration Methods

### `enable_clock_gating(enable=True)`

Enable or disable clock gating functionality.

**Parameters:**
- `enable`: True to enable clock gating, False to disable

```python
# Enable clock gating
clock_gate.enable_clock_gating(True)

# Disable for debug
clock_gate.enable_clock_gating(False)
```

**Signal Controlled:** `i_cfg_cg_enable`

### `set_idle_count(count)`

Set the idle count threshold for clock gating activation.

**Parameters:**
- `count`: Number of idle cycles before clock gating is activated

```python
# Conservative gating (16 idle cycles)
clock_gate.set_idle_count(16)

# Aggressive gating (4 idle cycles)
clock_gate.set_idle_count(4)

# Minimal gating (2 idle cycles)
clock_gate.set_idle_count(2)
```

**Signal Controlled:** `i_cfg_cg_idle_count`

## Monitoring Methods

### `monitor_activity(duration=1000, units='ns')`

Monitor activity on valid signals for a specified duration and generate comprehensive statistics.

**Parameters:**
- `duration`: Duration to monitor (default: 1000)
- `units`: Time units for duration (default: 'ns')

**Returns:** Dictionary with detailed activity statistics

```python
# Monitor for 5 microseconds
stats = await clock_gate.monitor_activity(5000, 'ns')

# Example output
{
    'total_cycles': 500,
    'active_cycles': 320,
    'gated_cycles': 75,
    'user_active_cycles': 200,
    'axi_active_cycles': 180,
    'active_percent': 64.0,
    'gated_percent': 15.0,
    'user_active_percent': 40.0,
    'axi_active_percent': 36.0
}
```

**Statistics Explained:**
- `total_cycles`: Total clock cycles monitored
- `active_cycles`: Cycles with any valid signal active
- `gated_cycles`: Cycles where clock was gated
- `user_active_cycles`: Cycles with user-side activity
- `axi_active_cycles`: Cycles with AXI-side activity
- Percentages calculated as (count / total_cycles) * 100

## State Monitoring

### `get_current_state()`

Get the current state of the clock gate controller.

**Returns:** Dictionary with current state information

```python
state = clock_gate.get_current_state()

# Example output
{
    'enabled': True,
    'idle_count': 8,
    'is_gated': False,
    'is_idle': True
}
```

**State Fields:**
- `enabled`: Whether clock gating is enabled
- `idle_count`: Current idle count threshold
- `is_gated`: Current gating state (from `o_gating` signal)
- `is_idle`: Current idle state (from `o_idle` signal)

## Synchronization Methods

### `wait_for_idle(timeout=1000, units='ns')`

Wait for the controller to enter idle state.

**Parameters:**
- `timeout`: Maximum time to wait (default: 1000)
- `units`: Time units for timeout (default: 'ns')

**Returns:** True if idle state reached, False if timeout

```python
# Wait for idle with default timeout
idle_reached = await clock_gate.wait_for_idle()

# Wait with custom timeout
idle_reached = await clock_gate.wait_for_idle(2000, 'ns')

if idle_reached:
    print("System is now idle")
else:
    print("Timeout waiting for idle")
```

### `wait_for_gating(timeout=1000, units='ns')`

Wait for the controller to enter gated state.

**Parameters:**
- `timeout`: Maximum time to wait (default: 1000)
- `units`: Time units for timeout (default: 'ns')

**Returns:** True if gated state reached, False if timeout

```python
# Wait for clock gating to activate
gated = await clock_gate.wait_for_gating(5000, 'ns')

if gated:
    print("Clock is now gated")
    # Perform power measurements
else:
    print("Clock gating not activated")
```

## Debug and Control Methods

### `force_wakeup()`

Force a wakeup by temporarily asserting all user valid signals.

**Returns:** Dictionary mapping signal names to their original values

```python
# Force system wakeup for debugging
original_values = clock_gate.force_wakeup()

# Perform debug operations while awake
await debug_operations()

# Restore original state
clock_gate.restore_signals(original_values)
```

**Use Cases:**
- Debugging clock gating issues
- Ensuring system is awake for test operations
- Testing wakeup responsiveness

### `restore_signals(original_values)`

Restore signals to their original values after a forced wakeup.

**Parameters:**
- `original_values`: Dictionary from `force_wakeup()` call

```python
# Complete force/restore cycle
original = clock_gate.force_wakeup()
# ... perform operations while awake ...
clock_gate.restore_signals(original)
```

## Usage Patterns

### Basic Power Monitoring

```python
import cocotb
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl

@cocotb.test()
async def test_power_efficiency(dut):
    # Set up clock gate controller
    clock_gate = AxiClockGateCtrl(
        dut,
        instance_path="dut.cg_ctrl",
        user_valid_signals=["req_valid", "cmd_valid"],
        axi_valid_signals=["axi_arvalid", "axi_awvalid"]
    )
    
    # Configure for moderate gating
    clock_gate.enable_clock_gating(True)
    clock_gate.set_idle_count(8)
    
    # Run test and monitor power
    stats = await clock_gate.monitor_activity(10000, 'ns')
    
    # Validate power efficiency
    assert stats['gated_percent'] > 10, f"Poor gating efficiency: {stats['gated_percent']}%"
    assert stats['active_percent'] < 90, f"System too active: {stats['active_percent']}%"
    
    print(f"Power efficiency: {stats['gated_percent']:.1f}% gated")
```

### Advanced Power Analysis

```python
class PowerAnalysisTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut, "PowerAnalysis")
        
        self.clock_gate = AxiClockGateCtrl(
            dut,
            instance_path="dut.power_ctrl",
            user_valid_signals=self.get_user_signals(),
            axi_valid_signals=self.get_axi_signals()
        )
    
    async def run_power_sweep(self, idle_counts=[2, 4, 8, 16]):
        """Test different idle count settings"""
        results = {}
        
        for idle_count in idle_counts:
            self.clock_gate.set_idle_count(idle_count)
            
            # Run test scenario
            await self.run_test_sequence()
            
            # Measure power efficiency
            stats = await self.clock_gate.monitor_activity(5000, 'ns')
            results[idle_count] = stats
            
            self.log.info(f"Idle count {idle_count}: {stats['gated_percent']:.1f}% gated")
        
        return results
    
    async def validate_wakeup_latency(self):
        """Test system wakeup responsiveness"""
        # Force system to idle
        await self.clock_gate.wait_for_idle(timeout=1000)
        
        # Force wakeup and measure latency
        start_time = cocotb.utils.get_sim_time('ns')
        self.clock_gate.force_wakeup()
        
        # Wait for system to become active
        await self.wait_for_activity()
        
        end_time = cocotb.utils.get_sim_time('ns')
        latency = end_time - start_time
        
        self.log.info(f"Wakeup latency: {latency} ns")
        return latency
```

### Integration with Randomization

```python
from CocoTBFramework.tbclasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

class PowerAwareRandomTest(TBBase):
    def __init__(self, dut):
        super().__init__(dut, "PowerRandom")
        self.setup_clock_gating()
        
    async def run_randomized_power_test(self, config_name='burst_pause'):
        """Run randomized test with power monitoring"""
        
        # Apply randomization configuration
        config = AXI_RANDOMIZER_CONFIGS[config_name]
        self.apply_randomizer_config(config)
        
        # Enable appropriate power settings
        if 'burst' in config_name:
            self.clock_gate.set_idle_count(4)  # Quick gating for bursts
        else:
            self.clock_gate.set_idle_count(16) # Conservative gating
        
        # Run test with monitoring
        test_task = cocotb.start_soon(self.run_random_transactions())
        monitor_task = cocotb.start_soon(
            self.clock_gate.monitor_activity(20000, 'ns')
        )
        
        # Wait for completion
        await test_task
        stats = await monitor_task
        
        # Validate power and performance
        self.validate_results(stats, config_name)
        
        return stats
```

## Signal Hierarchy

The controller expects the following signal hierarchy:

### Control Signals (Inputs)
- `i_cfg_cg_enable`: Enable/disable clock gating
- `i_cfg_cg_idle_count`: Idle count threshold

### Status Signals (Outputs)  
- `o_gating`: Current gating state
- `o_idle`: Current idle state

### User Valid Signals (Configurable)
- Configurable list of user-side valid signals
- Typically: `s_axi_*valid`, `req_valid`, `cmd_valid`

### AXI Valid Signals (Configurable)
- Configurable list of AXI interface valid signals  
- Typically: `m_axi_*valid`, `axi_*valid`

## Best Practices

1. **Start with conservative idle counts** (16+ cycles) and reduce based on power requirements
2. **Monitor both user and AXI sides** to ensure complete activity tracking
3. **Use force_wakeup() sparingly** and always restore signals afterward
4. **Combine with randomization** to test realistic traffic patterns
5. **Validate wakeup latency** to ensure acceptable responsiveness
6. **Document signal mappings** for team understanding
7. **Test with clock gating disabled** for functional verification first

## Integration Notes

- **Inherits from TBBase**: Provides logging, error handling, and common infrastructure
- **Works with any AXI implementation**: Protocol-agnostic design
- **Supports hierarchical signal paths**: Flexible signal mapping
- **Compatible with randomization configs**: Integrates with `amba_random_configs.py`
- **Provides comprehensive statistics**: Enables data-driven power optimization

The `AxiClockGateCtrl` class provides a robust foundation for power-aware verification of AMBA protocols, enabling teams to validate clock gating implementations while maintaining comprehensive observability into system power behavior.