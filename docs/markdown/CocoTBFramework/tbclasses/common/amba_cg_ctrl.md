# AMBA Clock Gate Controller

## Overview

The `amba_cg_ctrl` module provides a testbench class for verifying AMBA clock gating controllers. Clock gating is a power-saving technique that disables the clock to inactive parts of a design. This module helps test that clock gating activates and deactivates correctly based on bus activity signals, with proper timing and control.

## Class Definition

```python
class AxiClockGateCtrl(TBBase):
    """
    Generic AXI Clock Gate Controller class.

    Controls clock gating based on activity from multiple valid signals
    on both user and AXI interface sides.
    """

    def __init__(self, dut, clock_gate_prefix="", user_valid_signals=None, axi_valid_signals=None):
        """
        Initialize the AXI Clock Gate Controller.

        Args:
            dut: Device under test
            clock_gate_prefix: Signal prefix for the clock gate control module
            user_valid_signals: List of user-side valid signal names
            axi_valid_signals: List of AXI-side valid signal names
        """
        super().__init__(dut)

        # Store parameters
        self.dut = dut
        self.prefix = clock_gate_prefix

        # Default empty lists if not provided
        self.user_valid_signals = user_valid_signals or []
        self.axi_valid_signals = axi_valid_signals or []

        # Store the full paths to the user and AXI valid signals
        self.user_valid_paths = []
        self.axi_valid_paths = []

        # Register signal paths
        self._register_signals()

        # Track current state
        self.is_enabled = False
        self.idle_count = 0
        self.is_gated = False
        self.is_idle = False
```

## Key Features

- Automatic detection and registration of valid signals
- Controlling clock gating enable/disable
- Setting idle count threshold for gating activation
- Monitoring activity on valid signals
- Measuring gating efficiency
- Forcing wakeup for testing
- Waiting for idle/gated states

## Primary Methods

### enable_clock_gating

Enables or disables clock gating functionality.

```python
def enable_clock_gating(self, enable=True):
    """
    Enable or disable clock gating.

    Args:
        enable: True to enable clock gating, False to disable
    """
    # Implementation...
```

### set_idle_count

Sets the idle count threshold for clock gating.

```python
def set_idle_count(self, count):
    """
    Set the idle count threshold for clock gating.

    Args:
        count: Number of idle cycles before clock gating is activated
    """
    # Implementation...
```

### monitor_activity

Monitors activity on valid signals for a specified duration.

```python
async def monitor_activity(self, duration=1000, units='ns'):
    """
    Monitor activity on valid signals for a specified duration.

    Args:
        duration: Duration to monitor
        units: Time units for duration

    Returns:
        Dict with activity statistics
    """
    # Implementation...
```

### get_current_state

Gets the current state of the clock gate controller.

```python
def get_current_state(self):
    """
    Get the current state of the clock gate controller.

    Returns:
        Dict with current state information
    """
    # Implementation...
```

### force_wakeup

Forces a wakeup by temporarily asserting user valid signals.

```python
def force_wakeup(self):
    """
    Force a wakeup by temporarily asserting all user valid signals.
    This is useful for testing or ensuring the clock is active.
    """
    # Implementation...
```

### wait_for_idle

Waits for the controller to enter idle state.

```python
async def wait_for_idle(self, timeout=1000, units='ns'):
    """
    Wait for the controller to enter idle state.

    Args:
        timeout: Maximum time to wait
        units: Time units for timeout

    Returns:
        True if idle state was reached, False if timeout
    """
    # Implementation...
```

### wait_for_gating

Waits for the controller to enter gated state.

```python
async def wait_for_gating(self, timeout=1000, units='ns'):
    """
    Wait for the controller to enter gated state.

    Args:
        timeout: Maximum time to wait
        units: Time units for timeout

    Returns:
        True if gated state was reached, False if timeout
    """
    # Implementation...
```

## Test Methodology

The AMBA clock gate controller testing approach includes:

1. **Signal Detection**: Automatically detect and register valid signals
2. **Configuration Testing**: Verify enable/disable and idle count configuration
3. **Activity Monitoring**: Measure activity on monitored signals
4. **Gating Efficiency**: Analyze percentage of time clock is gated
5. **Wake/Sleep Transitions**: Test transitions between active and gated states

The controller tracks and reports detailed statistics:

```python
stats = {
    'total_cycles': 0,
    'active_cycles': 0,
    'gated_cycles': 0,
    'user_active_cycles': 0,
    'axi_active_cycles': 0
}

# Calculate percentages
if stats['total_cycles'] > 0:
    stats['active_percent'] = (stats['active_cycles'] / stats['total_cycles']) * 100
    stats['gated_percent'] = (stats['gated_cycles'] / stats['total_cycles']) * 100
    stats['user_active_percent'] = (stats['user_active_cycles'] / stats['total_cycles']) * 100
    stats['axi_active_percent'] = (stats['axi_active_cycles'] / stats['total_cycles']) * 100
```

## Implementation Approach

The implementation monitors valid signals and tracks idle/gating state:

```python
# Check user valid signals
user_active = any(signal.value == 1 for signal in self.user_valid_paths if hasattr(signal, 'value'))
if user_active:
    stats['user_active_cycles'] += 1

# Check AXI valid signals
axi_active = any(signal.value == 1 for signal in self.axi_valid_paths if hasattr(signal, 'value'))
if axi_active:
    stats['axi_active_cycles'] += 1

# Overall activity
if user_active or axi_active:
    stats['active_cycles'] += 1

# Track gating if signal available
if gating_signal and gating_signal.value == 1:
    stats['gated_cycles'] += 1
    self.is_gated = True
else:
    self.is_gated = False

# Track idle state if signal available
if idle_signal:
    self.is_idle = (idle_signal.value == 1)
```

## Example Usage

Basic usage of the AMBA clock gate controller:

```python
from CocoTBFramework.tbclasses.common.amba_cg_ctrl import AxiClockGateCtrl

@cocotb.test()
async def test_clock_gating(dut):
    # Create controller with AXI valid signals
    clock_gate = AxiClockGateCtrl(
        dut,
        clock_gate_prefix="cg_",
        user_valid_signals=["s_axi_arvalid", "s_axi_rvalid"],
        axi_valid_signals=["m_axi_arvalid", "m_axi_rvalid"]
    )
    
    # Configure controller
    clock_gate.enable_clock_gating(True)
    clock_gate.set_idle_count(8)
    
    # Monitor activity
    stats = await clock_gate.monitor_activity(1000, 'ns')
    print(f"Active: {stats['active_percent']}%, Gated: {stats['gated_percent']}%")
    
    # Wait for gated state
    is_gated = await clock_gate.wait_for_gating(timeout=1000, units='ns')
    if is_gated:
        print("Clock is now gated")
    
    # Force wakeup for testing
    saved_values = clock_gate.force_wakeup()
    
    # Restore original values
    clock_gate.restore_signals(saved_values)
```

Using activity monitoring to measure efficiency:

```python
@cocotb.test()
async def test_clock_gating_efficiency(dut):
    # Create controller with AMBA valid signals
    clock_gate = AxiClockGateCtrl(dut, clock_gate_prefix="cg_")
    
    # Auto-detect valid signals
    user_valids = ["s_axi_awvalid", "s_axi_wvalid", "s_axi_arvalid"]
    axi_valids = ["m_axi_bvalid", "m_axi_rvalid"]
    
    for signal in user_valids:
        if hasattr(dut, signal):
            clock_gate.user_valid_signals.append(signal)
            
    for signal in axi_valids:
        if hasattr(dut, signal):
            clock_gate.axi_valid_signals.append(signal)
    
    clock_gate._register_signals()
    
    # Enable and configure
    clock_gate.enable_clock_gating(True)
    clock_gate.set_idle_count(16)
    
    # Run test stimulus (sending transactions)
    # ...
    
    # Measure efficiency
    stats = await clock_gate.monitor_activity(10000, 'ns')
    
    # Report results
    print(f"Clock Gating Efficiency Report:")
    print(f"  Total cycles: {stats['total_cycles']}")
    print(f"  Active cycles: {stats['active_cycles']} ({stats['active_percent']:.1f}%)")
    print(f"  Gated cycles: {stats['gated_cycles']} ({stats['gated_percent']:.1f}%)")
    print(f"  User activity: {stats['user_active_cycles']} ({stats['user_active_percent']:.1f}%)")
    print(f"  AXI activity: {stats['axi_active_cycles']} ({stats['axi_active_percent']:.1f}%)")
```

## Implementation Notes

- DUT signals use customizable prefixes via clock_gate_prefix parameter
- Support for both user-side and AXI-side valid signals
- Handles missing signals gracefully
- Provides comprehensive activity statistics
- Waits for state transitions with proper timeout handling
- Supports force wakeup with signal value preservation

## Clock Gating Control Signals

The standard control signals for AMBA clock gating:

- **i_cfg_cg_enable**: Enables/disables clock gating functionality
- **i_cfg_cg_idle_count**: Cycles to wait before activating gating
- **o_gating**: Indicates clock is currently gated (output)
- **o_idle**: Indicates module is currently idle (output)

## See Also

- [APB Components](../../components/apb/index.md) - APB protocol components
- [AXI4 Components](../../components/axi4/index.md) - AXI4 protocol components

## Navigation

[↑ Common Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
