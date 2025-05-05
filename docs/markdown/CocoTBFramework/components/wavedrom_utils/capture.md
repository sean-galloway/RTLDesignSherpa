# Capture

## Overview

The `capture` module provides utilities for efficiently managing waveform data capture during CocoTB simulations. It offers various capture modes, automatic resource management, and performance optimizations to ensure efficient waveform generation even for long-running simulations.

## Features

- Multiple capture modes (continuous, time-window, trigger-based, scenario-based)
- Automatic pause and resume capability
- Efficient resource management to prevent memory issues
- Periodic checking and statistics gathering
- Automatic saving of intermediate results
- Performance monitoring and optimization
- Multiple utility functions for common capture configurations

## Classes

### CaptureConfig

A dataclass for configuring the waveform capture process.

```python
@dataclass
class CaptureConfig:
    """Configuration for waveform capture process"""
    sample_interval_ns: int = 0  # 0 = Every clock cycle
    max_execution_time_s: int = 0  # 0 = No limit
    max_cycles: int = 0  # 0 = No limit
    periodic_checks_interval: int = 50  # Run checks every N cycles
    enable_statistics: bool = True
    periodic_save: bool = False
    save_interval_cycles: int = 1000
    output_format: str = "json"  # "json" or "html"
    debug_level: int = 1  # 0=None, 1=Basic, 2=Detailed, 3=Verbose
```

### CaptureMode

An enum class defining the capture modes for waveform data.

```python
class CaptureMode(Enum):
    """Capture modes for waveform data"""
    CONTINUOUS = 1  # Capture continuously until stopped
    TIME_WINDOW = 2  # Capture for a specific time window
    TRIGGER_BASED = 3  # Capture based on trigger conditions
    SCENARIO_BASED = 4  # Capture based on verification scenarios
```

### WaveformCapture

The main class for managing waveform capture during simulations.

#### Constructor

```python
def __init__(self, dut, container: WaveformContainer, config: CaptureConfig = None):
    """
    Initialize the waveform capture
    
    Args:
        dut: Device under test
        container: WaveformContainer instance
        config: Optional capture configuration
    """
```

#### Key Methods

```python
async def start_capture(self, mode: CaptureMode = CaptureMode.CONTINUOUS, 
                      duration_ns: int = None, trigger: SignalEvent = None):
    """
    Start waveform capture with the specified mode
    
    Args:
        mode: Capture mode
        duration_ns: Duration for TIME_WINDOW mode
        trigger: Trigger event for TRIGGER_BASED mode
    """
```

```python
async def stop_capture(self):
    """Stop the capture process"""
```

```python
async def pause_capture(self):
    """Pause the capture process"""
```

```python
async def resume_capture(self):
    """Resume the capture process"""
```

```python
async def run_continuous_capture(self, duration_ns: Optional[int] = None):
    """
    Run continuous waveform capture
    
    Args:
        duration_ns: Optional duration in nanoseconds
    """
```

```python
async def run_scenario_capture(self):
    """Run capture based on verification scenarios in the container"""
```

```python
def get_capture_stats(self) -> Dict[str, Any]:
    """
    Get statistics about the capture process
    
    Returns:
        Dictionary of capture statistics
    """
```

## Utility Functions

### create_standard_capture

Creates a standard waveform capture instance.

```python
def create_standard_capture(dut, container: WaveformContainer) -> WaveformCapture:
    """
    Create a standard waveform capture instance
    
    Args:
        dut: Device under test
        container: WaveformContainer instance
        
    Returns:
        WaveformCapture instance
    """
```

### create_debug_capture

Creates a debug waveform capture instance with verbose output.

```python
def create_debug_capture(dut, container: WaveformContainer) -> WaveformCapture:
    """
    Create a debug waveform capture instance with verbose output
    
    Args:
        dut: Device under test
        container: WaveformContainer instance
        
    Returns:
        WaveformCapture instance
    """
```

### create_performance_capture

Creates a performance-optimized waveform capture instance.

```python
def create_performance_capture(dut, container: WaveformContainer, max_cycles: int) -> WaveformCapture:
    """
    Create a performance-optimized waveform capture instance
    
    Args:
        dut: Device under test
        container: WaveformContainer instance
        max_cycles: Maximum number of cycles to capture
        
    Returns:
        WaveformCapture instance
    """
```

## Example Usage

### Basic Continuous Capture

```python
from CocoTBFramework.components.wavedrom_utils import (
    WaveformContainer, ScenarioConfig, SignalEvent, SignalRelation, EdgeType
)
from CocoTBFramework.components.wavedrom_utils.capture import (
    WaveformCapture, CaptureMode, create_standard_capture
)

@cocotb.test()
async def test_protocol(dut):
    # Create container with scenarios
    container = WaveformContainer(
        title="Protocol Verification",
        clock_signal="clk",
        signal_groups={"Control": ["clk", "rst_n"], "Data": ["valid", "ready", "data"]},
        scenarios=[protocol_scenario]
    )
    
    # Create and start capture
    capture = create_standard_capture(dut, container)
    await capture.start_capture(CaptureMode.CONTINUOUS)
    
    # Run test sequence
    # ... test code here ...
    
    # Stop capture and generate output
    await capture.stop_capture()
    container.generate_wavedrom("protocol_verification.json")
```

### Time-Window Capture

```python
# Create capture with 1000ns window
capture = WaveformCapture(dut, container)
await capture.start_capture(CaptureMode.TIME_WINDOW, duration_ns=1000)

# Simulation will automatically stop after 1000ns
```

### Trigger-Based Capture

```python
# Create trigger event (rising edge on 'valid')
trigger = SignalEvent("valid", EdgeType.RISING)

# Create capture with trigger
capture = WaveformCapture(dut, container)
await capture.start_capture(CaptureMode.TRIGGER_BASED, trigger=trigger)

# Will add annotations when trigger is detected
```

### Scenario-Based Capture

```python
# Create container with scenarios
container = WaveformContainer(
    title="Protocol Verification",
    clock_signal="clk",
    signal_groups=signal_groups,
    scenarios=[protocol_scenario, state_scenario]
)

# Create and start scenario-based capture
capture = WaveformCapture(dut, container)
await capture.start_capture(CaptureMode.SCENARIO_BASED)

# Will automatically run all scenarios in the container
```

### Custom Configuration

```python
# Create custom configuration
config = CaptureConfig(
    sample_interval_ns=0,    # Every clock cycle
    max_cycles=10000,        # Stop after 10,000 cycles
    periodic_checks_interval=100,
    enable_statistics=True,
    periodic_save=True,
    save_interval_cycles=1000,
    output_format="html",
    debug_level=2
)

# Create capture with custom config
capture = WaveformCapture(dut, container, config)
await capture.start_capture()
```

### Using Debug Capture

```python
# Create debug capture with verbose output
capture = create_debug_capture(dut, container)
await capture.start_capture()

# Will provide detailed output with periodic saves
```

### Pausing and Resuming Capture

```python
# Start capture
capture = create_standard_capture(dut, container)
await capture.start_capture()

# Pause capture during uninteresting sections
await capture.pause_capture()

# ... simulate uninteresting section ...

# Resume capture for important sections
await capture.resume_capture()
```

## Capture Modes

### CONTINUOUS Mode

Captures waveform data continuously until explicitly stopped or a configured limit is reached.

```python
await capture.start_capture(CaptureMode.CONTINUOUS)
```

### TIME_WINDOW Mode

Captures waveform data for a specific time window and then automatically stops.

```python
await capture.start_capture(CaptureMode.TIME_WINDOW, duration_ns=5000)
```

### TRIGGER_BASED Mode

Captures waveform data and adds annotations when specified trigger events are detected.

```python
trigger = SignalEvent("valid", EdgeType.RISING, value=1)
await capture.start_capture(CaptureMode.TRIGGER_BASED, trigger=trigger)
```

### SCENARIO_BASED Mode

Automatically runs all scenarios in the container and captures waveform data during their execution.

```python
await capture.start_capture(CaptureMode.SCENARIO_BASED)
```

## Periodic Checking and Saving

The capture module includes features for periodic operations:

### Periodic Checks

Configured through `periodic_checks_interval`, these run periodically to:
- Update capture statistics
- Check for trigger conditions
- Log debug information

### Periodic Saving

When `periodic_save` is enabled, the capture will automatically save intermediate results:
- Saves occur every `save_interval_cycles` cycles
- Files include cycle count in the filename
- Format depends on `output_format` setting

## Resource Management

The capture module includes features to manage resources efficiently:

### Memory Limiting

By setting `max_cycles`, the capture will automatically stop after a specified number of cycles to prevent excessive memory usage.

### Execution Time Limiting

By setting `max_execution_time_s`, the capture will automatically stop after a specified number of seconds to prevent runaway simulations.

### Statistics Collection

The `get_capture_stats()` method provides information about resource usage:
- Cycles captured
- Execution time
- Events detected
- Event history size
- Capture rate (cycles per second)

## Implementation Notes

- The capture task runs asynchronously using cocotb's `start_soon`
- All capture operations are non-blocking
- Resource statistics are updated in real-time
- Errors during capture are logged but do not terminate the simulation
- The module uses asyncio locks to prevent concurrent access issues

## Best Practices

1. **Choose the Right Mode**: Select the capture mode that best fits your verification needs
2. **Set Resource Limits**: Always set `max_cycles` or `max_execution_time_s` for long-running simulations
3. **Use Periodic Saving**: Enable periodic saving for long simulations to preserve intermediate results
4. **Pause During Initialization**: Consider pausing capture during initialization/reset sequences
5. **Monitor Performance**: Check capture stats periodically to ensure efficient operation
6. **Use Factory Functions**: Use the provided utility functions for common capture configurations

## See Also

- [Container](container.md) - Container for managing verification scenarios
- [Generator](generator.md) - Base WaveDrom generator
- [Enhanced Generator](enhanced_generator.md) - Extended generator with advanced features
- [Protocol Checks](protocol_checks.md) - Standard protocol checks
- [Models](models.md) - Signal event and relationship models

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
