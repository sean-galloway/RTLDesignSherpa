# Enhanced Generator

## Overview

The `enhanced_generator` module extends the base WaveDrom generator with advanced features for pattern matching, statistical analysis, and enhanced visualization. It provides a more powerful and feature-rich alternative to the standard generator, while maintaining compatibility with the existing WaveDrom utilities.

## Features

- Advanced pattern detection and matching
- Signal statistics collection and analysis
- Enhanced visualization with HTML output
- Customizable debug annotations with severity levels
- Multiple output formats (JSON, HTML)
- Time-based and cycle-based annotations
- Highly configurable visualization options
- Auto-saving capabilities for long simulations

## Classes

### SignalAnalysisType

An enum class defining the types of signal analysis to perform.

```python
class SignalAnalysisType(Enum):
    """Types of signal analysis to perform"""
    TOGGLE_RATE = auto()       # Signal toggle frequency
    PULSE_WIDTH = auto()       # Width of signal pulses
    PATTERN_MATCH = auto()     # Match specific bit patterns
    STATISTICS = auto()        # Statistical analysis of values
    DEPENDENCIES = auto()      # Identify signal dependencies
    TIMING = auto()            # Measure timing metrics
```

### EnhancedWaveDromConfig

A dataclass for configuring the enhanced WaveDrom generator.

```python
@dataclass
class EnhancedWaveDromConfig:
    """Configuration for enhanced WaveDrom generator"""
    title: str = "WaveDrom Analysis"
    hscale: float = 1.0
    skin: str = "default"
    include_time_scale: bool = True
    auto_save: bool = False
    auto_save_format: str = "json"
    highlight_violations: bool = True
    max_history_size: int = 10000
    statistical_analysis: bool = False
    include_html_wrapper: bool = False
```

### EnhancedWaveDromGenerator

The main class for generating enhanced WaveDrom diagrams with additional features.

#### Constructor

```python
def __init__(self, clock, config: EnhancedWaveDromConfig = None):
    """
    Initialize enhanced WaveDrom generator
    
    Args:
        clock: Clock signal from DUT
        config: Optional configuration settings
    """
```

#### Key Attributes

- `clock`: Clock signal for synchronization
- `config`: Configuration settings
- `signals`: Dictionary of tracked signals and their values
- `relations`: List of signal relationships to monitor
- `detected_relations`: List of detected signal relationships
- `current_cycle`: Current simulation cycle
- `event_history`: List of detected signal events
- `debug_points`: List of debugging annotations
- `signal_statistics`: Dictionary of collected signal statistics
- `signal_patterns`: Dictionary of patterns to detect
- `annotations`: List of custom annotations
- `start_time`: Simulation start time

#### Key Methods

```python
def add_signal(self, name: str, dut_path: str, clock_domain: str = None, 
              analysis_types: List[SignalAnalysisType] = None):
    """
    Add a signal to track during simulation with enhanced analysis
    
    Args:
        name: Display name for the signal
        dut_path: Path to signal in DUT hierarchy
        clock_domain: Optional clock domain for the signal
        analysis_types: Optional list of analysis types to perform
    """
```

```python
def add_pattern(self, signal_name: str, pattern_name: str, pattern: Union[str, int, List],
               highlight_color: str = "red"):
    """
    Add a pattern to detect on a signal
    
    Args:
        signal_name: Name of the signal to monitor
        pattern_name: Name for this pattern
        pattern: Bit pattern as string, integer, or list of 0/1
        highlight_color: Color to use when highlighting pattern in output
    """
```

```python
def add_annotation(self, cycle: int, text: str, signals: Dict[str, Any] = None,
                 style: Dict[str, str] = None):
    """
    Add a custom annotation to the waveform
    
    Args:
        cycle: Clock cycle for the annotation
        text: Annotation text
        signals: Optional dict of signal values to associate
        style: Optional style settings like color, fontSize, etc.
    """
```

```python
async def sample(self):
    """
    Sample all signals and check for relationships
    
    Enhanced to track statistics and check for patterns
    """
```

```python
def add_debug_point(self, cycle: int, message: str, signals: Dict[str, Any], 
                  category: str = "violation", severity: str = "warning"):
    """
    Add an enhanced debugging annotation
    
    Args:
        cycle: Clock cycle for the annotation
        message: Debug message
        signals: Dict of signal values at this debug point
        category: Category of debug point (e.g., "violation", "info")
        severity: Severity level ("info", "warning", "error")
    """
```

```python
def get_signal_statistics(self, signal_name: str = None) -> Dict:
    """
    Get statistics for one or all signals
    
    Args:
        signal_name: Optional signal name, or None for all signals
        
    Returns:
        Dictionary of signal statistics
    """
```

```python
def generate(self, output_file: Optional[str] = None) -> Dict:
    """
    Generate enhanced WaveDrom JSON output
    
    Args:
        output_file: Optional path to save JSON output
        
    Returns:
        WaveDrom JSON configuration dictionary
    """
```

## Example Usage

### Basic Usage with Enhanced Features

```python
from CocoTBFramework.components.wavedrom_utils.enhanced_generator import (
    EnhancedWaveDromGenerator, EnhancedWaveDromConfig, SignalAnalysisType
)

@cocotb.test()
async def test_enhanced_waveform(dut):
    # Create configuration
    config = EnhancedWaveDromConfig(
        title="Protocol Analysis",
        hscale=1.5,
        statistical_analysis=True,
        include_html_wrapper=True,
        max_history_size=5000
    )
    
    # Create generator
    generator = EnhancedWaveDromGenerator(dut.clk, config)
    
    # Add signals with analysis types
    generator.add_signal("clk", "clk")
    generator.add_signal("reset", "rst_n")
    generator.add_signal("data", "data", analysis_types=[
        SignalAnalysisType.TOGGLE_RATE,
        SignalAnalysisType.STATISTICS
    ])
    generator.add_signal("valid", "valid")
    generator.add_signal("ready", "ready")
    
    # Run simulation for 100 cycles
    for _ in range(100):
        await generator.sample()
        
    # Generate HTML output with statistics
    generator.generate("protocol_analysis.html")
```

### Pattern Detection

```python
# Create generator
generator = EnhancedWaveDromGenerator(dut.clk)

# Add signals
generator.add_signal("clk", "clk")
generator.add_signal("data", "data")

# Add patterns to detect
generator.add_pattern("data", "all_ones", 0xFF)
generator.add_pattern("data", "alternating", "10101010")
generator.add_pattern("data", "sequence", [1, 0, 0, 1])

# Run simulation
for _ in range(100):
    await generator.sample()
    
# Check detected patterns
for pattern in generator.signal_patterns["data"]:
    print(f"Pattern {pattern['name']} found at cycles: {pattern['occurrences']}")
```

### Custom Annotations

```python
# Create generator
generator = EnhancedWaveDromGenerator(dut.clk)

# Add signals
generator.add_signal("clk", "clk")
generator.add_signal("state", "state")
generator.add_signal("data", "data")

# Run simulation
for cycle in range(100):
    await generator.sample()
    
    # Add custom annotations for state changes
    if dut.state.value != generator.get_last_value("state"):
        generator.add_annotation(
            cycle,
            f"State change to {dut.state.value}",
            {"state": dut.state.value},
            {"color": "green"}
        )
```

### Signal Statistics

```python
# Create configuration with statistics enabled
config = EnhancedWaveDromConfig(statistical_analysis=True)

# Create generator
generator = EnhancedWaveDromGenerator(dut.clk, config)

# Add signals
generator.add_signal("clk", "clk")
generator.add_signal("valid", "valid")
generator.add_signal("ready", "ready")

# Run simulation
for _ in range(100):
    await generator.sample()
    
# Get statistics for a specific signal
valid_stats = generator.get_signal_statistics("valid")
print(f"Valid toggle rate: {valid_stats['statistics']['toggle_rate']:.2f}")
print(f"Valid high percentage: {valid_stats['statistics']['time_high']:.1f}%")
```

### HTML Output with Statistics

```python
# Create configuration with HTML output
config = EnhancedWaveDromConfig(
    include_html_wrapper=True,
    statistical_analysis=True
)

# Create generator
generator = EnhancedWaveDromGenerator(dut.clk, config)

# Add signals and run simulation
# ...

# Generate HTML output with statistics table
generator.generate("waveform_with_stats.html")
```

## Pattern Matching Capabilities

The enhanced generator provides powerful pattern matching capabilities for detecting specific bit patterns in signals:

1. **Binary Patterns**: Detect specific binary sequences like "10110"
2. **Hexadecimal Values**: Detect specific values like 0xA5
3. **Bit Lists**: Detect patterns defined as lists of bits [1, 0, 1, 1, 0]

When a pattern is detected, it's recorded with:
- The cycle number where it was found
- Statistics on occurrence frequency
- Optional visual highlighting in the output

## Signal Statistics

The following statistics are collected for signals:

1. **Toggle Rate**: How frequently the signal changes state
2. **Time High/Low**: Percentage of time spent in high/low state
3. **Pulse Width**: Minimum and maximum pulse widths
4. **Pattern Occurrences**: Count of detected patterns
5. **Transition Counts**: Number of value changes

## HTML Output Format

The HTML output provides enhanced visualization with:

1. **Interactive WaveDrom Diagram**: Standard waveform display
2. **Signal Statistics Table**: Displaying collected metrics
3. **Debug Annotations Table**: Listing all detected issues
4. **Pattern Detection Summary**: Showing detected patterns
5. **Simulation Metadata**: Information about the simulation run

## Implementation Notes

- Pattern matching uses binary string comparison for efficiency
- Statistics are updated incrementally to minimize overhead
- HTML generation uses CDN-hosted WaveDrom libraries
- Annotations can be styled with custom colors and formatting
- Memory usage is controlled through configurable history size limits

## Advanced Configuration

### Scale and Appearance

```python
config = EnhancedWaveDromConfig(
    title="Detailed Protocol Analysis",
    hscale=2.0,  # Double width for better readability
    skin="default",  # WaveDrom skin
    include_time_scale=True  # Include time scale in display
)
```

### Auto-Saving

```python
config = EnhancedWaveDromConfig(
    auto_save=True,  # Enable auto-saving
    auto_save_format="html",  # Save as HTML
)
```

### Memory Management

```python
config = EnhancedWaveDromConfig(
    max_history_size=5000  # Limit event history to 5000 entries
)
```

## Best Practices

1. **Enable Statistics Selectively**: Only enable statistics for signals of interest
2. **Limit History Size**: Set appropriate max_history_size for long simulations
3. **Use Clock Domains**: Group signals by clock domain for multi-clock designs
4. **Pattern Precision**: Be specific with patterns to avoid false positives
5. **HTML for Final Reports**: Use JSON for intermediate saves, HTML for final reports
6. **Categories and Severities**: Use consistent categories and severities for debug points

## See Also

- [Generator](generator.md) - Base WaveDrom generator
- [Models](models.md) - Signal event and relationship models
- [Container](container.md) - Container for managing verification scenarios
- [Protocol Checks](protocol_checks.md) - Standard protocol checks
- [Capture](capture.md) - Utilities for managing waveform capture

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
