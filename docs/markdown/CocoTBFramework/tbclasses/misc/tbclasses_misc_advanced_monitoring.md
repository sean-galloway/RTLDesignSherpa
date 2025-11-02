# advanced_monitoring.py

Advanced monitoring capabilities providing comprehensive test execution analysis, profiling, debugging support, and detailed reporting for CocoTB testbenches. This module enables deep insights into test performance, resource usage, and execution patterns.

## Overview

The `advanced_monitoring.py` module provides sophisticated monitoring and analysis capabilities for verification environments. It tracks test execution metrics, provides profiling information, captures debug data, and generates comprehensive reports for test analysis and optimization.

### Key Features
- **Real-time performance profiling** with CPU and memory tracking
- **Checkpoint-based execution tracking** for detailed test flow analysis  
- **Statistical analysis and visualization** of test metrics
- **Memory leak detection** and resource usage monitoring
- **Interactive debugging support** with stack trace capture
- **Comprehensive reporting** with multiple output formats
- **Integration with TBBase** and other framework components

## Core Components

### TestMetrics

Data class containing comprehensive test execution metrics.

```python
@dataclass
class TestMetrics:
    test_name: str
    start_time: float
    end_time: Optional[float] = None
    status: str = "running"
    
    # Performance metrics
    cpu_usage_samples: List[float] = field(default_factory=list)
    memory_usage_samples: List[float] = field(default_factory=list)
    
    # Transaction metrics
    transactions_sent: int = 0
    transactions_received: int = 0
    transactions_failed: int = 0
    
    # Error tracking
    errors: int = 0
    warnings: int = 0
    
    # Timing analysis
    checkpoints: List[Dict] = field(default_factory=list)
    
    # Resource tracking
    max_memory_usage: float = 0.0
    avg_cpu_usage: float = 0.0
    
    # Identifiers for detailed analysis
    profile_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    debug_id: str = field(default_factory=lambda: str(uuid.uuid4()))
```

### TestProfiler

Real-time performance profiler for tracking CPU, memory, and execution metrics.

#### Constructor

```python
TestProfiler(sampling_interval=1.0, enable_detailed_tracking=True)
```

**Parameters:**
- `sampling_interval`: Interval between performance samples in seconds (default: 1.0)
- `enable_detailed_tracking`: Enable detailed CPU and memory tracking (default: True)

#### Methods

##### `start_profiling(profile_id)`

Start profiling for a specific test session.

**Parameters:**
- `profile_id`: Unique identifier for the profiling session

```python
profiler = TestProfiler(sampling_interval=0.5)
profile_id = profiler.start_profiling("test_001")
```

##### `stop_profiling(profile_id)`

Stop profiling and return collected metrics.

**Parameters:**
- `profile_id`: Profile session identifier

**Returns:** Dictionary of profiling metrics

```python
metrics = profiler.stop_profiling(profile_id)
print(f"Average CPU: {metrics['avg_cpu']:.1f}%")
print(f"Peak Memory: {metrics['peak_memory']:.1f} MB")
```

##### `add_checkpoint(name, profile_id, metadata=None)`

Add a checkpoint for timing analysis.

**Parameters:**
- `name`: Checkpoint identifier
- `profile_id`: Associated profile session
- `metadata`: Optional checkpoint metadata

```python
profiler.add_checkpoint("initialization_complete", profile_id)
profiler.add_checkpoint("main_test_start", profile_id, {"phase": "execution"})
```

##### `get_performance_summary(profile_id)`

Get comprehensive performance summary for a profile session.

**Parameters:**
- `profile_id`: Profile session identifier

**Returns:** Dictionary with performance analysis

```python
summary = profiler.get_performance_summary(profile_id)
print(f"Test duration: {summary['duration']:.2f}s")
print(f"Memory efficiency: {summary['memory_efficiency']:.1%}")
```

### TestDebugger

Debugging support with stack trace capture and execution analysis.

#### Constructor

```python
TestDebugger(max_traces=100, enable_stack_capture=True)
```

**Parameters:**
- `max_traces`: Maximum number of stack traces to retain (default: 100)
- `enable_stack_capture`: Enable automatic stack trace capture (default: True)

#### Methods

##### `start_debug_session(debug_id)`

Start a debugging session.

**Parameters:**
- `debug_id`: Unique identifier for the debug session

```python
debugger = TestDebugger()
debug_id = debugger.start_debug_session("debug_001")
```

##### `capture_stack_trace(debug_id, context=None)`

Capture current stack trace with context information.

**Parameters:**
- `debug_id`: Debug session identifier
- `context`: Optional context description

```python
debugger.capture_stack_trace(debug_id, "before_transaction_send")
```

##### `get_debug_summary(debug_id)`

Get debugging summary with stack traces and analysis.

**Parameters:**
- `debug_id`: Debug session identifier

**Returns:** Dictionary with debug information

```python
debug_info = debugger.get_debug_summary(debug_id)
for trace in debug_info['stack_traces']:
    print(f"Context: {trace['context']}")
    print(f"Function: {trace['function']}")
```

### TestReporter

Comprehensive reporting system with multiple output formats.

#### Constructor

```python
TestReporter(report_dir="./reports", enable_html=True, enable_json=True)
```

**Parameters:**
- `report_dir`: Directory for report output (default: "./reports")
- `enable_html`: Generate HTML reports (default: True)
- `enable_json`: Generate JSON reports (default: True)

#### Methods

##### `start_test_report(test_name)`

Initialize a new test report.

**Parameters:**
- `test_name`: Test identifier

**Returns:** TestMetrics instance for the test

```python
reporter = TestReporter(report_dir="./test_reports")
metrics = reporter.start_test_report("memory_stress_test")
```

##### `update_test_metrics(metrics, **kwargs)`

Update test metrics with new data.

**Parameters:**
- `metrics`: TestMetrics instance to update
- `**kwargs`: Metric values to update

```python
reporter.update_test_metrics(metrics,
    transactions_sent=50,
    transactions_received=48,
    errors=2
)
```

##### `finalize_test_report(metrics)`

Generate final test report with all collected data.

**Parameters:**
- `metrics`: TestMetrics instance with complete test data

**Returns:** Dictionary with report summary

```python
final_report = reporter.finalize_test_report(metrics)
print(f"Report saved to: {final_report['report_path']}")
print(f"Test status: {final_report['test_info']['status']}")
```

## Context Manager Interface

### `advanced_monitoring(test_name, report_dir="./reports", log=None)`

Primary interface providing context manager for easy test monitoring integration.

**Parameters:**
- `test_name`: Test identifier for reporting
- `report_dir`: Directory for report output (default: "./reports")
- `log`: Logger instance (default: None)

**Returns:** Monitor context object with checkpoint and metrics methods

```python
from CocoTBFramework.tbclasses.misc.advanced_monitoring import advanced_monitoring

@cocotb.test()
async def monitored_test(dut):
    with advanced_monitoring("comprehensive_test") as monitor:
        # Test initialization
        monitor.checkpoint("initialization_start")
        await initialize_testbench(dut)
        monitor.checkpoint("initialization_complete")
        
        # Main test execution
        monitor.checkpoint("main_test_start")
        for i in range(100):
            await execute_transaction(dut, i)
            monitor.update_metrics(transactions_sent=1)
        monitor.checkpoint("main_test_complete")
        
        # Verification phase
        monitor.checkpoint("verification_start")
        results = await verify_results(dut)
        monitor.update_metrics(verification_errors=len(results['errors']))
        monitor.checkpoint("verification_complete")
    
    # Report is automatically generated at context exit
```

#### Monitor Context Methods

##### `checkpoint(name)`

Create a checkpoint in the test execution.

**Parameters:**
- `name`: Checkpoint identifier

```python
with advanced_monitoring("test") as monitor:
    monitor.checkpoint("phase_1_complete")
    # ... test logic ...
    monitor.checkpoint("phase_2_complete")
```

##### `update_metrics(**kwargs)`

Update test metrics with new values.

**Parameters:**
- `**kwargs`: Metric names and values to update

```python
with advanced_monitoring("test") as monitor:
    # Update transaction counts
    monitor.update_metrics(
        transactions_sent=10,
        transactions_received=8,
        errors=2
    )
```

##### `get_status()`

Get current test status and metrics.

**Returns:** Dictionary with current test information

```python
with advanced_monitoring("test") as monitor:
    # ... test execution ...
    status = monitor.get_status()
    print(f"Duration: {status['duration']:.2f}s")
    print(f"Memory: {status['memory_current']:.1f} MB")
```

## Integration with TBBase

### MonitoringTBBase

Example integration showing how to combine advanced monitoring with TBBase infrastructure.

```python
from CocoTBFramework.tbclasses.misc.tbbase import TBBase
from CocoTBFramework.tbclasses.misc.advanced_monitoring import advanced_monitoring

class MonitoringTBBase(TBBase):
    """Testbench base class with integrated advanced monitoring"""
    
    def __init__(self, dut, test_name="MonitoringTest", **kwargs):
        super().__init__(dut, test_name, **kwargs)
        self.monitor_context = None
    
    async def run_monitored_test(self, test_function, *args, **kwargs):
        """Run a test with comprehensive monitoring"""
        with advanced_monitoring(self.test_name) as monitor:
            self.monitor_context = monitor
            
            try:
                # Initialization phase
                monitor.checkpoint("testbench_init_start")
                await self.initialize()
                monitor.checkpoint("testbench_init_complete")
                
                # Test execution phase
                monitor.checkpoint("test_execution_start")
                result = await test_function(self, *args, **kwargs)
                monitor.checkpoint("test_execution_complete")
                
                # Cleanup phase
                monitor.checkpoint("cleanup_start")
                await self.cleanup()
                monitor.checkpoint("cleanup_complete")
                
                return result
                
            except Exception as e:
                monitor.update_metrics(errors=1)
                self.log.error(f"Test failed: {e}")
                raise
    
    def update_test_metrics(self, **kwargs):
        """Update metrics if monitoring is active"""
        if self.monitor_context:
            self.monitor_context.update_metrics(**kwargs)
```

## Usage Patterns

### Basic Monitoring

```python
import cocotb
from CocoTBFramework.tbclasses.misc.advanced_monitoring import advanced_monitoring

@cocotb.test()
async def basic_monitored_test(dut):
    """Simple test with basic monitoring"""
    with advanced_monitoring("basic_test") as monitor:
        # Test setup
        monitor.checkpoint("setup_complete")
        
        # Test execution
        for i in range(10):
            await send_transaction(dut, i)
            monitor.update_metrics(transactions_sent=1)
        
        monitor.checkpoint("test_complete")
```

### Performance Analysis

```python
@cocotb.test()
async def performance_test(dut):
    """Test with detailed performance analysis"""
    with advanced_monitoring("performance_test") as monitor:
        # Stress test with performance tracking
        start_time = time.time()
        
        for burst in range(10):
            monitor.checkpoint(f"burst_{burst}_start")
            
            # High-frequency transactions
            for i in range(1000):
                await send_transaction(dut, i)
                monitor.update_metrics(transactions_sent=1)
            
            monitor.checkpoint(f"burst_{burst}_complete")
            
            # Check performance status
            status = monitor.get_status()
            if status['memory_current'] > 1000:  # 1GB limit
                monitor.update_metrics(warnings=1)
                break
        
        total_time = time.time() - start_time
        throughput = 10000 / total_time  # transactions per second
        monitor.update_metrics(throughput=throughput)
```

### Error Tracking and Analysis

```python
@cocotb.test()
async def error_analysis_test(dut):
    """Test with comprehensive error tracking"""
    with advanced_monitoring("error_analysis") as monitor:
        error_count = 0
        
        for test_case in test_scenarios:
            monitor.checkpoint(f"scenario_{test_case['name']}_start")
            
            try:
                await execute_scenario(dut, test_case)
                monitor.update_metrics(scenarios_passed=1)
                
            except ProtocolError as e:
                error_count += 1
                monitor.update_metrics(
                    protocol_errors=1,
                    errors=1
                )
                monitor.checkpoint(f"protocol_error_{error_count}")
                
            except TimeoutError as e:
                error_count += 1
                monitor.update_metrics(
                    timeout_errors=1,
                    errors=1
                )
                monitor.checkpoint(f"timeout_error_{error_count}")
                
            monitor.checkpoint(f"scenario_{test_case['name']}_complete")
```

### Regression Testing

```python
@cocotb.test()
async def regression_test(dut):
    """Regression test with trend analysis"""
    baseline_metrics = load_baseline_metrics("regression_baseline.json")
    
    with advanced_monitoring("regression_test") as monitor:
        # Execute standard test suite
        await execute_test_suite(dut, monitor)
        
        # Compare with baseline
        current_status = monitor.get_status()
        
        # Performance regression detection
        if current_status['duration'] > baseline_metrics['max_duration'] * 1.1:
            monitor.update_metrics(
                performance_regressions=1,
                warnings=1
            )
        
        # Memory regression detection
        if current_status['memory_current'] > baseline_metrics['max_memory'] * 1.1:
            monitor.update_metrics(
                memory_regressions=1,
                warnings=1
            )
        
        monitor.checkpoint("regression_analysis_complete")
```

## Report Analysis

The advanced monitoring system generates comprehensive reports that can be analyzed for:

### Performance Optimization
- Identify performance bottlenecks in test execution
- Track memory usage patterns and potential leaks
- Analyze checkpoint timing for optimization opportunities
- Compare performance across different test configurations

### Test Quality Assessment
- Monitor test coverage and transaction completeness
- Track error rates and failure patterns
- Analyze test reliability and consistency
- Identify unstable test scenarios

### Development Insights
- Understand testbench resource requirements
- Optimize test execution order and dependencies
- Identify opportunities for parallel execution
- Monitor the impact of code changes on test performance

## Best Practices

1. **Use meaningful checkpoint names** that clearly identify test phases
2. **Update metrics consistently** throughout test execution
3. **Monitor resource usage** especially for long-running tests
4. **Analyze reports regularly** to identify trends and issues
5. **Integrate with CI/CD** for automated performance monitoring
6. **Archive reports** for historical analysis and regression detection
7. **Configure appropriate sampling rates** based on test characteristics

The advanced monitoring system provides powerful capabilities for understanding, optimizing, and maintaining verification environments while ensuring consistent test quality and performance.