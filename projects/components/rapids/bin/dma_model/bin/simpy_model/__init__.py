"""
SimPy Model Package

Discrete-event simulation for AXI4 performance analysis.

Main modules:
- current_design: Core SimPy simulation (baseline + optimized)
- optimizations: Incremental optimization framework
- validate: Validation against analytical model
- compare: Model comparison and visualization
"""

# Core simulation components
from .current_design import (
    ReadChannelConfig,
    ReadChannelStats,
    ReadChannel,
    AXI4ReadSystem,
    run_baseline_simulation,
    run_optimized_simulation
)

# Optimization framework
from .optimizations import (
    OptimizationStep,
    OPTIMIZATION_SEQUENCE,
    run_single_optimization,
    run_optimization_sequence
)

# Validation - only import what actually exists
from .validate import (
    ValidationResult,
    validate_baseline,
    validate_optimized,
    validate_all_configurations,
    generate_validation_report,
    validate_timing_breakdown
)

# Comparison and visualization
from .compare import (
    ComparisonResult,
    compare_single_config,
    run_channel_sweep,
    plot_comparison,
    create_comparison_table
)

__version__ = "1.0.0"

__all__ = [
    # Core simulation
    'ReadChannelConfig',
    'ReadChannelStats',
    'ReadChannel',
    'AXI4ReadSystem',
    'run_baseline_simulation',
    'run_optimized_simulation',
    
    # Optimization framework
    'OptimizationStep',
    'OPTIMIZATION_SEQUENCE',
    'run_single_optimization',
    'run_optimization_sequence',
    
    # Validation - only what exists
    'ValidationResult',
    'validate_baseline',
    'validate_optimized',
    'validate_all_configurations',
    'generate_validation_report',
    'validate_timing_breakdown',
    
    # Comparison
    'ComparisonResult',
    'compare_single_config',
    'run_channel_sweep',
    'plot_comparison',
    'create_comparison_table',
]
