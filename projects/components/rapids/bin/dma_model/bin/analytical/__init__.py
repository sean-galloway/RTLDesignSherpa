"""
Analytical Model Package

Analytical performance analysis using closed-form equations.

Main functions:
- get_baseline_performance: Current design performance
- get_optimized_performance: Optimized design performance
- compare_all_payloads: Compare different payload sizes
- analyze_pipelining_impact: Analyze pipelining benefits
- compare_drain_modes: Store-and-forward vs streaming
- run_full_analysis: Complete analysis suite

Usage:
    from analytical import get_baseline_performance, get_optimized_performance
    
    baseline = get_baseline_performance(verbose=True)
    optimized = get_optimized_performance(pipeline_depth=4, streaming=True)
    
    print(f"Baseline: {baseline['performance'].calculate_channel_bandwidth(16)['total_bw']:.2f} GB/s")
    print(f"Optimized: {optimized['performance'].calculate_channel_bandwidth(16)['total_bw']:.2f} GB/s")
"""

from .current_design import (
    get_baseline_performance,
    get_optimized_performance,
    compare_all_payloads,
    analyze_pipelining_impact,
    compare_drain_modes,
    run_full_analysis
)

__version__ = "1.0.0"
__all__ = [
    'get_baseline_performance',
    'get_optimized_performance',
    'compare_all_payloads',
    'analyze_pipelining_impact',
    'compare_drain_modes',
    'run_full_analysis'
]
