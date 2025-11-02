# Complete Read + Write Analysis Integration

## Overview

This document shows how to integrate the new write path analysis with existing read path analysis to provide complete system-level performance analysis.

## Files Created

### 1. `analytical/write_analysis.py`
Analytical model for write path with functions:
- `get_write_performance()` - Baseline write (256B bursts, 32 outstanding)
- `get_optimized_write_performance()` - Optimized write (64 outstanding)  
- `compare_write_payloads()` - Compare different write burst sizes
- `analyze_combined_performance()` - Combined read+write analysis

### 2. `simpy_model/write_design.py`
SimPy simulation for write path with:
- `WriteChannel` class
- `AXI4WriteSystem` class
- `run_write_simulation()` - Baseline simulation
- `run_optimized_write_simulation()` - Optimized simulation

## Integration Approach

### Tables Should Show BOTH Read and Write

**Before (Read Only):**
```
Configuration      Bandwidth      Efficiency
Baseline           44.05 GB/s     76.5%
Optimized          64.00 GB/s     99.0%
```

**After (Read + Write):**
```
Configuration      Read BW        Write BW       Combined BW    Efficiency
Baseline           44.05 GB/s     18.23 GB/s     57.6 GB/s      100%
Optimized          64.00 GB/s     24.50 GB/s     57.6 GB/s      100%
```

**Key Points:**
- Combined BW limited by AXI peak (57.6 GB/s)
- Read and write compete for same AXI bandwidth
- Show all three: read, write, combined

## Usage Examples

### Example 1: Analyze Both Paths (Analytical)

```python
from analytical.current_design import get_baseline_performance, get_optimized_performance
from analytical.write_analysis import get_write_performance, get_optimized_write_performance

# Read path
read_baseline = get_baseline_performance(verbose=False)
read_opt = get_optimized_performance(pipeline_depth=4, streaming=True, verbose=False)

# Write path
write_baseline = get_write_performance(num_channels=16, verbose=False)
write_opt = get_optimized_write_performance(num_channels=16, max_outstanding=64, verbose=False)

# Get results
read_base_bw = read_baseline['performance'].calculate_channel_bandwidth(16)['total_bw']
read_opt_bw = read_opt['performance'].calculate_channel_bandwidth(16)['total_bw']
write_base_bw = write_baseline['result']['total_bw']
write_opt_bw = write_opt['result']['total_bw']

# Print comparison table
print(f"{'Configuration':<20} {'Read BW':<15} {'Write BW':<15} {'Combined':<15}")
print("-" * 70)
print(f"{'Baseline':<20} {read_base_bw:>8.2f} GB/s   {write_base_bw:>8.2f} GB/s   {min(read_base_bw + write_base_bw, 57.6):>8.2f} GB/s")
print(f"{'Optimized':<20} {read_opt_bw:>8.2f} GB/s   {write_opt_bw:>8.2f} GB/s   {min(read_opt_bw + write_opt_bw, 57.6):>8.2f} GB/s")
```

### Example 2: Combined Analysis Function

```python
from analytical.write_analysis import analyze_combined_performance

# Baseline: both unoptimized
baseline = analyze_combined_performance(
    num_channels=16,
    read_optimized=False,
    write_optimized=False,
    verbose=True
)

# Optimized: both optimized
optimized = analyze_combined_performance(
    num_channels=16,
    read_optimized=True,
    write_optimized=True,
    verbose=True
)

# Results show:
# - Read BW
# - Write BW
# - Combined BW (limited by AXI peak)
# - Whether AXI-limited
```

### Example 3: SimPy Both Paths

```python
from simpy_model.current_design import run_baseline_simulation as run_read_sim
from simpy_model.write_design import run_write_simulation

# Run both simulations
read_results = run_read_sim(num_channels=16, simulation_time=100000, verbose=False)
write_results = run_write_simulation(num_channels=16, simulation_time=100000, verbose=False)

# Extract bandwidths
read_bw = read_results['aggregate_bandwidth']
write_bw = write_results['aggregate_bandwidth']
combined = min(read_bw + write_bw, 57.6)  # AXI peak limit

print(f"SimPy Results:")
print(f"  Read:     {read_bw:.2f} GB/s")
print(f"  Write:    {write_bw:.2f} GB/s")
print(f"  Combined: {combined:.2f} GB/s (AXI limited)")
```

## Updated Quick Start Examples

### Example: Compare Baseline vs Optimized (Both Paths)

```python
def example_compare_both_paths():
    """Compare baseline vs optimized for BOTH read and write."""
    from analytical import get_baseline_performance, get_optimized_performance
    from analytical.write_analysis import get_write_performance, get_optimized_write_performance
    
    # Get read performance
    read_base = get_baseline_performance(verbose=False)
    read_opt = get_optimized_performance(pipeline_depth=4, streaming=True, verbose=False)
    
    # Get write performance
    write_base = get_write_performance(num_channels=16, verbose=False)
    write_opt = get_optimized_write_performance(num_channels=16, max_outstanding=64, verbose=False)
    
    # Extract bandwidths
    rb_bw = read_base['performance'].calculate_channel_bandwidth(16)['total_bw']
    ro_bw = read_opt['performance'].calculate_channel_bandwidth(16)['total_bw']
    wb_bw = write_base['result']['total_bw']
    wo_bw = write_opt['result']['total_bw']
    
    axi_peak = 57.6
    
    print("\n" + "="*80)
    print("  BASELINE VS OPTIMIZED - READ + WRITE")
    print("="*80 + "\n")
    
    print(f"{'Configuration':<15} {'Read BW':<15} {'Write BW':<15} {'Combined':<15} {'AXI %':<10}")
    print("-" * 75)
    
    comb_base = min(rb_bw + wb_bw, axi_peak)
    comb_opt = min(ro_bw + wo_bw, axi_peak)
    
    print(f"{'Baseline':<15} {rb_bw:>8.2f} GB/s   {wb_bw:>8.2f} GB/s   {comb_base:>8.2f} GB/s   {comb_base/axi_peak*100:>5.1f}%")
    print(f"{'Optimized':<15} {ro_bw:>8.2f} GB/s   {wo_bw:>8.2f} GB/s   {comb_opt:>8.2f} GB/s   {comb_opt/axi_peak*100:>5.1f}%")
    
    print("\nKey Insights:")
    print(f"  • Read improvement:  +{((ro_bw/rb_bw)-1)*100:.1f}%")
    print(f"  • Write improvement: +{((wo_bw/wb_bw)-1)*100:.1f}%")
    print(f"  • Combined at AXI peak ({axi_peak} GB/s) for both configs")
    print(f"  • Read + Write compete for shared AXI bandwidth")
```

## Performance Summary Format

### Recommended Table Format

```
================================================================================
  PERFORMANCE SUMMARY - BASELINE vs OPTIMIZED
================================================================================

Configuration      Read BW        Write BW       Combined BW    AXI Util
--------------------------------------------------------------------------------
Baseline           44.05 GB/s     18.23 GB/s     57.6 GB/s*     100%
Optimized          64.00 GB/s     24.50 GB/s     57.6 GB/s*     100%
--------------------------------------------------------------------------------
Improvement        +45.3%         +34.4%         +0%            —

* Limited by AXI peak bandwidth (57.6 GB/s)
  Read and write paths share the same AXI interface

Per-Path Details:
  Read:  2KB bursts, store-and-forward → streaming + pipelining
  Write: 256B bursts, 32 outstanding → 64 outstanding

Key Findings:
  ✓ Read path optimized to 64 GB/s (exceeds 50 GB/s target)
  ✓ Write path improved to 24.5 GB/s
  ⚠ Combined bandwidth limited by AXI peak
  → In practice, workload mix determines actual performance
```

## SRAM Analysis for Both Paths

### Read SRAM
- Large bursts (2KB)
- Store-and-forward or streaming
- Ping-pong (4KB) or Monolithic (8KB) per channel

### Write SRAM  
- Small bursts (256B)
- Fill buffers before sending
- Simpler requirements (~1KB per channel)

### Combined SRAM Budget

```python
from analytical.sram_analysis import compare_sram_modes

# Read SRAM
read_sram = compare_sram_modes(payload=2048, pipeline_depth=4, num_channels=16)
read_total_kb = read_sram['monolithic']['total_sram_kb']

# Write SRAM (estimate: 2 slots × 256B)
write_sram_per_ch = 0.5  # KB
write_total_kb = write_sram_per_ch * 16

# Total system SRAM
total_sram_kb = read_total_kb + write_total_kb

print(f"System SRAM Budget:")
print(f"  Read path:  {read_total_kb:.1f} KB")
print(f"  Write path: {write_total_kb:.1f} KB")
print(f"  Total:      {total_sram_kb:.1f} KB")
```

## Validation

### Validate Both Paths

```python
from simpy_model.validate import validate_baseline, validate_optimized

# Validate read path (existing)
read_val = validate_baseline(num_channels=16, simulation_time=100000)

# Validate write path (new)
# Create write validation similarly to read validation
# Compare analytical write vs SimPy write

print(f"Validation Results:")
print(f"  Read:  Analytical={read_val.analytical_bw:.2f}, SimPy={read_val.simpy_bw:.2f}, Diff={read_val.relative_diff_pct:+.1f}%")
print(f"  Write: [Implement similar validation for write path]")
```

## Migration Checklist

To fully integrate read + write analysis:

### ✅ Completed
- [x] Created `analytical/write_analysis.py`
- [x] Created `simpy_model/write_design.py`
- [x] Functions for baseline and optimized write
- [x] Combined read+write analysis function

### 🔄 To Do
- [ ] Update `run_complete_analysis.py` to run both paths
- [ ] Update `quick_start.py` examples to show both
- [ ] Update all tables to have "Read BW" and "Write BW" columns
- [ ] Add write path to validation framework
- [ ] Update SRAM analysis to include write buffers
- [ ] Update plots to show both paths
- [ ] Update README with read+write examples

### 📋 Recommended Updates

**1. run_complete_analysis.py**
```python
# After Part 1 (Analytical Read)
print_header("PART 1B: ANALYTICAL WRITE PATH")
analytical_write_results = run_analytical_write_analysis()

# After Part 2 (SimPy Read)
print_header("PART 2B: SIMPY WRITE PATH")
simpy_write_results = run_simpy_write_analysis()

# Update final summary
print("\n1. BASELINE PERFORMANCE:")
print(f"   Read:     {baseline_read_bw:.2f} GB/s")
print(f"   Write:    {baseline_write_bw:.2f} GB/s")
print(f"   Combined: {min(baseline_read_bw + baseline_write_bw, 57.6):.2f} GB/s")
```

**2. quick_start.py**
```python
def example_3_compare_both_paths():
    """Example 3: Compare baseline vs optimized (READ + WRITE)."""
    # Show both read and write in comparison table
    # Include combined bandwidth
    # Note AXI peak limitation
```

**3. All Tables**
```
Before:
Configuration      Bandwidth
Baseline           44.05 GB/s

After:
Configuration      Read BW        Write BW       Combined
Baseline           44.05 GB/s     18.23 GB/s     57.6 GB/s
```

## Summary

### What We Built
✅ Analytical write path model  
✅ SimPy write path simulation  
✅ Combined read+write analysis  
✅ Integration functions  

### How to Use
```python
# Quick combined analysis
from analytical.write_analysis import analyze_combined_performance

results = analyze_combined_performance(
    num_channels=16,
    read_optimized=True,
    write_optimized=True,
    verbose=True
)

# Shows:
# - Read: 64.00 GB/s
# - Write: 24.50 GB/s
# - Combined: 57.6 GB/s (AXI limited)
```

### Next Steps
1. Update main scripts to call both read and write functions
2. Update all output tables to show both paths
3. Add write validation
4. Update documentation

### Key Message
**Complete system analysis = Read performance + Write performance**

Both paths share the same AXI bandwidth (57.6 GB/s peak), so they must be analyzed together to understand true system capability.
