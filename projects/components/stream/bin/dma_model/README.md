# STREAM DMA Performance Model

**Version:** 1.0
**Last Updated:** 2025-10-17
**Purpose:** Analytical performance model for STREAM memory-to-memory DMA engine

---

## Overview

This directory contains a comprehensive performance analysis model for the STREAM DMA engine. The model accurately reflects STREAM architecture with:

- **8 independent channels** (vs 16 in RAPIDS)
- **Separate read and write paths** (decoupled by SRAM buffer)
- **Asymmetric burst configurations** (read vs write engines can have different parameters)
- **Three performance modes:** Low, Medium, High
- **SRAM buffering** (64 KB total, 8 KB per channel)

The model helps you understand bandwidth scaling, identify bottlenecks, and select appropriate performance modes for your use case.

---

## Quick Start

### Run Full Analysis

```bash
# Activate virtual environment (if not already active)
source /path/to/rtldesignsherpa/venv/bin/activate

# Navigate to analysis directory
cd bin/dma_model/bin

# Run complete analysis with all modes
python3 comprehensive_analysis.py

# Generate performance plots
python3 comprehensive_analysis.py --plots
```

### Analyze Specific Mode

```bash
# Analyze LOW performance mode only
python3 comprehensive_analysis.py --mode LOW

# Analyze MEDIUM mode with plots
python3 comprehensive_analysis.py --mode MEDIUM --plots

# Analyze HIGH mode with custom payload
python3 comprehensive_analysis.py --mode HIGH --payload 2048 --plots
```

---

## Performance Modes

### Low Performance Mode (Tutorial)

**Target:** Educational, area-constrained designs

**Configuration:**
- Read burst: 8 beats
- Write burst: 16 beats (asymmetric!)
- Outstanding transactions: 1 (read), 1 (write)
- Pipeline depth: 1

**Performance (8 channels, 1KB payload):**
- Read bandwidth: 39.4 GB/s
- Write bandwidth: 37.9 GB/s
- DMA throughput: 37.9 GB/s (limited by write path)

**Use Cases:**
- Tutorial examples
- FPGA prototypes
- Area-constrained designs
- Simple learning platform

### Medium Performance Mode (Typical)

**Target:** Balanced performance/area for typical FPGA implementations

**Configuration:**
- Read burst: 16 beats
- Write burst: 32 beats (asymmetric!)
- Outstanding transactions: 4 (read), 4 (write)
- Pipeline depth: 4

**Performance (8 channels, 1KB payload):**
- Read bandwidth: 57.6 GB/s (AXI peak)
- Write bandwidth: 57.6 GB/s (AXI peak)
- DMA throughput: 57.6 GB/s (balanced)

**Use Cases:**
- Typical FPGA implementations
- Balanced designs
- Production systems

### High Performance Mode (Maximum Throughput)

**Target:** High-throughput ASIC/FPGA implementations

**Configuration:**
- Read burst: 256 beats
- Write burst: 256 beats
- Outstanding transactions: 16 (read), 16 (write)
- Pipeline depth: 16

**Performance (8 channels, 1KB payload):**
- Read bandwidth: 57.6 GB/s (AXI peak)
- Write bandwidth: 57.6 GB/s (AXI peak)
- DMA throughput: 57.6 GB/s (balanced)

**Note:** SRAM capacity (128 lines/channel) limits effective pipelining at small payload sizes.

**Use Cases:**
- High-performance ASIC
- High-end FPGA (Versal, Agilex, etc.)
- Maximum throughput applications

---

## Key Architecture Insights

### 1. Read and Write Paths are INDEPENDENT

Unlike network-oriented designs (like RAPIDS), STREAM read and write paths are **completely decoupled** by the SRAM buffer:

- Read path: Memory → AXI Read Engine → SRAM
- Write path: SRAM → AXI Write Engine → Memory

**Implication:** You can analyze read and write bandwidth separately. Overall DMA throughput is limited by the **slower of the two paths**.

### 2. Asymmetric Burst Lengths

STREAM supports **different burst configurations for read vs write engines**:

- Low mode: 8-beat read, 16-beat write
- Medium mode: 16-beat read, 32-beat write
- High mode: 256-beat read/write

**Why Asymmetric?**
- Write path typically benefits from larger bursts (fewer AW transactions)
- Read path can be smaller for better interleaving
- Allows fine-tuning for specific memory controller characteristics

### 3. SRAM Capacity Constraints

Each channel has **128 lines** (8 KB / 64 bytes per line):

- **Low mode:** No constraint (bursts < 16 beats)
- **Medium mode:** Mild constraint at large payloads
- **High mode:** SRAM limits effective pipeline depth at small payloads

**Example (High mode, 1KB payload):**
- Payload = 1024 bytes = 16 beats
- 128 lines / 16 beats = 8 bursts max in SRAM
- Effective pipeline = min(16, 8) = 8 (SRAM-limited)

### 4. Bandwidth Scaling

**Single Channel Performance:**
- Limited by: Timing (latency + data transfer)
- Affected by: Burst size, pipeline depth, outstanding transactions

**Multi-Channel Performance:**
- Additional limit: AXI peak bandwidth (57.6 GB/s @ 512-bit, 1 GHz, α=0.9)
- Channels compete for shared AXI interface
- Total bandwidth caps at AXI peak

**Efficiency Calculation:**
```
Efficiency = (Total_BW / AXI_Peak_BW) * 100%

Low mode: 37.9 GB/s / 57.6 GB/s = 65.8% efficient
Medium mode: 57.6 GB/s / 57.6 GB/s = 100% efficient (saturated)
High mode: 57.6 GB/s / 57.6 GB/s = 100% efficient (saturated)
```

---

## Analysis Outputs

### 1. Console Output

**Default Configuration:**
- AXI interface parameters (width, frequency, peak bandwidth)
- SRAM configuration (total size, per-channel capacity)
- Performance mode configurations

**Per-Mode Analysis (Low/Medium/High):**
- Configuration summary
- Single channel performance (read/write separate)
- 8-channel performance (read/write separate)
- DMA end-to-end throughput
- Bottleneck identification

**Mode Comparison:**
- Side-by-side performance comparison
- Key insights and recommendations

**Payload Sweep:**
- Performance across different payload sizes (256B to 4KB)
- Shows impact of burst size on bandwidth

### 2. Visualization Plots

All plots saved to `assets/` directory:

**Individual Mode Plots:**
- `{mode}_read.png` - Read engine performance
- `{mode}_write.png` - Write engine performance
- `{mode}_comparison.png` - Read vs write on same axes

**Mode Comparison:**
- `mode_comparison.png` - Low vs Medium vs High modes

**Plot Features:**
- Per-channel bandwidth (left subplot)
- Total bandwidth (right subplot)
- AXI peak reference line
- Clear labeling and legends

---

## Directory Structure

```
bin/dma_model/
├── README.md                           # This file
├── bin/
│   ├── comprehensive_analysis.py      # Main analysis script
│   └── pyperf/                        # Performance analysis package
│       ├── __init__.py
│       ├── performance.py             # Core performance model
│       └── visualization.py           # Plot generation
├── csv/                                # CSV output (if generated)
└── assets/                             # Generated plots
    ├── low_read.png
    ├── low_write.png
    ├── low_comparison.png
    ├── medium_read.png
    ├── medium_write.png
    ├── medium_comparison.png
    ├── high_read.png
    ├── high_write.png
    ├── high_comparison.png
    └── mode_comparison.png
```

---

## Usage Examples

### Example 1: Compare All Modes

```bash
python3 comprehensive_analysis.py
```

Output:
- Default configuration
- Low mode analysis
- Medium mode analysis
- High mode analysis
- Mode comparison table
- Payload sweep analysis for each mode
- Summary and recommendations

### Example 2: Analyze Low Mode with Plots

```bash
python3 comprehensive_analysis.py --mode LOW --plots
```

Output:
- Low mode configuration
- Single channel performance
- 8-channel performance
- Payload sweep
- Plots: `assets/low_*.png`

### Example 3: Custom Payload Analysis

```bash
python3 comprehensive_analysis.py --mode MEDIUM --payload 2048 --plots
```

Output:
- Medium mode with 2KB payload
- Performance analysis
- Plots with 2KB configuration

### Example 4: Generate Only Plots

```bash
python3 comprehensive_analysis.py --plots --output-dir plots/
```

Output:
- Full analysis
- All plots saved to `plots/` directory

---

## Performance Model Details

### Bandwidth Calculation

**Per-Channel Bandwidth:**

```python
# With pipelining (pipeline_depth > 1)
cycles_per_burst = (latency / effective_pipeline) + effective_BL
B_channel = (payload * frequency) / cycles_per_burst

# Without pipelining (pipeline_depth = 1)
cycles_per_burst = latency + effective_BL
B_channel = (payload * frequency) / cycles_per_burst
```

**Where:**
- `latency` = Memory latency (200 cycles)
- `effective_pipeline` = min(pipeline_depth, SRAM_capacity, max_outstanding)
- `effective_BL` = min(payload / bus_width, max_burst_len)

**Total Bandwidth:**

```python
total_bw_from_channels = B_channel * num_channels
total_bw = min(total_bw_from_channels, AXI_peak_BW)
```

**DMA Throughput:**

```python
# Read and write are independent, DMA limited by slower
dma_throughput = min(read_total_bw, write_total_bw)
```

### Limiting Factors

**Timing-Limited:**
- Sequential operation (low pipeline depth)
- High latency relative to data transfer time

**AXI Peak-Limited:**
- Total channel bandwidth exceeds AXI interface capacity
- Multiple channels saturate the bus

**SRAM Capacity-Limited:**
- Effective pipeline depth limited by SRAM buffer size
- Occurs in High mode with small payloads

**Outstanding Transaction-Limited:**
- `max_outstanding` < `pipeline_depth`
- Transaction table capacity constrains pipelining

---

## Interpreting Results

### Bottleneck Identification

**"Limited by: timing"**
- Pipeline depth insufficient to hide latency
- Consider: Increase pipeline depth or burst size

**"Limited by: AXI_peak"**
- Bus saturated (good!)
- Further channels won't increase total bandwidth

**"Limited by: SRAM_capacity"**
- SRAM buffer too small for desired pipeline depth
- Consider: Larger payloads or increase SRAM per channel

**"Bottleneck: write_path"**
- Write bandwidth < read bandwidth
- Overall DMA throughput limited by write side
- Consider: Increase write burst length or outstanding transactions

**"Bottleneck: read_path"**
- Read bandwidth < write bandwidth
- Overall DMA throughput limited by read side
- Consider: Increase read burst length or outstanding transactions

**"Bottleneck: balanced"**
- Read and write bandwidths equal (ideal!)

### Efficiency Metrics

**Single Channel Efficiency:**
```
Efficiency = (B_channel / B_max) * 100%

Where B_max = bus_width * frequency * alpha
```

**Multi-Channel Efficiency:**
```
Efficiency = (Total_BW / AXI_Peak_BW) * 100%

Target: 100% (saturated bus)
```

---

## Comparison to RAPIDS

| Feature | RAPIDS | STREAM |
|---------|--------|--------|
| **Channels** | 16 | 8 |
| **Interfaces** | Network + Memory | Memory only |
| **Read/Write Coupling** | Coupled via network | Independent (SRAM-decoupled) |
| **Burst Lengths** | Typically symmetric | Asymmetric (read ≠ write) |
| **Complexity** | High (network protocol) | Low (memory-to-memory) |
| **Use Case** | Network accelerator | Tutorial DMA |

**Key Difference:** STREAM read and write paths are **completely independent**, while RAPIDS paths are coupled through network interfaces.

---

## Advanced Usage

### Custom Mode Configuration

To create custom performance configurations, edit `performance.py`:

```python
CUSTOM_PERF_CONFIG = {
    'name': 'Custom Performance',
    'max_burst_len_read': 32,
    'max_burst_len_write': 64,
    'max_outstanding_read': 8,
    'max_outstanding_write': 8,
    'pipeline_depth': 8,
    'use_case': 'Custom FPGA design'
}
```

Then use in analysis:

```python
from pyperf import create_mode_configs, StreamDMAPerformance

# Create custom config
custom_config = StreamDMAConfig(
    read_config=AXIConfig(
        payload=1024,
        max_burst_len=32,
        max_outstanding=8,
        pipeline_depth=8,
        engine_type="read"
    ),
    write_config=AXIConfig(
        payload=1024,
        max_burst_len=64,
        max_outstanding=8,
        pipeline_depth=8,
        engine_type="write"
    )
)

# Analyze
dma_perf = StreamDMAPerformance(custom_config)
results = dma_perf.calculate_dma_bandwidth(num_channels=8)
```

### CSV Export

To export results to CSV for external analysis:

```python
import pandas as pd

# Generate performance table
dma_df = dma_perf.generate_dma_table(max_channels=8)

# Export to CSV
dma_df.to_csv('csv/stream_performance.csv', index=False)
```

---

## Dependencies

**Required Python Packages:**
- `pandas` - Data analysis and tables
- `numpy` - Numerical computations
- `matplotlib` - Plot generation (optional, for `--plots`)

**Installation:**
```bash
# All dependencies in repository requirements.txt
pip install -r /path/to/rtldesignsherpa/requirements.txt
```

---

## Troubleshooting

### Issue: "ModuleNotFoundError: No module named 'pandas'"

**Solution:** Activate virtual environment

```bash
source /path/to/rtldesignsherpa/venv/bin/activate
python3 comprehensive_analysis.py
```

### Issue: Plots not generating

**Symptom:** "Could not generate plots: No module named 'matplotlib'"

**Solution:** Install matplotlib

```bash
pip install matplotlib
```

Or use analysis without plots:

```bash
python3 comprehensive_analysis.py  # No --plots flag
```

### Issue: Unexpected performance results

**Check:**
1. Payload size matches expected value
2. Performance mode is correct (LOW vs MEDIUM vs HIGH)
3. SRAM capacity sufficient for desired pipeline depth
4. AXI interface parameters (width, frequency) match your design

---

## Future Enhancements

**Potential Additions:**
- [ ] Memory controller latency variations
- [ ] Non-uniform latency modeling (DDR refresh, etc.)
- [ ] Power consumption estimates
- [ ] Area vs performance tradeoff analysis
- [ ] Payload size optimization recommendations

---

## References

**STREAM Specification:**
- `projects/components/stream/docs/stream_spec/stream_index.md` - Complete architecture
- `projects/components/stream/docs/stream_spec/ch02_blocks/` - Block specifications

**Related:**
- `projects/components/rapids/bin/dma_model/` - RAPIDS performance model (reference)

---

## Version History

- **v1.0 (2025-10-17):** Initial creation
  - Low/Medium/High performance modes
  - Asymmetric burst length support
  - Independent read/write path analysis
  - Comprehensive visualization

---

**Maintained By:** STREAM Architecture Team
**Questions?** See `projects/components/stream/CLAUDE.md` for development guide
