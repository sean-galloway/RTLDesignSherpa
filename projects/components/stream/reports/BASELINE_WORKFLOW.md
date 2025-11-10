# V1 Baseline Performance Testing Workflow

**Created:** 2025-10-28
**Purpose:** Document workflow for collecting V1 baseline metrics and creating DMA performance model

---

## Current Status

✅ **Performance Report Templates Created** (6 files in `reports/`)
✅ **V1 Baseline Test Created** (`performance_tests/test_v1_baseline_read.py`)
⏳ **Test needs refinement** to properly use testbench API
⏳ **V1 baseline data collection** (18 configurations)
⏳ **DMA model creation/update** in `bin/`

---

## Workflow Steps

### Step 1: Run V1 Baseline Tests (Automated) ✅

**Automated Workflow:**
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/dv/tests/performance_tests

# Run V1 read baseline AND auto-update reports
make v1-read-baseline

# OR run manually with separate report update
pytest test_v1_baseline_read.py -v -s
../../../bin/update_performance_reports.py --version v1 --engine read
```

**What the Makefile Does:**
1. Creates output directories (performance_results/, logs/)
2. Runs pytest with all 18 V1 read configurations in parallel
3. Collects JSON results to performance_results/
4. Automatically updates reports/v1_read_performance.md
5. Displays summary of updated configurations

**Expected Runtime:**
- ~18 configurations × ~30-60 seconds each = ~10-20 minutes total
- Parallel execution with 8 workers reduces wall time

**Output Files:**
```
performance_results/
├── v1_read_perf_dw128_bs256_SRAM_lat3.json
├── v1_read_perf_dw128_bs256_DDR3_lat60.json
├── v1_read_perf_dw128_bs256_DDR4_lat100.json
├── ... (15 more configurations)

reports/
└── v1_read_performance.md  ← AUTOMATICALLY UPDATED!
```

### Step 2: Verify Report Updates

**Check Updated Report:**
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream

# View populated report
cat reports/v1_read_performance.md

# Check specific configuration
grep "SRAM" reports/v1_read_performance.md
grep "DDR4" reports/v1_read_performance.md
```

**Expected Changes:**
- All "TBD" values replaced with actual metrics
- Total cycles, bandwidth, efficiency populated
- Tables complete for all 18 configurations

### Step 3: Manual Report Update (If Needed)

**Update Script:** `bin/update_performance_reports.py`

**Usage:**
```bash
# Update specific version/engine
./bin/update_performance_reports.py --version v1 --engine read

# Update all reports from all JSON results
./bin/update_performance_reports.py --version all --engine all

# Specify custom directories
./bin/update_performance_reports.py \
    --json-dir custom_results/ \
    --reports-dir custom_reports/
```

**Script Features:**
- Parses JSON results by config (version, engine, data width, burst size, memory type)
- Finds matching table rows in markdown reports
- Replaces TBD values with actual metrics
- Preserves markdown formatting
- Reports which configurations were updated

### Step 4: Create DMA Performance Model

**File:** `bin/dma_model.py`

**Purpose:** Mathematical model to predict V1/V2/V3 performance based on:
- Memory latency
- Burst length
- Data width
- Queue depth (V2/V3)
- Outstanding transactions (V2/V3)

**V1 Model (Single Outstanding):**
```python
def v1_bandwidth_model(latency, burst_len):
    """
    V1 uses single outstanding transaction.

    Args:
        latency: Memory latency in cycles
        burst_len: Burst length in beats

    Returns:
        bandwidth in beats/cycle
    """
    # V1 timeline for one burst:
    # - 1 cycle: AR handshake
    # - latency cycles: wait for first beat
    # - burst_len cycles: receive data beats
    # - 1 cycle: completion strobe

    cycles_per_burst = 1 + latency + burst_len + 1
    beats_per_burst = burst_len

    return beats_per_burst / cycles_per_burst

# Example:
# SRAM (lat=3, burst=16): 16 / (1+3+16+1) = 16/21 = 0.76 beats/cycle
# DDR4 (lat=100, burst=16): 16 / (1+100+16+1) = 16/118 = 0.136 beats/cycle
```

**V2 Model (Command Pipelined):**
```python
def v2_bandwidth_model(latency, burst_len, queue_depth):
    """
    V2 uses command queue to hide latency.

    Steady state: 1 beat per cycle (fully pipelined)
    Startup: queue_depth bursts to fill pipeline
    """
    # Startup phase: fill command queue
    startup_cycles = queue_depth * (1 + latency)

    # Steady state: 1 beat/cycle
    steady_state_bw = 1.0

    # For large number of commands, approaches 1.0 beats/cycle
    # For 1000 commands at burst_len=16:
    total_bursts = 1000 / (burst_len + 1)  # Account for completion cycles
    total_cycles = startup_cycles + (total_bursts - queue_depth) * burst_len
    total_beats = 1000 * burst_len

    return total_beats / total_cycles
```

### Step 5: Validate Model Against Empirical Data

**Script:** `bin/validate_dma_model.py`

```python
#!/usr/bin/env python3
"""Validate DMA model predictions against empirical test results."""

import json
from pathlib import Path
from dma_model import v1_bandwidth_model, v2_bandwidth_model

def compare_model_vs_empirical():
    """Compare model predictions to actual test results."""

    results_dir = Path('dv/tests/performance_results')

    print(f"{'Config':<30} {'Empirical':<15} {'Model':<15} {'Error':<10}")
    print(f"{'-'*70}")

    for json_file in sorted(results_dir.glob('v1_read_perf_*.json')):
        with open(json_file, 'r') as f:
            result = json.load(f)

        config = result['config']
        metrics = result['metrics']

        # Extract parameters
        latency = config['memory_latency_cycles']
        burst_len = config['beats_per_burst']

        # Get empirical bandwidth
        empirical_bw = metrics['bandwidth_beats_per_cycle']

        # Calculate model prediction
        model_bw = v1_bandwidth_model(latency, burst_len)

        # Calculate error
        error_percent = abs(empirical_bw - model_bw) / empirical_bw * 100

        config_str = f"dw={config['data_width']},bs={config['burst_size_bytes']},{config['memory_type']}"
        print(f"{config_str:<30} {empirical_bw:<15.4f} {model_bw:<15.4f} {error_percent:<10.2f}%")

if __name__ == '__main__':
    compare_model_vs_empirical()
```

---

## Expected V1 Baseline Results

Based on PRD targets:

| Data Width | Burst Size | Memory | Latency | Expected BW (beats/cycle) |
|------------|------------|--------|---------|---------------------------|
| 128 | 256B (16 beats) | SRAM | 3 | ~0.76 (76%) |
| 128 | 256B (16 beats) | DDR3 | 60 | ~0.21 (21%) |
| 128 | 256B (16 beats) | DDR4 | 100 | ~0.14 (14%) |
| 256 | 512B (16 beats) | SRAM | 3 | ~0.76 (76%) |
| 256 | 512B (16 beats) | DDR3 | 60 | ~0.21 (21%) |
| 256 | 512B (16 beats) | DDR4 | 100 | ~0.14 (14%) |

**Note:** Bandwidth is independent of data width (measured in beats/cycle)
**Note:** Longer bursts improve efficiency (amortize overhead)

---

## Next Actions

1. **Fix test_v1_baseline_read.py** to use testbench API properly
2. **Run V1 baseline tests** (18 configurations)
3. **Create bin/dma_model.py** with V1/V2/V3 analytical models
4. **Create bin/validate_dma_model.py** to compare model vs empirical
5. **Populate v1_read_performance.md** with actual data
6. **Iterate on model** to minimize error vs empirical results
7. **Use validated model** to predict V2/V3 performance before implementation

---

**Last Updated:** 2025-10-28

