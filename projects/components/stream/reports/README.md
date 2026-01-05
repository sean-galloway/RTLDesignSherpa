<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# STREAM Performance Reports

This directory contains sustained bandwidth performance reports for V1/V2/V3 AXI engine configurations.

---

## Report Structure

**6 Markdown Files:**

| File | Configuration | Status | Data Populated |
|------|---------------|--------|----------------|
| `v1_read_performance.md` | V1 Read (Single Outstanding) | Template | Awaiting baseline |
| `v1_write_performance.md` | V1 Write (Single Outstanding) | Template | Awaiting baseline |
| `v2_read_performance.md` | V2 Read (Command Pipelined) | Pending | After V2 impl |
| `v2_write_performance.md` | V2 Write (Command Pipelined) | Pending | After V2 impl |
| `v3_read_performance.md` | V3 Read (Out-of-Order) | Pending | After V3 impl |
| `v3_write_performance.md` | V3 Write (Out-of-Order) | Pending | After V3 impl |

---

## Test Methodology

**Common Test Parameters:**
- **Test Duration:** 1000 commands issued back-to-back
- **Data Widths:** 128 bits (16 bytes/beat), 256 bits (32 bytes/beat)
- **Burst Sizes:** 256B, 512B, 1024B
- **Memory Types:** SRAM (3-cycle latency), DDR3 (60-cycle), DDR4 (100-cycle)
- **Measurement:** Sustained bandwidth in steady state

**Performance Metrics Tracked:**
1. Total cycles (from first command to completion)
2. Total beats transferred
3. Bandwidth (beats/cycle)
4. Bandwidth (GB/s @ 200MHz clock)
5. Efficiency (% of ideal 1.0 beats/cycle)

---

## V1 Baseline (Priority)

**Next Step:** Execute V1 baseline performance tests

**Test Scripts to Create:**
- `test_performance_baseline_v1_read.py`
- `test_performance_baseline_v1_write.py`

**Workflow:**
1. Create performance measurement test
2. Run tests with all parameter combinations:
   - 2 data widths × 3 burst sizes × 3 memory types = 18 configurations per engine
3. Collect metrics (cycles, beats, bandwidth, efficiency)
4. Populate `v1_read_performance.md` and `v1_write_performance.md` TBD fields
5. Generate summary comparison tables

---

## V2 Performance (After V2 Implementation)

**Prerequisites:**
- V2 RTL implementation complete
- V2 functional tests passing
- V1 baseline established for comparison

**Additional Parameters:**
- `CMD_QUEUE_DEPTH`: 4, 8
- `MAX_OUTSTANDING`: 4, 8

**Comparison Goals:**
- Achieve 6.7x improvement vs V1 for DDR4
- Validate command pipelining effectiveness
- Measure area efficiency (throughput per LUT)

---

## V3 Performance (After V3 Implementation)

**Prerequisites:**
- V2 implementation complete and validated
- V2 performance targets met
- OOO memory model available for testing

**Additional Parameters:**
- `ENABLE_OOO_READ`: 1 (read engine)
- `ENABLE_OOO_DRAIN`: 1 (write engine)
- `CMD_QUEUE_DEPTH`: 8, 16

**Comparison Goals:**
- Achieve 7.0x improvement vs V1 for DDR4
- Quantify OOO benefit vs V2 in-order
- Determine when V3 area cost is justified

---

## Report Generation Workflow

### Automated Workflow (Recommended)

**Run tests and auto-update reports in one command:**

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/dv/tests/performance_tests

# V1 Baseline
make v1-baseline           # Read + write (auto-updates both reports)
make v1-read-baseline      # Read only (auto-updates v1_read_performance.md)

# V2 Performance (after implementation)
make v2-performance        # Read + write

# V3 Performance (after implementation)
make v3-performance        # Read + write

# All baselines
make all-baselines
```

**What Happens:**
1. ✅ Tests run with parallel execution (8 workers)
2. ✅ JSON results saved to performance_results/
3. ✅ Markdown reports automatically updated
4. ✅ Summary displayed with updated configurations

### Manual Workflow (Advanced)

**Step 1: Run Performance Tests**

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/dv/tests/performance_tests

# V1 Baseline
pytest test_v1_baseline_read.py -v -s -n 8
pytest test_v1_baseline_write.py -v -s -n 8  # (when created)

# V2/V3 Performance (after implementation)
pytest test_v2_*.py -v -s -n 8
pytest test_v3_*.py -v -s -n 8
```

**Step 2: Update Reports from JSON**

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream

# Update specific version/engine
./bin/update_performance_reports.py --version v1 --engine read

# Update all reports
./bin/update_performance_reports.py --version all --engine all
```

**Step 3: Verify Updates**

```bash
# Check updated report
cat reports/v1_read_performance.md

# View JSON results
ls -lh dv/tests/performance_results/
cat dv/tests/performance_results/v1_read_perf_dw128_bs256_SRAM_lat3.json
```

---

## Performance Targets (from PRD)

### V1 (Single Outstanding)
- **DDR4:** 0.14 beats/cycle (14% efficiency)
- **SRAM:** 0.40 beats/cycle (40% efficiency)
- **Area:** ~1,250 LUTs per engine

### V2 (Command Pipelined)
- **DDR4:** 0.94 beats/cycle (94% efficiency) → **6.7x vs V1**
- **SRAM:** 0.85 beats/cycle (85% efficiency) → **2.1x vs V1**
- **Area:** ~2,000 LUTs per engine (1.6x vs V1)
- **Area Efficiency:** 4.19x throughput per unit area (best)

### V3 (Out-of-Order)
- **DDR4:** 0.98 beats/cycle (98% efficiency) → **7.0x vs V1**
- **SRAM:** 0.92 beats/cycle (92% efficiency) → **2.3x vs V1**
- **Area:** ~3,500 LUTs per engine (2.8x vs V1)
- **Area Efficiency:** 2.50x throughput per unit area

---

## Report Update Checklist

### V1 Baseline
- [ ] Create performance test scripts
- [ ] Run 1000-command tests for all configurations
- [ ] Populate `v1_read_performance.md` TBD values
- [ ] Populate `v1_write_performance.md` TBD values
- [ ] Validate results match expected ~0.14 (DDR4) and ~0.40 (SRAM)

### V2 Reports
- [ ] Implement V2 RTL (read + write engines)
- [ ] Create V2 performance tests
- [ ] Run tests with queue depths 4 and 8
- [ ] Populate `v2_read_performance.md`
- [ ] Populate `v2_write_performance.md`
- [ ] Validate 6.7x improvement achieved

### V3 Reports
- [ ] Implement V3 RTL (OOO logic)
- [ ] Create V3 performance tests with OOO memory model
- [ ] Run tests with queue depths 8 and 16
- [ ] Populate `v3_read_performance.md`
- [ ] Populate `v3_write_performance.md`
- [ ] Validate 7.0x improvement achieved
- [ ] Document V3 vs V2 trade-off analysis

---

## Directory Contents

```
reports/
├── README.md                      # This file
├── v1_read_performance.md         # V1 read baseline (awaiting data)
├── v1_write_performance.md        # V1 write baseline (awaiting data)
├── v2_read_performance.md         # V2 read (pending implementation)
├── v2_write_performance.md        # V2 write (pending implementation)
├── v3_read_performance.md         # V3 read (pending implementation)
└── v3_write_performance.md        # V3 write (pending implementation)
```

---

**Created:** 2025-10-28
**Last Updated:** 2025-10-28
**Next Action:** Create V1 baseline performance tests and populate V1 reports

