# pumice 100 MHz convergence — pre-change perf + timing baseline

Date: 2026-10-20  
Task: Task 1 of 2026-10-20-pumice-100mhz convergence plan

## Git HEAD

```
ecebdada55a5454fa000c753b576ce012c5535ce
```

## Perf suite run

### Exact command

From the repo root, after `source env_python` and `export PYTHONPATH="$(pwd)/bin"`:

```bash
cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests
TEST_TREFI=585 TEST_TXN=1024 python3 -m pytest test_granite_char_perf.py::test_granite_char_perf -v -s 2>&1 | tee /tmp/pumice_base_perf.log
```

### Result

`test_granite_char_perf PASSED` in 277.65 s.

Raw perf dump: `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/logs/perf_dump_test_granite_char_perf.json`

### Per-cell bandwidth table

Run conditions: clk = 74.985 MHz, tREFI = 585, txn = 1024, burst_len = 8, gap = 0.

| family      | wr_cyc | wr_bw (MB/s) | wr_util | rd_cyc | rd_bw (MB/s) | rd_util | mismatched |
|-------------|--------|--------------|---------|--------|--------------|---------|------------|
| incremental | 8,837  | 556.1        | 0.927   | 8,796  | 558.7        | 0.931   | 0          |
| row_major   | 8,620  | 570.1        | 0.950   | 8,641  | 568.7        | 0.948   | 0          |
| col_ilv     | 15,997 | 307.2        | 0.512   | 13,918 | 353.1        | 0.589   | 0          |
| col_major   | 22,238 | 221.0        | 0.368   | 20,042 | 245.2        | 0.409   | 0          |

Notes:
- All families completed write and read phases cleanly (`wr_ok=true`, `rd_ok=true`).
- No mismatched beats.
- Effective JEDEC timings programmed: tRC=5, tRCD=2, tRP=2, tRAS=4, tRFC=11, tREFI=585, tRRD=2, tFAW=4, tWTR=4, tCCD=1, tWR=4, tRTP=2, tRTW=21.

## Timing snapshot

Source OOC run: `/tmp/pumice_timing_head/`
Baseline copy: `/tmp/pumice_timing_baseline_fixed/`

### Totals from `timing_summary.rpt`

| metric                  | value     |
|-------------------------|-----------|
| Total failing endpoints | 518       |
| aclk WNS                | -13.245 ns |
| dfi_clk WNS             | -2.839 ns  |
| aclk TNS                | -695.736 ns |
| dfi_clk TNS             | -902.570 ns |
| Combined WNS            | -13.245 ns |
| Combined TNS            | -1598.306 ns |

## Artifact paths for downstream delta proof (Task 6)

- `BASE_PERF`: `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/logs/perf_dump_test_granite_char_perf.json`
- `BASE_TIMING`: `/tmp/pumice_timing_baseline_fixed/`
  - `bucketized_new.csv`
  - `timing_summary.rpt`
- Tee log: `/tmp/pumice_base_perf.log`
