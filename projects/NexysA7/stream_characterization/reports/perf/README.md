# perf/ — STREAM DMA characterization runs

CSV exports of FPGA characterization measurements. Methodology: see
`projects/NexysA7/stream_characterization/DMA_UTILIZATION_MEASUREMENT.md`.

## Files

| File | Source | Rows | Notes |
|---|---|---|---|
| `char_matrix_2026-06-05.csv` | full default matrix | 40 | desc x ch sweep at 1MB/desc |
| `respdelay_sweep_2026-06-05.csv` | resp-delay axis | 32 | 4 configs x 8 delays (0..64 cyc) |

## Columns

- `date`, `time`: wall clock of the run
- `config`, `channels`, `descriptors`, `desc_KB`: workload axes
- `mb_moved`, `dma_time_s`, `throughput_MBps`: raw transfer metrics
- `datapath_{R,W,E2E}_pct`: harness-reported steady-state productive% (definition 2.1)
- `{R,W}_{prod,bp,starv}_pct`: four-bucket breakdown of the data-phase window (Section 3)
- `E2E_util_pct`: derived as `throughput / 1600 MB/s * 100` (single-bus theoretical max @ 100 MHz, 128b)
- `overhead_delta_pp`: `datapath_E2E_pct - E2E_util_pct` — the methodology doc's overhead summary
- `resp_delay_cycles` (sweep only): per-beat R+B hold injected by axi_response_delay

## Reproduce

```bash
cd flows-stream-bridge/host
python3 run_characterization.py --port /dev/ttyUSB2                                  # full matrix
python3 run_characterization.py --port /dev/ttyUSB2 \
    --configs 1desc_1ch_1MB 16desc_1ch_1MB 16desc_4ch_1MB 16desc_8ch_1MB \
    --resp-delays 0,1,2,4,8,16,32,64                                                 # resp-delay axis
```
