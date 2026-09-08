# Troubleshooting

## Current board state

Sim timing is closed; on-board DDR2 runs but is **gated by PHY calibration**. A
clean read-leveling eye is found only at **`t_phy_wrlat = 0`** (bitslip 0, taps
0–11, centre tap 5). The default of `t_phy_wrlat = 4` used by `--simple` /
`--char` breaks the write path ("no passing tap").

**Known-good board config:** `t_phy_wrlat = 0`, `t_rddata_en = 6`, `rd_phase = 0`,
`rddata_delay = 8`, `cmd_delay = 1`.

After the runtime page-policy fix, OPEN vs CLOSE page policy moved read
throughput from ~12.7 MB/s to ~112 MB/s (8.8×) and write to ~44 MB/s (3.5×). For
reference, LiteDRAM on the same board reaches ~600 MB/s peak (300 MT/s memtest).

## Sticky errors look like a wedge

`STATUS.any_error` is **sticky** and is cleared by `CTRL.clear_stats`, **not**
`soft_reset`. A single failed read latches `rd_error`; every subsequent engine
wait then returns False and looks like a hardware wedge that isn't one. Clear
stats between phases. Note `pumice_master.wait_engine()` waits on **one** engine
(write-then-read is phased); a "wait for both" would hang.

## Known bugs / bounds

| Symptom | Cause / workaround |
|---------|--------------------|
| Read engine wedges at ~4790 txns | `rd_cmd_cam` ceiling — keep board runs `txn ≤ 1024` for clean completion; the perf *rate* is still valid at scale |
| `row_major` wedges immediately | every burst is a row-miss — needs the wedge fix before it can be characterized |
| Intermittent 1–11 beat mismatches at scale | clean at `txn ≤ 1024` |
| `col_major` stride overflow | stride 16 KB × txn > 8192 exceeds 128 MB → address alias; host bounds `col_major` to `txn ≤ 8192` |
| `synth_mask_obs` / `lookahead_max_obs` read 0 | init never set `CTRLR_CAP` — advertise capability first |

: Known issues and bounds

## Cannot find the board

The USB-UART re-enumerates across reboots/replugs. `--port auto` (default) probes
each `/dev/ttyUSB*`, reads `BUILD_ID`, and picks the one answering `0x44445232`.
If none respond it raises "no pumice DDR2 char harness responded … is the board
powered and programmed?" — confirm the bitstream is flashed and the FTDI cable is
free.

## a7ddrphy is not simulatable

Verilator cannot model OSERDESE2 / ISERDESE2 / IDELAYE2, so sim connects at the
DFI level with `DFISlavePHY` + `MemoryModel`. Read-eye / DQS-gate / pin-LOC
problems are silicon-only. Regenerating the real PHY requires **Python 3.10
only** (migen's CSR-name tracer breaks on 3.11/3.12):

```bash
uv venv --python 3.10 /tmp/litex-venv310 && source /tmp/litex-venv310/bin/activate
uv pip install migen "litex==2024.12" "litedram==2024.12" pyyaml
cd projects/fpga-systems/NexysA7/pumice/build-perf
python3 bin/elaborate_a7ddrphy.py --out rtl-vivado/a7ddrphy/a7ddrphy_generated.v
python3 bin/elaborate_a7ddrphy.py --dump-csr-map      # CSR offsets for firmware
```

## debug_sram trace ring is disabled on this build

`DEBUG_SRAM_WORDS` was shrunk 32768 → **512** — the full ring needed ~44 K
distributed-RAM cells (2.4× over the 100T budget) and blocked `place_design`. The
256-KB address *window* is unchanged (accesses > 2 KB alias into the ring); the
ring is effectively unused here. Raise it on a larger device.

## LiteDRAM baseline flow

`flows-litedram-uart` is wired and lint-clean but board bring-up is gated. The
default `./regen.sh` builds an empty BIOS ROM (`--no-compile-software`) so the
core never asserts `init_done` — use `./regen.sh --bios` (needs riscv-gcc). The
host variant (harness_csr at base 0, no pumice APB cfg) is still TODO.
