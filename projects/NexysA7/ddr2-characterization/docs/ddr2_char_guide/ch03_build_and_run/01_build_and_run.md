# Build and Run

All commands assume the Python environment is sourced (sets `REPO_ROOT`,
`SIM=verilator`, `PATH`, `PYTHONPATH`):

```bash
cd /path/to/RTLDesignSherpa && source env_python
cd projects/NexysA7/ddr2-characterization/flows-ours-uart
```

## `flows-ours-uart` make targets

`UART ?= /dev/ttyUSB1`, `BAUD ?= 115200`, `VIVADO ?= vivado`.

| Target | Action |
|--------|--------|
| `make lint` | Verilator lint of `ddr2_char_top` via the harness filelist |
| `make project` / `make synth` | create Vivado project / synth-only + reports |
| `make bitstream` | full synth + impl + bitgen (~10–30 min) → `bitstream/ddr2_char.bit` |
| `make bitstream-ila` | same, plus an ILA on the DFI boundary → `.bit` + `.ltx` |
| `make program` | flash the board |
| `make utilization` / `make timing` | print the latest reports |
| `make smoke` | `host/run_smoke.py` — link + one linear WR/RD integrity pass |
| `make status` | `host/ddr2_char.py` — one-shot BUILD_ID + status dump |
| `make level` | `host/pumice_master.py --level-only` — a7ddrphy leveling |
| `make simple` | `host/pumice_master.py --simple` — init + one write→read pass |
| `make characterize` | `host/pumice_master.py --full` — full workload sweep |
| `make sweep-rddly` / `make train-deskew` | PHY timing sweeps |
| `make host-test` | `pytest host/test_pumice_master.py` (mock UART, no board) |
| `make sim` / `sim-smoke` / `sim-simple` / `sim-level` | run the **same** host programs in cocotb sim |
| `make clean` / `clean-all` | remove build artifacts |

: flows-ours-uart make targets

The other Makefiles: `flows-litedram-uart/Makefile` (`make regen` /
`make bitstream` / `make program` for the LiteDRAM baseline) and
`ddr2_char_framework/dv/tests/Makefile` (the cocotb macro suite: `make run`,
`run-smoke`, `run-<shape>`, and parallel `run-{gate,func,full}-parallel`).

## The host programs (`flows-ours-uart/host/`)

The port defaults to `--port auto`, which probes every `/dev/ttyUSB*` and keeps
the board that answers `BUILD_ID == 0x44445232` ("DDR2").

**`run_smoke.py`** — the first thing to run after flashing. Programs a linear
WR+RD workload, kicks both engines, and checks CRC / cycles / perf.

```bash
python3 host/run_smoke.py --port /dev/ttyUSB1 --txn 1024 --blen 8 --seed 0xDEADBEEF
```

Pass = BUILD_ID matches, both engines done, `CRC_ACTUAL == CRC_EXPECTED`,
`BEATS_MISMATCHED == 0`, and `TIMER.pass`.

**`pumice_master.py`** — the orchestration program; one mode is required:

```bash
python3 host/pumice_master.py --port /dev/ttyUSB1 --level-only   # PHY read/write leveling
python3 host/pumice_master.py --port /dev/ttyUSB1 --simple       # init + one write→read pass
python3 host/pumice_master.py --port /dev/ttyUSB1 --full         # full workload sweep
python3 host/pumice_master.py --port /dev/ttyUSB1 --char --char-profile matrix --char-scale 1000 --csv out.csv
```

Useful options: `--no-level`, `--rd-phase`, `--rd-delay`, `--char-configs`,
`--char-scale N` (≈1000 on FPGA), `--level-cache JSON`, `--clk-mhz`.

**`ddr2_char.py`** — the driver library plus a one-shot status CLI
(`python3 host/ddr2_char.py --port auto`). It exports `DDR2CharDriver`, the
base-address constants, and the enum constants used throughout.

## Typical bring-up sequence

```bash
make bitstream
make program
make smoke   UART=/dev/ttyUSB1      # link + integrity
make level                          # find the read/write eye
make simple                         # one clean write→read
make characterize                   # full sweep -> CSV
# no board? prove the same programs in sim:
make sim
```
