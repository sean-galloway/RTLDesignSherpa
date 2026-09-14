# Build and Run

All commands assume the Python environment is sourced (sets `REPO_ROOT`,
`SIM=verilator`, `PATH`, `PYTHONPATH`):

```bash
cd /path/to/RTLDesignSherpa && source env_python
cd projects/fpga-systems/NexysA7/pumice/build-perf
```

## `build-perf` make targets

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

: build-perf make targets

The other Makefiles: `flows-litedram-uart/Makefile` (`make regen` /
`make bitstream` / `make program` for the LiteDRAM baseline) and
`ddr2_char_framework/dv/tests/Makefile` (the cocotb macro suite: `make run`,
`run-smoke`, `run-<shape>`, and parallel `run-{gate,func,full}-parallel`).

## The host programs (`build-perf/host/`)

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

## The performance sweeps (`build-perf/bin/`)

Three scripts, each isolating one axis. Run them from `build-perf/` after
`make program`; all three write JSON or a table and none need arguments.

**`axlen_sweep.py`** — bandwidth against AXI burst length at a fixed
outstanding budget. This is the headline read/write figure and the
Little's-law fit.

**`outstanding_sweep.py`** — bandwidth against the number of bursts in flight,
at a fixed AxLEN. This is the DIRECT test of the latency-bound claim: if a
shortfall is Little's law, the knee sits near `latency/AxLEN` and moves as
`1/AxLEN`. A knee well before that names whatever the real limit is instead.
The runtime `max_outstanding` dial and the 32-deep ceiling exist for this sweep.

**`bank_gap_sweep.py`** (plot with `plot_bank_gap.py`) — N writers and N readers
running CONCURRENTLY, one bank apiece, across inter-burst gap 0..15, three
address orders, at 4+4 / 3+3 / 2+2 / 1+1 engines. It answers how much idle the
controller absorbs before bandwidth falls.

```bash
python3 bin/axlen_sweep.py
python3 bin/outstanding_sweep.py
python3 bin/bank_gap_sweep.py && python3 bin/plot_bank_gap.py reports/bank_gap_sweep.json
```

Useful env: `GENS`, `GAPS` (a named sweep — `full`, `knee`, `ends` — or a
literal list), `TXN`, and `PREFILL`. **Leave `PREFILL` at its default `point`.**
It re-fills the whole device before every measurement so points are
independent; `PREFILL=once` exists only for a deliberate damage-accumulation
experiment, not to go faster. The gap range stops at 15 because the CSR field
is four bits — asking for 16 programs 0 and silently re-measures back-to-back
under a different label.

Reading the output: the knee column is the largest gap still within 3% of the
gap-0 value. A FLAT curve at high generator counts is a result, not a broken
axis — a gap only bends the curve once aggregate demand drops below what the
controller can deliver, and four generators at gap 15 are still over-subscribing
it. Points whose data failed verification are ringed in the plots and listed as
`FAIL:` lines with their stray-beat count; their bandwidth is still a real
measurement, but the configuration is not a clean operating point.

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
