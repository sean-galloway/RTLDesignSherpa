# Build and Run

Every Makefile requires `REPO_ROOT`, so source the environment first:

```bash
cd /path/to/RTLDesignSherpa && source env_python
cd projects/NexysA7/stream_characterization
```

## Make targets

The **top-level Makefile** is a per-flow factory — targets take a flow suffix:

```bash
make bitstream-stream-bridge     # build the primary flow
make program-stream-bridge
make sim-stream-bridge
make all-bitstreams              # every built flow
make docs                        # render the reports
make help                        # full 2x2 matrix + targets
```

The **primary flow** (`flows-stream-bridge/Makefile`) has the detailed targets:

| Target | What it does |
|--------|--------------|
| `make bitstream` | regen-bridges + verify-sim + full P&R (~10–30 min) → `bitstream/stream_char.bit` |
| `make program` | JTAG flash |
| `make sim` | cocotb regression (`dv/tests` → `run-all-full-parallel`) |
| `make area` | out-of-context bare-`stream_top_ch8` area report |
| `make synth` / `make utilization` / `make timing` | synth-only + reports |
| `make regen-bridges` / `make regen-regs-nomon` | regenerate the bridge / register collateral |
| `make verify-sim` | pre-bitstream gate (`-k "ping or csr_read"`); bypass with `BITSTREAM_SKIP_VERIFY=1` |

: flows-stream-bridge make targets

The `dv/tests/Makefile` runs the cocotb suite by level: `run-all-{gate,func,full}[-parallel][-wave]`
(`TEST_LEVEL`, 48-worker xdist, `--reruns 3`).

```bash
cd flows-stream-bridge
make bitstream
make program
make sim
```

## Host tools (`flows-stream-bridge/host/`)

All default `--port auto` (autodetect) and `--baud 115200`.

**`run_characterization.py`** — the main sweep runner (40-config matrix:
{1,2,4,8,16} desc/ch × 1–8 ch × 1 MB):

```bash
./run_characterization.py --port /dev/ttyUSB1 --channels 1 2 4 8 --size 1MB --csv fpga_suite.csv
./run_characterization.py --resp-delays 0,128 --compression --mon-config debug-compl
```

`--configs`, `--phase`, `--resp-delays[-wr]`, `--rd-prefetch`, `-o out.json`,
`--dry-run`; env `XFER_BEATS=b` sets burst size.

**`characterize.py`** — a lighter one-row-per-config sweep (cycles + MB/s).
**`stream_ext_suite.py`** / **`stream_ext_char.py`** — extended row/col addressing
(needs the DUT built with `USE_ROW_COL_MAJOR_ADDRESSING=1`).
**`per_source_capture.py`** — per-source MonBus isolation for compression datasets.
**`dump_status.py`** — quick sanity (prints BUILD_ID `0x53545243`).
**`dump_monbus_sram.py`** — dump the trace ring (`--base 0x00040000` STREAM,
`0x000c0000` bridge). By-name access helpers: `stream_addrs.A()` (STREAM APB),
`harness_addrs.H()` (harness CSR), `stream_device.Stream`.

Exact reproduce commands live in the `reports/perf/README.md` and
`reports/compression/README.md` appendices.

## Port autodetect and identity

`--port auto` probes each `/dev/ttyUSB*` by writing the magic `0xC0FFEE5A` to the
harness `SCRATCH` CSR and reading it back; the board that echoes is the harness.
Confirm it is alive with `dump_status.py` — the `BUILD_ID` at harness CSR `0x24`
reads `0x5354_5243` ("STRC").
