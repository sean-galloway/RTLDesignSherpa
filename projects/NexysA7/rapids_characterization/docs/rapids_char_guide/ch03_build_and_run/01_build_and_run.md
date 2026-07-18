# Build and Run

All commands assume the Python environment is sourced (the Makefile hard-fails
without `REPO_ROOT`):

```bash
cd /path/to/RTLDesignSherpa && source env_python
cd projects/NexysA7/rapids_characterization/flows-rapids-beats
```

## Make targets (`flows-rapids-beats/Makefile`)

| Target | What it does |
|--------|--------------|
| `make sim` | cocotb harness self-check (sink + source, multi-channel) |
| `make verify-sim` | pre-bitstream sim gate (`-k sink`); bypass with `BITSTREAM_SKIP_VERIFY=1` |
| `make project` / `make synth` | create Vivado project / synth-only + utilization |
| `make bitstream` | full synth + impl + bitgen (depends on `verify-sim`) |
| `make program` | flash the board over JTAG |
| `make smoke` | fast golden-validated UART confidence check |
| `make suite` | full UART sweep → JSON under `reports/` |
| `make characterize` | full UART campaign on `PORT` |
| `make flow` | sim → bitstream → program → characterize |
| `make utilization` / `make timing` | print the latest reports |
| `make clean` / `make clean-all` | remove artifacts |

: flows-rapids-beats make targets

Knobs: `CHANNELS` (4 on nexys, 8 on genesys2 — passed as both the build generic
and the host `--channels`, kept in lockstep), `BEATS=8`, `PORT=/dev/ttyUSB1`,
`BOARD=nexys|genesys2`, `BITSTREAM_SKIP_VERIFY=1`.

```bash
make sim                                  # cocotb self-check
make bitstream                            # Nexys A7, 4 channels
make bitstream BOARD=genesys2 CHANNELS=8  # Genesys 2, 8 channels
make program
make smoke PORT=/dev/ttyUSB1
make suite CHANNELS=4
```

The Vivado build targets part `xc7a100tcsg324-1`, top `rapids_char_top`, with
board-fit generics `NUM_CHANNELS=4`, `SRAM_DEPTH=256`, `DESC_RAM_ENTRIES=256`.
Programming is pinned to a specific JTAG serial so the flash and the UART
campaign land on the same board (override `RAPIDS_CHAR_JTAG_SERIAL`).

## The host campaign (`flows-rapids-beats/host/`)

The port defaults to `--port auto`, which probes each `/dev/ttyUSB*` and keeps
the board whose region-2 `CTRL`/`ID` reads `0x52415031` ("RAP1").

**`run_characterization.py`** — the campaign runner (sink then source):

```bash
# Full campaign, verbose
./run_characterization.py --port /dev/ttyUSB1 --channels 4 --active 4 --beats 8 -v

# One path only
./run_characterization.py --sink-only   --channels 4
./run_characterization.py --source-only --channels 4

# Smoke (both paths, quick) and full suite (matrix → JSON)
./run_characterization.py --smoke  --channels 4
./run_characterization.py --suite  --suite-channels 1,2,4 --suite-beats 1,4,8,16 \
        --suite-bp off,on --suite-seeds default,0x12345678
```

Exit codes: `0` all pass, `1` a self-check failed, `2` no UART link / wrong ID.

**`dump_status.py`** — a STATUS / totals / CRC snapshot
(`./dump_status.py --port /dev/ttyUSB1 --channels 4`). Other host modules:
`descriptor_builder.py` (256-bit descriptor builder), `rapids_char_golden.py`
(standalone golden CRC), `rapids_char_io.py` (transport + autodetect).

## Typical sequence

```bash
make sim                            # prove the harness self-check
make bitstream                      # (runs verify-sim first)
make program
make smoke PORT=/dev/ttyUSB1        # golden-validated link check
make suite CHANNELS=4               # full sweep -> reports/*.json
```
