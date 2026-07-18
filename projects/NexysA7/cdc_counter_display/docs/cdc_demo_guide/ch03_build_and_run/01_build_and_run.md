# Build and Run

All commands are run from `projects/NexysA7/cdc_counter_display/` after sourcing
the Python environment:

```bash
cd /path/to/RTLDesignSherpa
source env_python            # sets SIM=verilator, PATH, PYTHONPATH, REPO_ROOT
cd projects/NexysA7/cdc_counter_display
```

## The workflow at a glance

```
make regmap  ->  make consistency  ->  make sim-demo   (prove it in simulation)
                                          |
                                          v
             make build-demo  ->  make program-demo  ->  run_cdc_demo.py   (on the board)
```

## Make targets

### Simulation

| Target | What it does |
|--------|--------------|
| `make sim` | Phase-1 CocoTB sim of `cdc_counter_display_top`. |
| `make sim-demo` | Phase-2 **UART-equivalence** sim: wraps the real `uart_axil_bridge` + harness and runs the host programs over a cocotb UART master (`dv/tests/test_cdc_demo_uart.py`). Four tests: smoke, press, cfg_load, cdc_mode. |

: Simulation make targets

### Register collateral

| Target | What it does |
|--------|--------------|
| `make regmap` | Regenerate `dv/tbclasses/cdc_demo_csr_regmap.py` from `rtl/cdc_demo_csr.rdl`. Run after editing the RDL — never hand-edit the regmap. |
| `make consistency` | Guard test: the generated regmap must match the hand-written `cdc_demo_harness.sv` (offsets + per-counter block). |

: Register-collateral make targets

### Bitstream

| Target | What it does |
|--------|--------------|
| `make build-demo` | Build the phase-2 bitstream `cdc_demo.bit` with Vivado (~5–10 min). |
| `make program-demo` | Flash the board with `cdc_demo.bit`. |
| `make lint-demo` | Verilator lint of the phase-2 RTL (Xilinx clocking primitives are stubbed — see Chapter 6). |

: Bitstream make targets

## The host CLI (`host/run_cdc_demo.py`)

The CLI builds a `CdcDemoDriver`, resolves the serial port (auto-probes every
`/dev/ttyUSB*` for the `CDC1` build ID unless `--port` is given), and dispatches
to the authored-once programs in `cdc_programs.py`.

```bash
# Verify the link and dump all four counters' defaults
python3 host/run_cdc_demo.py smoke

# Inject 1000 host presses to counter 2; checks VALUE = INIT + 1000*INCREMENT
python3 host/run_cdc_demo.py press --counter 2 --count 1000

# CFG_LOAD reload check / CDC_MODE round-trip
python3 host/run_cdc_demo.py cfg-load --counter 1
python3 host/run_cdc_demo.py cdc-mode --counter 0

# Real-time monitor of all four counters
python3 host/run_cdc_demo.py monitor

# The headline demo: NO-CDC + auto-increment, sweep the clock slow -> fast
python3 host/run_cdc_demo.py watch-fail --counter 2

# Force a specific port instead of autodetect
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 smoke
```

Each subcommand prints a human-readable result and returns a non-zero exit code
on failure, so the CLI doubles as a board bring-up smoke test.

### The "watch it fail" procedure

1. Program the board (`make program-demo`).
2. `python3 host/run_cdc_demo.py watch-fail --counter 2` sets counter 2 to
   NO-CDC + auto-increment, sets `DISP_SELECT` to 2, and sweeps `div_pickoff`
   from slow to fast, sampling `VALUE` at each step.
3. Read the on-board 7-seg: clean counting at slow pickoffs, visible scramble at
   fast pickoffs. Compare against a counter left in a safe mode — it stays clean.
