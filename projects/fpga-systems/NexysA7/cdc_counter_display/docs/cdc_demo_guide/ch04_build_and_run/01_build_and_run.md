# Build and Run

All commands are run from `projects/fpga-systems/NexysA7/cdc_counter_display/` after sourcing
the Python environment:

```bash
cd /path/to/RTLDesignSherpa
source env_python            # sets SIM=verilator, PATH, PYTHONPATH, REPO_ROOT
cd projects/fpga-systems/NexysA7/cdc_counter_display
```

## The workflow at a glance

```
make regmap  ->  make consistency  ->  make sim        (prove it in simulation)
                                          |
                                          v
             make bitstream  ->  make program  ->  make host-cdc_demo   (on the board)
```

Targets go to `build-demo` by default; add `BUILD=phase1` for the button-only
build. All flow logic lives in the global `make/fpga_flow.mk` (`make targets`
lists what was discovered).

## Make targets

### Simulation

| Target | What it does |
|--------|--------------|
| `make sim BUILD=phase1` | Phase-1 CocoTB sim of `cdc_counter_display_top`. |
| `make sim` | **UART-equivalence** sim: wraps the real `uart_axil_bridge` + harness and runs the host programs over a cocotb UART master (`build-demo/dv/tests/test_cdc_demo_uart.py`). Four tests: smoke, press, cfg_load, cdc_mode. |

: Simulation make targets

### Register collateral

| Target | What it does |
|--------|--------------|
| `make regmap` | Regenerate `build-demo/dv/tbclasses/cdc_demo_csr_regmap.py` from `build-demo/rtl/cdc_demo_csr.rdl`. Run after editing the RDL — never hand-edit the regmap. |
| `make consistency` | Guard test: the generated regmap must match the hand-written `cdc_demo_harness.sv` (offsets + per-counter block). |

: Register-collateral make targets

### Bitstream

| Target | What it does |
|--------|--------------|
| `make bitstream` | Build the demo bitstream `build-demo/fpga/bitstream/cdc_demo.bit` with Vivado (~5–10 min). `make project` creates the Vivado project only; `make synth` stops after synthesis. |
| `make program` | Flash the board (shared board layer, registry-pinned JTAG serial). `make ports` / `make board-info` inspect the board. |
| `make lint` | Verilator lint of the build's filelist closure (Xilinx clocking primitives are stubbed — see Chapter 7). |
| `make utilization` / `make timing` | Print the latest report summaries. |
| `make keep` | Promote the current bitstream + reports out of the clean blast radius. |

: Bitstream make targets

## The host CLI (`build-demo/host/host_cdc_demo.py`)

The CLI builds a `CdcDemoDriver`, resolves the serial port through the shared
board layer (narrows to this board's ports by USB serial, then probes for the
`CDC1` build ID unless `--port` is given), and dispatches to the authored-once
programs in `cdc_programs.py`. Run it as `make host-cdc_demo ARGS=...` or
directly:

```bash
# Verify the link and dump all four counters' defaults
make host-cdc_demo ARGS=smoke

# Inject 1000 host presses to counter 2; checks VALUE = INIT + 1000*INCREMENT
make host-cdc_demo ARGS="press --counter 2 --count 1000"

# CFG_LOAD reload check / CDC_MODE round-trip
make host-cdc_demo ARGS="cfg-load --counter 1"
make host-cdc_demo ARGS="cdc-mode --counter 0"

# Real-time monitor of all four counters
make host-cdc_demo ARGS=monitor

# The headline demo: NO-CDC + auto-increment, sweep the clock slow -> fast
make host-cdc_demo ARGS="watch-fail --counter 2"

# Force a specific port instead of autodetect (direct invocation)
python3 build-demo/host/host_cdc_demo.py --port /dev/ttyUSB1 smoke
```

Each subcommand prints a human-readable result and returns a non-zero exit code
on failure, so the CLI doubles as a board bring-up smoke test.

### The "watch it fail" procedure

1. Program the board (`make program`).
2. `make host-cdc_demo ARGS="watch-fail --counter 2"` sets counter 2 to
   NO-CDC + auto-increment, sets `DISP_SELECT` to 2, and sweeps `div_pickoff`
   from slow to fast, sampling `VALUE` at each step.
3. Read the on-board 7-seg: clean counting at slow pickoffs, visible scramble at
   fast pickoffs. Compare against a counter left in a safe mode — it stays clean.
