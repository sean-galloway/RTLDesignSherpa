---
title: Stream host objects
summary: What each object in the stream area IS, which RTL block it drives, and which layer it belongs to - so a new tool composes these instead of growing a fifth copy of the same thing.
---

# Stream host objects

The stream area's host code is a small set of objects over the shared
[[host-stack]]. This note is the catalogue: what each one is, what it talks to,
and where it lives. The layout rules (which directory, which filename prefix)
are [[flow-layout]]; this is the object model those rules arrange.

## The catalogue

| Object | Lives in | Drives | Kind |
|---|---|---|---|
| `stream_env` | `bin/stream_env.py` | nothing -- locates layers | module (import for side effect) |
| `Stream(Device)` | `bin/stream_device.py` | `stream_top_ch8` via `stream_regs` | device |
| `CharacterizationRunner` | `bin/characterization.py` | the harness CSRs + a DMA campaign | runner/library |
| `DescriptorBuilder` | `bin/descriptor_builder.py` | descriptor RAM contents | pure builder |
| `harness_addrs` / `stream_addrs` | `bin/` | by-name addresses + `compose()` | library |
| `bus_meters` | `bin/bus_meters.py` | `axi4_intf_master_observer` bucket CSRs | library + `main()` |
| `rw_perf` / `desc_perf` | `bin/` | in-core RDMON/WRMON/DAXMON windows | library + `main()` |
| `stream_ext_suite` | `bin/stream_ext_suite.py` | row/col traversal cases over `Stream` | library + `main()` |
| `stream_ext_report` | `bin/stream_ext_report.py` | nothing -- formats results | pure formatter |
| `MonitorProgram` + `route_monbus` / `arm_addr_ranges` / `set_timeouts` | `bin/stream_monitors.py` | the in-core DAXMON/RDMON/WRMON cones, group routing, addr-range checker | library (runner hooks) |
| `tally` | `bin/tally.py` | `monbus_tally_axil` CAM load + dense-bin sweep, depth from hardware | library |
| `mon_compress` | `bin/mon_compress.py` | compression measurement over the runner | library + `main()` |
| `mon_err_window` | `bin/mon_err_window.py` | the group's ERROR window: `ERR_SELECT` records read back from memory against `MON_ERR_REC_COUNT` | library + `main()` |
| `bridge_windows` | `bin/bridge_windows.py` | bridge slave windows by name from the TOML; `monbus_capture_window()` (trace) and `monbus_err_window()` (error, top 4 KB of comp_sram) | library |
| `StreamHarnessTB` | `dv/tbclasses/stream_harness_tb.py` | `stream_harness` over UART | testbench (both builds) |
| `MonbusGroupHarness` | `bin/TBClasses/scoreboards/monbus_group/` | a monbus group's trace window, error window (or drain port on the two-port groups) and irq | shared TB collateral |
| `host_*.py` | `build-<n>/host/` | one campaign each | program |

### When a module is BOTH a library and a program

`bus_meters`, `rw_perf`, `desc_perf`, `stream_ext_suite`, `mon_compress` and `mon_err_window` each
carry a `main()` AND get imported by other programs (`host_ext_char` imports
`bus_meters.read_meter`). They cannot sit in a build's `host/`: only entry
points live there, and only one build would have them.

So the module goes in `bin/` and the build gets a launcher:

```python
# build-perf/host/host_bus_meters.py -- the CLI half, nothing else
from bus_meters import main
if __name__ == "__main__":
    sys.exit(main())
```

The `read_` verb is dropped on the way into `bin/` (`read_bus_meters.py` ->
`bus_meters.py`): in `bin/` it is a noun, a thing you can measure; the verb
belongs to the command that runs it. See [[flow-layout]] for why a library must
not carry the `host_` prefix -- a runnable library named `run_*` was the
mistake that produced this rule.

Everything in `bin/` is shared by BOTH builds. Everything in `build-*/host/` is
that build's own -- and only that build's: `host_mon_*` (in-core monitors)
live in `build-mon/host/` alone, `host_obs_*` (observer taps) in
`build-obs/host/` alone, because each needs an instrument the other build
does not ship. Copies of the mon programs in build-obs (and of the obs
campaign in build-mon) drifted apart within days and were removed. The split is not cosmetic: `characterization.py` and the
`*_addrs` libraries are imported by monitor-side programs as well as perf-side
ones, which is why they are component-level.

## Devices: one object per register-mapped block

A `Device` is `(base address, regmap)`. That is the whole idea, and it is why
the same class serves sim and silicon -- only the injected bridge differs.

```python
dma = Stream(bridge, "ch0",                 # base + regmap IS the Device
             regs_base=0x0000_0000,
             desc_ram_base=0x0002_0000)
dma.enable_channel(0)                       # by name, never by offset
dma.kick(channel=0, desc_addr=0x0002_0000)
```

Two rules that keep devices thin:

- **Never hand-roll read-modify-write.** `UartRegisterMap` takes `rmw=True` and
  preserves the unnamed fields. A device that reads every field back and
  rewrites them is reimplementing the layer below it -- the retired
  slave-monitor device did exactly that before review, in three separate
  methods. (That device is gone: its window is the slave-role observer on
  `obs_regs` now, STREAM TASK-073.)
- **Never name an offset.** The address map is the generated regmap's job. A
  literal offset in a device class is the bug [[registers-by-name]] exists to
  prevent, and it survives every register-map move undetected.

## `stream_env`: the one place that knows where things are

Mirrors `pumice_env`. It locates the shared FPGA layer by searching upward for
a marker file, then puts three layers on `sys.path`: the shared layer, this
area's `bin/`, and the selected build's `host/` (`STREAM_BUILD` picks; default
`mon`).

Every host program starts with the same two lines and nothing else:

```python
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401  (import side effect: sys.path setup)
```

This replaced three different hand-counted walks -- one to a sibling flow
(`../../flows-stream-bridge/host`), one `[os.pardir] * 5` to the repo root, and
one to `projects/components/utility-ip/converters/bin` for the UART bridge. The last was
already wrong: that path now holds only a compatibility shim whose own
docstring says new code must not import through it. See [[flow-layout]]
"anchor paths, never count directory levels".

## Library or program? The prefix decides, and it is not a style choice

`host/host_*.py` becomes `make host-<name>`; `bin/run_*.py` becomes
`make run-<name>`; anything else is a library. Discovery is a glob, so the name
is the declaration.

The trap with teeth: **a library that happens to be runnable is still a
library.** `run_characterization.py` has a CLI and fourteen importers. Left
under that name in a component `bin/`, the flow would glob it as a *runner* and
`make run-characterization` would invoke it with `--board/--baud/--sequences`
it does not accept. It is `characterization.py` for that reason -- the same
"one name, one thing" collision `flow-layout` records for `run_smoke.py`.

## Adding a new object

Ask which layer it belongs to before writing it:

- Talks to a register-mapped block? -> a `Device` subclass in `bin/`, with a
  generated regmap. Not a pile of `bridge.write(0x…)` calls.
- Orchestrates a campaign over devices? -> a runner/library in `bin/`.
- Programs an instrument around a DMA run? -> a `CharacterizationRunner`
  hook (`mon_config`, `pre_kick`), never a hand-rolled reset/configure/kick.
  See [[uart-harness]] "Instrumentation goes INSIDE the board's program".
- Is one runnable investigation? -> `host_*.py` in the build that owns it.
- Wire-level orchestration of a monbus group? -> it already exists, and it is
  `MonbusGroupHarness`. Drain, trace, fifo counters and IRQ are done; decode is
  delegated to `TBClasses.monbus.parse`. Hand-rolling any of that is the
  mistake [[bfm-usage]] records.

## Related

- [[host-stack]] - the shared layers these compose
- [[flow-layout]] - directories and filename prefixes
- [[registers-by-name]] - why no object may name an offset
- [[monitor-board-coverage]] - what the monitor-side devices are for

## The two monbus windows share one memory (stream TASK-019, 2026-10-25)

STREAM's monitor egress is `monbus_axil4_group_1wr`: write-only, no slave
read port. Everything it keeps goes to memory over the bridge's `monbus_wr`
master, `ERR_SELECT`-routed packets into the ERROR window and the rest into the
TRACE window. On `bridge_stream_mon_axil` the only memory that master can reach
is `comp_sram` (64 KB), so the error window is its top 4 KB
(`bridge_windows.monbus_err_window()`, 170 records) and the trace window is the
rest (`monbus_capture_window()`). Three things follow:

- **Program both windows, every run, by name.** The RDL reset values are sim
  addresses that land on `dma_axil` here. `route_monbus()` and
  `StreamHarnessTB` write `MON_GROUP_ERR_*` alongside `MON_GROUP_*`, and
  `route_monbus("comp_sram")` shrinks the trace to exclude the error window;
  a caller that takes `W("comp_sram")` raw overlaps the two.
- **The `stream_err` bridge slot is RESERVED, not removed.** Dropping a slave
  respins the generated xbar, which is how the DE hang arrived last time
  (the stream bridge respin of 2026-10 that rewrote the xbar under a working
  design). The harness answers SLVERR on both
  channels so a stale drain tool fails loudly.
- **Reads come from memory.** `dump_monbus.py` reads the error window
  (`MON_ERR_REC_COUNT` says how many), `dump_monbus_sram.py` the trace window;
  `mon_err_window.probe_err_window` is the one program (cosim and board) that
  proves count, slots and record types agree.
