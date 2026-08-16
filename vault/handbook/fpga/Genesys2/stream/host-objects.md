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
| `SlaveMon(Device)` | `bin/slvmon_device.py` | `dma_slave_monitors` via `slvmon_regs` | device |
| `CharacterizationRunner` | `bin/characterization.py` | the harness CSRs + a DMA campaign | runner/library |
| `DescriptorBuilder` | `bin/descriptor_builder.py` | descriptor RAM contents | pure builder |
| `harness_addrs` / `stream_addrs` | `bin/` | by-name addresses + `compose()` | library |
| `bus_meters` | `bin/bus_meters.py` | `axi4_intf_master_observer` bucket CSRs | library + `main()` |
| `rw_perf` / `desc_perf` | `bin/` | in-core RDMON/WRMON/DAXMON windows | library + `main()` |
| `stream_ext_suite` | `bin/stream_ext_suite.py` | row/col traversal cases over `Stream` | library + `main()` |
| `stream_ext_report` | `bin/stream_ext_report.py` | nothing -- formats results | pure formatter |
| `StreamHarnessTB` | `dv/tbclasses/stream_harness_tb.py` | `stream_harness` over UART | testbench (both builds) |
| `MonbusGroupHarness` | `bin/TBClasses/scoreboards/monbus_group/` | a monbus group's drain/trace/irq | shared TB collateral |
| `host_*.py` | `build-<n>/host/` | one campaign each | program |

### When a module is BOTH a library and a program

`bus_meters`, `rw_perf`, `desc_perf` and `stream_ext_suite` each carry a
`main()` AND get imported by other programs (`host_ext_char` imports
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
that build's own. The split is not cosmetic: `characterization.py` and the
`*_addrs` libraries are imported by monitor-side programs as well as perf-side
ones, which is why they are component-level.

## Devices: one object per register-mapped block

A `Device` is `(base address, regmap)`. That is the whole idea, and it is why
the same class serves sim and silicon -- only the injected bridge differs.

```python
slv = SlaveMon(bridge)                      # base 0x0018_0000, slvmon regmap
slv.arm_threshold("rd", cycles=20)          # by name, never by offset
slv.classes("rd", compl=False)              # rmw=True underneath
```

Two rules that keep devices thin:

- **Never hand-roll read-modify-write.** `UartRegisterMap` takes `rmw=True` and
  preserves the unnamed fields. A device that reads every field back and
  rewrites them is reimplementing the layer below it -- `SlaveMon` did exactly
  that before review, in three separate methods.
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
one to `projects/components/converters/bin` for the UART bridge. The last was
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
- Is one runnable investigation? -> `host_*.py` in the build that owns it.
- Wire-level orchestration of a monbus group? -> it already exists, and it is
  `MonbusGroupHarness`. Drain, trace, fifo counters and IRQ are done; decode is
  delegated to `TBClasses.monbus.parse`. Hand-rolling any of that is the
  mistake [[feedback_monbus_group_harness]] records.

## Related

- [[host-stack]] - the shared layers these compose
- [[flow-layout]] - directories and filename prefixes
- [[registers-by-name]] - why no object may name an offset
- [[monitor-board-coverage]] - what the monitor-side devices are for
