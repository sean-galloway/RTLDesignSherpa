---
title: FPGA area structure
summary: Where an FPGA project lives - board / component / build, and the four places something shared can go. [[flow-layout]] starts one level below this.
---

# Where an FPGA project lives

`projects/fpga-systems/` holds everything that targets a real board. Three
levels, each answering a different question:

```
projects/fpga-systems/
  bin/                        SHARED host layer, every board and component
    uart_link.py board.py boards/ uart_axi_bridge.py sequence.py
    program_fpga.tcl
  <Board>/                    a physical board: NexysA7, Genesys2
    <component>/              a design on that board: pumice, stream
      Makefile                area dispatcher (BUILD=..., forwards the rest)
      bin/                    sequences + libraries shared by THIS component's builds
      rtl/  rtl/filelists     RTL shared by this component's builds
      dv/                     sim for the shared blocks
      build-<name>/           one per bitstream -- see [[flow-layout]]
```

The board level is not decoration: a component's constraints, clocking and
timing headroom are board facts, and two boards running "the same" design are
two builds with two xdc files and two sets of reports.

## The four homes for shared things

Most structural mistakes are putting a shared thing at the wrong level. In
increasing scope:

| Scope | Home | Example |
|---|---|---|
| One build | `build-<name>/rtl`, `/host`, `/dv` | that build's harness + top |
| One component, all its builds | `<component>/rtl`, `/bin`, `/dv` | stream's `harness_csr.sv`, the generated bridges, `stream_env.py` |
| Every board flow | `projects/fpga-systems/bin/` (host) | `uart_link`, the board registry, `program_fpga.tcl` |
| Every board flow, but RTL | `projects/components/misc/rtl/` | `verilator_xilinx_stubs.sv` |

That last row is the one with a date on it. Verilator stubs for Xilinx
primitives (`BUFG`, `IBUFDS`, `MMCME2_BASE`) are needed by every board top, and
a `projects/fpga-systems/rtl/` was invented for them -- a directory that is in
no skeleton and no note, which is precisely how the divergence being cleaned up
started. There was already a home: `misc/` is a registered component area that
board flows consume via `MISC_ROOT`. **A new top-level directory is a
convention change; make it deliberately or not at all.**

Corollary: the consumer `-f` includes the owner's filelist, never the `.sv`.
`misc/` owns its compile closure (see [[filelists]] and
`bin/filelists.toml`), so a board flow writes

```
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
```

## Component with two builds

Two builds under one component is the normal shape, and it means two different
things depending on the pair:

- **pumice**: `build-perf` (pumice on real DDR2) and `build-litedram` (LiteDRAM
  in its place) -- two controllers, one board, so `make ab` runs both back to
  back and the comparison is meaningful.
- **stream**: `build-mon` (monitor-validation harness) and `build-perf`
  (characterization harness) -- two harnesses over one design.

Either way the component's `bin/` and `rtl/` are what the builds share, and the
build Makefiles stay variables-only ([[build-flows]]).

## A design on two boards

A design that runs on two boards is NOT a third build under one board. It is
the same component appearing under each `<Board>/`, sharing what it can. The
stream characterization harness has both a Nexys A7 top and a Genesys 2 top;
under this layout those are `NexysA7/stream/` and `Genesys2/stream/`, not two
tops in one directory selected by a `BOARD` variable -- which is what the
pre-migration flow did and why its Makefile grew an `ifeq` around the bitstream
name.

## Migrating a flow into this layout

The mechanics and the traps are [[flow-migration]]. The short version: copy,
never move, until every flow is green -- an in-place move deletes the working
reference at exactly the moment you need it to compare against.

## Related

- [[flow-layout]] - the build skeleton and the filename prefixes
- [[build-flows]] - `make/fpga_flow.mk`, the flow every build includes
- [[boards]] - the registry, and picking a JTAG target
- [[host-stack]] - the python transport layers
