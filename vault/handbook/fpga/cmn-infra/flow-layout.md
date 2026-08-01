---
title: FPGA flow layout
summary: The directory skeleton and filename conventions every FPGA build shares. Prefixes declare what a file is, so make discovers targets by glob and nothing has to be enumerated.
---

# FPGA flow layout

One skeleton for every build, so a person who knows one flow knows all of them
and `make/fpga_flow.mk` can find everything without being told. The rule that
makes it work: **a filename prefix declares what the file is**, and discovery is
a plain glob over those prefixes.

## Skeleton

```
<area>/                     e.g. projects/fpga-systems/NexysA7/pumice
  bin/                      sequences + runners, SHARED by every build here
    run_*.py                a runner: picks board, resolves port, opens transport
    seq_*.py                one sequence; declares `requires`, uses ctx.bus only
    <area>_env.py           the one place that knows where the shared layer is
  build-<name>/             one per bitstream; skeletons are IDENTICAL
    Makefile                variables only, then include make/fpga_flow.mk
    bin/                    generators specific to THIS build (optional)
    dv/tb  dv/tests         cocotb harness sim; `make sim` runs dv/tests
    fpga/tcl                *.tcl -> discovered as `make tcl-<name>`
    fpga/constraints        xdc
    fpga/bitstream          build output
    fpga/reports            utilization / timing
    host/                   this build's host layer (see below)
    results/                measured data, committed when it is evidence
    rtl/  rtl/filelists     harness RTL and its .f
```

Generated vendor RTL is the one legitimate per-build difference:
`build-perf/rtl-vivado/` (Vivado/migen output) versus `build-litedram/gen/`
(LiteDRAM core output). Both are GENERATED -- never hand-edited, wiped and
rebuilt by their regeneration target.

## Filename conventions

| Pattern | Role | Discovered as |
|---|---|---|
| `bin/run_*.py` | runner, drives a whole plan | `make run-<name>` |
| `bin/seq_*.py` | one sequence | `make seq-<name>` |
| `host/host_*.py` | standalone host program | `make host-<name>` |
| `host/test_*.py` | pytest | via `SIM_TESTS`, never a make target |
| `host/<other>.py` | library: imported, never run | nothing |
| `fpga/tcl/*.tcl` | Vivado script | `make tcl-<name>` |

`make targets` prints exactly what was found on disk, so the answer to "what can
I run here" is never a guess.

### Why the host_ prefix and not a __main__ scan

Discovery first identified host programs by scanning for a `__main__` guard.
That worked, but it made role invisible in `ls` and it swept up library modules
that merely carry a debug CLI -- `ddr2_char.py` has fourteen importers and a CLI
both. The prefix states the intent instead of inferring it, and the split falls
out cleanly: nine `host_*` programs, four libraries, three test modules.

Renaming a library to `host_*` is therefore wrong. If a file is imported by
anything, it is a library that happens to be runnable, not a program.

## Anchor paths, never count directory levels

Every path derivation resolves by **searching upward for a marker**, not by
counting `..` segments.

This is a lesson with a date on it. The shared board/UART layer moved from
`fpga/bin` to `projects/fpga-systems/bin`, and every hand-counted path broke at
once: `pumice_env.py` counted five levels to the repo root, `ddr2_char.py`
carried its own copy of the same walk, `uart_link.py` counted three and silently
resolved to `<root>/projects/projects/...`, and a test asserted the literal
string `fpga/bin/program_fpga.tcl`. Four independent copies of one fact, each
broken separately.

The replacements search for `projects/fpga-systems/bin/uart_link.py` and stop
when they find it, honouring `REPO_ROOT` first. Cost is one `os.path.isfile`
per level; benefit is that the next move breaks nothing.

Corollary for generators: a tool that writes output must anchor its default
output path to its own location, not the cwd. `elaborate_a7ddrphy.py` defaulted
to a bare relative path and, run from the wrong directory, produced
`rtl-vivado/rtl-vivado/a7ddrphy/`.

## One name, one thing

Two files called `run_smoke.py` lived in one flow -- the sequence runner in
`bin/` and an older end-to-end DDR2 program in `host/`. Different code, same
name, and `make run-smoke` could only ever mean one of them. The host one is now
`host_ddr2_smoke.py`.

Related: [[build-flows]] (the Vivado batch flow), [[boards]] (the registry),
[[sequences]] (what a runner runs), [[host-stack]] (the transport layers).
