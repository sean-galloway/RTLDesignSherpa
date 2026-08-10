---
title: Migrating a flow into fpga-systems
summary: Copy never move, pin the roots with ':=', and check source PROVENANCE before believing a build - a relocated flow that quietly compiles the old sources looks identical until the board.
---

# Migrating a flow into fpga-systems

Moving a pre-migration flow (`projects/NexysA7/<something>_characterization/
flows-*/`) into the [[area-structure]] layout. Written from the stream monitor
build, which went through end to end.

## Copy, never move, until everything is green

Nothing in the old tree gets deleted until **every** flow is migrated and
passing. Two reasons, and the second is the one that matters:

1. Other flows still reference the shared framework you are relocating.
2. The old tree is the reference you compare against. Timing, sim runtime,
   board coverage -- all of it is only meaningful against a baseline, and an
   in-place move destroys the baseline at the moment you need it.

Capture the baseline explicitly before starting: WNS/TNS and utilization from
the existing reports, sim wall-clock, board coverage. The stream monitor build
came out at WNS +1.435 ns against a +1.426 ns baseline and a 704 s sim against
705 s -- numbers that mean "equivalent" only because the old numbers survived.

## Pin the roots with `:=`, not `?=`

`env_python` already exports the legacy roots pointing at the **pre-migration**
tree:

```sh
export STREAM_CHAR_ROOT=$REPO_ROOT/projects/NexysA7/stream_characterization/flows-stream-bridge
export STREAM_CHAR_FRAMEWORK_ROOT=$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework
```

So a relocated build Makefile that writes

```make
export STREAM_CHAR_ROOT ?= $(SELF_DIR)      # WRONG: env_python already set it
```

is silently ignored, and the new build resolves its filelists **backwards into
the old tree**. It looks fine -- `make targets` is right, the Makefile reads
right -- until lint names a source from a directory you thought you had left.
Use `:=` for every root the relocated build must own, and say why in a comment
so nobody "tidies" it back.

## Check provenance before believing a build

A relocated build that compiles the OLD sources produces a correct bitstream.
It will lint, simulate, place, route and program. There is no symptom until
someone edits the new tree and nothing changes.

So after `make project`, ask the project file where its sources actually came
from:

```sh
XPR=.../fpga/build/vivado_project/<flow>.xpr
grep -c 'projects/NexysA7/<old-tree>' $XPR     # must be 0
grep -oE '\$PPRDIR/[^"<]*\.(sv|v)' $XPR | sed 's|.*/\.\./||' | cut -d/ -f1-3 | sort | uniq -c
```

Every path should resolve into the new tree or to a repo-level library
(`rtl/amba`, `rtl/common`, `projects/components/...`). This is cheap and it is
the difference between "the new tree builds" and "the new tree builds itself".

**Check EVERY consumer, not just Vivado.** The `.xpr` is one place sources are
named; the sim filelists are another, and they are checked by a different
command. In the stream migration the `.xpr` came back clean at 0 old-tree
sources -- and `rtl/filelists/dma_slave_monitors.f` was meanwhile compiling

```
$REPO_ROOT/projects/NexysA7/stream_characterization/flows-stream-monitor/rtl/dma_slave_monitors.sv
```

because it named an ABSOLUTE path where its sibling used `$STREAM_CHAR_ROOT`.
Every cosim run reported that FUB test passing against the pre-migration
source, and it only surfaced when the module's ports changed and the test
elaborated the old one. Two generated bridge filelists had the same absolute
path. So:

```sh
# no filelist anywhere in the new tree may name the old one
grep -rn "<old-tree-path>" <new-tree>/**/filelists/*.f
```

A root-variable (`$STREAM_CHAR_ROOT`) survives relocation; an absolute path
does not, and fails silently because the file it names still exists.

### Filelists are not the only consumer either

Four classes of file name a source path, and each is checked by a different
command -- so a clean result from one says nothing about the others:

| consumer | names paths in | caught by |
|---|---|---|
| Vivado project | `.xpr` | `grep` after `make project` |
| sim filelists | `rtl/filelists/*.f` | `make lint` |
| **cocotb tests** | `filelist_path=` + `dut_name=` in `dv/tests/*.py` | `make sim` ONLY |
| **generators / regmap loaders** | anchor paths in `bin/*.py` | nothing -- silent |

The last two bit twice in one migration. `make lint` was green on both builds
while all three cosim tests still passed `build-mon/rtl/filelists/stream_mon_harness.f`
to `get_sources_from_filelist` -- lint reads the filelists directly and never
looks at the tests. And `gen_harness_regmap.py` kept WRITING into the old tree
while `harness_addrs._default_regmap()` kept READING from it, which no build
step touches at all.

A restructure that renames a top module (`stream_mon_harness` -> `stream_harness`)
breaks the tests in a second way, through `dut_name=`. Grep for the OLD MODULE
NAME as well as the old path:

```sh
grep -rn "<old-module>\|<old-tree-path>" <new-tree> --include=*.py --include=*.f
```

**Lint is not evidence that a relocation worked.** It proves the filelists
resolve. Only `make sim` exercises the test-side copy of those same paths, and
nothing but running the generator proves the generator writes where you think.

### Set EVERY root the closure uses, not the one you were thinking about

The nastiest variant: a filelist closure that spans TWO root variables, where a
consumer sets only one. The stream harness resolves against `$FRAMEWORK_ROOT`,
but the `instrumentation.f` it pulls in -- `harness_csr`, `axi_response_delay`,
and the GENERATED BRIDGES -- resolves against `$STREAM_CHAR_FRAMEWORK_ROOT`.
`env_python` exports the second one pointing at the pre-migration tree.

A test that sets only `FRAMEWORK_ROOT` therefore compiles the new harness
against the OLD tree's bridge. That is not a missing file and not an error --
it is a complete, successful build of a stale design. It surfaced only as

```
%Error-PINNOTFOUND: stream_harness.sv:620: Pin not found: 'obs_apb_PSEL'
```

because the new harness had gained an APB slave the old bridge did not have. Had
the relocation not also changed the design, it would have built silently and
been believed.

The rule: enumerate the roots the closure ACTUALLY uses, don't set the ones you
remember.

```sh
grep -ohE '\$[A-Z_]+' <new-tree>/rtl/filelists/*.f | sort -u   # every root, incl. nested -f
```

Then set all of them, in the Makefile AND in every test. `env_python`'s stale
export is what makes a missed one silent rather than fatal.

## Order of work

1. **Component layer first** -- `bin/`, `rtl/`, `dv/`. Both builds need it.
2. **Smallest build first.** It exercises every shared mechanism (Makefile
   contract, tcl env, filelist roots, board layer) at the lowest cost, and
   whatever breaks there would have broken in the big one too.
3. `make lint` -> `make sim` -> provenance -> `make bitstream` -> `make program`
   -> host programs. Each step is cheap relative to the next; `make project`
   before `bitstream` catches path errors in two minutes instead of thirty.

## What the relocated build declares

Variables only ([[build-flows]]). The stream monitor build's Makefile has zero
recipe lines. Things that felt like they needed a local recipe turned out to
belong in `make/fpga_flow.mk`, where every flow gets them:

- `PREBUILD` -- a pre-synthesis regeneration step (a bridge from its `.toml`, a
  regblock from its `.rdl`). Empty by default.
- `FPGA_BITSTREAM` -- exported so a tcl never re-derives the artifact name.
  This is what lets a build encode a flavor in the filename instead of two
  flavors overwriting one file.
- `LINT_WAIVERS` -- board-integration noise, not per-flow.

If a migration wants a recipe in a build Makefile, that is a signal the shared
flow is missing a hook, not that this build is special.

## Things that do not come across

- **Per-flow `program_fpga.tcl`** -- `make/fpga_board.mk` provides `program`.
  Check the old one for logic worth keeping first; in the stream case it was a
  byte-for-byte copy of the shared one, bug included ([[boards]]).
- **Duplicate constraints.** The stream monitor flow carried the same xdc in
  both `rtl/` and `constraints/`; only `constraints/` was ever read.
- **Dead scripts.** Host tools written against a retired register interface
  should not be carried forward into a tree being made clean. They stay in the
  old tree until it is retired.

## Python paths

Anchor, never count -- see [[flow-layout]]. A relocation is exactly when
`[os.pardir] * 5` breaks, and it breaks silently if the new depth happens to
match. Give the component a `<name>_env.py` that finds the shared layer by
marker file, and let every host program bootstrap through it.

Watch for a library named `run_*.py` landing in a component `bin/`: the flow
globs `run_*.py` there as *runners*, so an imported library with that name
becomes a bogus `make run-<x>` target. If a file is imported by anything it is
a library, whatever else it does -- rename it.

## Related

- [[area-structure]] - the tree being migrated into
- [[flow-layout]] - the build skeleton and filename prefixes
- [[build-flows]] - the shared flow Makefile
- [[boards]] - programming, and the JTAG target trap
