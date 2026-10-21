---
title: Build flows
summary: Vivado non-project batch flow, board switches, bitstream naming.
---

# Build flows

## The global make infra

Flow logic lives in ONE place and every FPGA project reuses it -- the
`make/tests.mk` pattern (see [[test-runner]]) applied to board builds. Three files:

| File | Include when | Gives you |
|---|---|---|
| `make/fpga_flow.mk` | a build wants the whole flow | `project synth bitstream bitstream-ila lint program ports board-info boards sim run seq-list utilization timing clean clean-all help` (it includes the other two) |
| `make/fpga_board.mk` | a flow already owns its build recipes | the board half only: `program ports board-info boards` |
| `make/fpga_lint.mk` | a flow on `fpga_board.mk` -- always | the lint gate: `lint flat-filelist lint-decl-order`, with `TOP` and `FILELIST` set |

**Every flow has `make lint`, including one that owns its build half** (owner,
2026-10-19). The lint gate used to live inside `fpga_flow.mk`, so the two RAPIDS
flows, which include `fpga_board.mk` to keep their `verify-sim`-gated build
recipes, had no lint target at all, and a hand-rolled substitute ran softer
(`-Wno-fatal`, its own stubs) than the real gate. The gate is now its own file:
`fpga_flow.mk` includes it unchanged (`make -n lint` identical on all 20 of its
flows), and a `fpga_board.mk` flow includes it directly and sets
`LINT_GENERICS` to the generics its `create_project.tcl` applies (RAPIDS:
`flows-rapids/Makefile`, `flows-rapids-beats/Makefile`). Never write a second
lint recipe.

A build's Makefile is variables, not recipes:

```make
FLOW      := ddr2_char
TOP       := ddr2_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/ddr2_char_harness.f
SIM_TESTS := $(SELF_DIR)/dv/tests
SEQ_DIR   := $(SELF_DIR)/../bin
include $(RDS_ROOT)/make/fpga_flow.mk
```

Paths are derived (`fpga/tcl`, `fpga/bitstream`, `fpga/reports`, falling back to
the older flat layout so existing flows can adopt it without moving anything).
A build needing a different recipe overrides the VARIABLE (`BUILD_TCL := ...`),
not the rule. `make help` is generated from the `##` comments, so it cannot
drift from the real target set.

Reference: `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/` -- a per-build Makefile of
five variables, plus an area dispatcher (`make bitstream BUILD=litedram`,
`make ab` to run both builds back to back).

### The escape hatches, so a build never needs a recipe

Every time a build "obviously needs" its own rule, the answer has been a
variable in the shared file instead. The three that exist:

| Variable | For | Default |
|---|---|---|
| `PREBUILD` | a command that must run before `project`/`synth`/`bitstream` -- regenerating a bridge from its `.toml`, a regblock from its `.rdl` | empty (a clean no-op) |
| `FPGA_BITSTREAM` | exported to the tcl so the artifact name has ONE authority | `$(FPGA_DIR)/bitstream/$(FLOW).bit` |
| `LINT_WAIVERS` | board-integration warning noise | includes `-Wno-PINMISSING`: a board top routinely leaves a submodule's optional status outputs open, and that is an integration choice, not a defect. **Never WIDTH** (below) |
| `LINT_VENDOR_VLT` | rules switched off for third-party source only, by file path | `make/verilator_vendor.vlt`: WIDTH off under AMD's IP library, nothing else |
| `LINT_UNROLL` | Verilator's loop-unroll budget, when the design's deepest loop exceeds the stock one | empty -- a flow that does not need it must not pay for it |

`FPGA_BITSTREAM` earns its keep when a build has more than one flavor. The
stream monitor build compiles either the error cone or all the others, and with
a fixed filename the second `make bitstream` silently overwrote the first --
after which nothing on disk said which was on the board. The Makefile encodes
the flavor in the name and the tcl reads `FPGA_BITSTREAM` rather than
re-deriving it. A tcl that builds its own output path is a second authority
waiting to disagree.

**A recipe appearing in a build Makefile is a signal the shared flow is missing
a hook, not that this build is special.**

### PREBUILD may only write files nobody edits

`PREBUILD` runs on every `project`/`synth`/`bitstream`, so whatever it writes is
rewritten every time anyone builds. Point it at generated RTL and filelists and
nothing else. The moment it also writes test collateral, building a bitstream
becomes a way to silently revert work.

Genesys 2 stream did exactly that: `regen_bridges.sh` passed `--generate-tests`,
so `make bitstream` regenerated `rtl/bridges/dv/`. Three separate rounds of
committed fixes were undone that way (33ac787e, 90bca4c1, bd79af49). The
regeneration was worse than stale, too -- the generator derived a dotted import
from the output directory, and `projects/fpga-systems/` contains a hyphen, so
`from projects.fpga-systems.Genesys2... import X` is a SyntaxError. The five
bridge tests were therefore not failing; they could not be COLLECTED, which in a
report is indistinguishable from a suite that passed.

Two rules fall out of it:

- **A generated file that keeps getting hand-fixed is telling you the fix
  belongs in the generator, or that the file is not generated any more.** Decide
  which; leaving it as "generated, but we patch it" guarantees the patch is lost.
  Area-specific content -- a TEST_LEVEL budget, a waiver the local CSR needs --
  a shared generator cannot know, and is the honest signal for the second answer.
- **Check idempotence, not output.** Run the PREBUILD on a clean tree and look at
  `git status`. If it dirties anything, that is the blast radius of every future
  `make bitstream`. `Genesys2/stream/bin/tests/test_bridge_dv_not_generated.py`
  makes that check mechanical for this flow.

## Defines: lint and the build used to see different RTL (RESOLVED 2026-09-07)

`ALWAYS_FF_RST` is now **unconditionally asynchronous on assertion**. There is
no switch. `USE_ASYNC_RESET` still parses and still does nothing; builds that
pass it are harmless.

Keep the history, because it is the reason the rule is now unconditional and
not merely "set the define everywhere". `make/fpga_flow.mk` set exactly one
define, and only for lint:

```make
LINT_DEFINES ?= +define+USE_ASYNC_RESET
```

Synthesis and simulation got no defines at all, so they took the header's
default, which was SYNCHRONOUS. Lint elaborated every `ALWAYS_FF_RST` block
with reset in the sensitivity list and the bitstream you actually built did
not. `BODY` was identical in both branches -- same flops, same reset values,
same logic -- so the exposure was narrow but exact: any finding that depended
on reset TIMING was being made against a configuration nobody built, in either
direction. Nothing documented why the define was there; it arrived unexplained
in d2d387e5 and read as intentional when it may simply have been misplaced.

The failure was not the default value. It was that the value was a KNOB, so
two tools could hold different answers and both report success. A knob nobody
sets deliberately is not configurability, it is a place for the tools to
disagree. Removing it removed the disagreement; picking the other default
would only have moved it.

There is still no `SYNTH_DEFINES` hook in `fpga_flow.mk`, and it is no longer
needed for resets. If a future knob genuinely has to reach synthesis, add the
hook rather than relying on a header default, and give lint and synth the same
value from ONE source -- see [[silent-fallbacks]].

Copies of the header are the remaining hazard: eight tracked copies of
`reset_defs.svh` kept the old conditional after the canonical file changed, one
of them live in `timing_characterization`, whose flops would have elaborated
synchronous while the rest of the tree was async. `bin/check_shared_include_copies.py`
(wired into the pre-commit hook) now fails on any tracked copy that has drifted.

## Flow notes

- Non-project batch Tcl driven by the Makefiles above
  (`fpga/tcl/{create_project,build_all,synth_only,build_ila}.tcl`). There is no
  per-flow `program_fpga.tcl` any more -- programming is the board registry, see
  [[boards]].
- A cocotb sim gate runs BEFORE Vivado (verify-sim): UART ping -> CSR
  round-trip. A build that skips it wastes hours on dead-on-arrival RTL.
- Long runs: background + log polling; place/route on a K325T takes tens
  of minutes - do not kill on a hunch. Monitor the log for the phase
  markers and Post Placement/Routing Timing Summary lines.
- Filelists resolve standalone (source env_python first); flow Makefiles
  may add flow-scoped vars but the .f files must not require them.
- Verilator sim of board tops: deep monitor tables need --unroll-count
  (default 64) - see [[timing-closure]] sibling gotchas. **The lint gate needs
  the same budget, from the same source.** It did not have it, and the result
  was not a noisy gate but a blind one: `make lint` on stream build-mon exited
  22 BLKLOOPINIT errors -- Verilator refusing to elaborate the monitor's
  per-slot delayed array assignments -- over RTL that every cocotb `run()`
  compiled clean, because those seven call sites passed the budget and the gate
  did not. BLKLOOPINIT is not a style warning to waive; it means the tool never
  looked at the design. Set `LINT_UNROLL` by DERIVING it from whatever the
  area's tests read (Genesys 2 stream: `dv/stream_cfg.py::verilator_unroll_args`,
  wired through `stream.mk`), never by retyping the number - that number has
  already been copy-pasted into seven places once and raised in only some.

## Bring-up order: registers before anything else

The moment a bitstream is on the board, the FIRST thing to run is the register
walk -- every endpoint, every register. Not the coverage run, not the DMA, not
the thing you built the bitstream to measure.

```sh
make program
make host-reg_walk        # every endpoint, every register -- MUST pass
make host-<the-real-thing>
```

Because a broken register path is silent. It accepts writes and returns values;
it just does not reach the hardware. On this repo that has already meant a
32-bit APB bus reaching silicon ONE BIT WIDE (implicit nets from a
declaration-order bug), and a 12-bit address window aliasing monitor registers
onto `GLOBAL_CTRL`. Both invalidated weeks of board results, and neither was
visible in sim -- Verilator and Vivado disagree on the first, and the second is
a host-side width.

Two consequences for the order:

- **The walk is DESTRUCTIVE.** It restores RDL defaults, and defaults are the
  safe-but-silent state (`PKT_MASK=0xFFFF` drops every packet). A coverage run
  straight after it reads zero and looks like dead silicon. Run the walk first,
  then configure, then measure -- or reprogram between.
- **It is also the fastest possible smoke test.** 258 registers over UART takes
  well under a minute and converts "the bitstream probably works" into a number.

Method and rationale: [[register-testing]].

## WIDTH is not waived (owner, 2026-10-20)

`LINT_WAIVERS` carried `-Wno-WIDTH` for every flow. Taking it out turned 23 of
39 builds red on 234 width sites, and among the noise were real defects that
had passed every simulation:

- a board top's 6-bit ID nets on a 7-bit bridge port (bridge-stress build-xil);
- a monitor group's 64-bit error drain wired into a 32-bit AXI-Lite window
  (STREAM's slave observer: the upper half of every record lost -- the class
  f08ccce4 fixed for stream_top_ch8, still alive in a second instance);
- STREAM's 16-bit monitor masks passed through 8-bit nets, so the monitor saw
  `0x00FF` where the RDL resets `0xFFFF`;
- an 8-bit copy of a 16-bit FIFO count that read "empty" at 256 records;
- a core instantiated without its user-width parameter (granite: user bits
  cut to 1, the upper B / R user bits undriven).

Fix a width by sizing the operand or the connection where the intent is
(`16'(x)`, `x[5:0]` with the dropped bits driven or marked unused, the net at
the port's width) -- never by a waiver. The only exemption is third-party
source this repo cannot edit, listed by path in `make/verilator_vendor.vlt`.
A comment in a `.vlt` must not begin with the tool's name: it is read as a
pragma and fails every build.
