---
title: Build flows
summary: Vivado non-project batch flow, board switches, bitstream naming.
---

# Build flows

## The global make infra

Flow logic lives in ONE place and every FPGA project reuses it -- the
`make/tests.mk` pattern (see [[test-runner]]) applied to board builds. Two files:

| File | Include when | Gives you |
|---|---|---|
| `make/fpga_flow.mk` | a build wants the whole flow | `project synth bitstream bitstream-ila lint program ports board-info boards sim run seq-list utilization timing clean clean-all help` |
| `make/fpga_board.mk` | a flow already owns its build recipes | the board half only: `program ports board-info boards` |

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

Reference: `projects/fpga-systems/NexysA7/pumice/` -- a per-build Makefile of
five variables, plus an area dispatcher (`make bitstream BUILD=litedram`,
`make ab` to run both builds back to back).

### The escape hatches, so a build never needs a recipe

Every time a build "obviously needs" its own rule, the answer has been a
variable in the shared file instead. The three that exist:

| Variable | For | Default |
|---|---|---|
| `PREBUILD` | a command that must run before `project`/`synth`/`bitstream` -- regenerating a bridge from its `.toml`, a regblock from its `.rdl` | empty (a clean no-op) |
| `FPGA_BITSTREAM` | exported to the tcl so the artifact name has ONE authority | `$(FPGA_DIR)/bitstream/$(FLOW).bit` |
| `LINT_WAIVERS` | board-integration warning noise | includes `-Wno-PINMISSING`: a board top routinely leaves a submodule's optional status outputs open, and that is an integration choice, not a defect |

`FPGA_BITSTREAM` earns its keep when a build has more than one flavor. The
stream monitor build compiles either the error cone or all the others, and with
a fixed filename the second `make bitstream` silently overwrote the first --
after which nothing on disk said which was on the board. The Makefile encodes
the flavor in the name and the tcl reads `FPGA_BITSTREAM` rather than
re-deriving it. A tcl that builds its own output path is a second authority
waiting to disagree.

**A recipe appearing in a build Makefile is a signal the shared flow is missing
a hook, not that this build is special.**

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
  (default 64) - see [[timing-closure]] sibling gotchas.

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
