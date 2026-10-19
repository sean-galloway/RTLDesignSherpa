# TASK-024: fpga-systems has no specification -- document the UART flow and the host/seq naming conventions as a chapter book with a PDF

**Priority:** P2
**Status:** CLOSED 2026-09-30 -- the book is written and the PDF builds (48 pages, 5 diagrams)
**Owner:** TBD
**Filed:** 2026-09-30 (Sean's request)

`projects/fpga-systems/bin/` is the shared board and UART layer every board flow
imports by bare module name, and it is the **only** major area in this repo with
no book. There are 27 `docs/<name>_(mas|has)/` books across components and
asic-trials; `projects/fpga-systems/` has no `docs/` directory at all. The layer
with the most consumers is the one with no specification.

Two things to document, per Sean: **the UART flow end to end**, and **the naming
conventions** for the host-side files -- `seq_*`, `host_*`, `run_*` and the
directories they live in.

## What exists to document (measured, not guessed)

`projects/fpga-systems/bin/`:

| File | What it is |
| --- | --- |
| `uart_link.py` | `UartLink`, `UartPort`, `list_uart_ports`, `find_port`, `register_probe`/`scratch_probe`, `open_bridge`. Port DISCOVERY by USB serial, not a hardcoded `/dev/ttyUSB*`. |
| `uart_axi_bridge.py` | register access over the link |
| `sequence.py` | the generic sequence container every `seq_*.py` builds on |
| `board.py`, `boards/` | the board registry: part, JTAG serial, UART serial |
| `fpga_board.py` | CLI over the registry (`list`/`info`/`ports`/`serial`/`readback`/`program`) |
| `board_lock.sh` | the board-keyed lock ([[TASK-022]]) |
| `program_fpga.tcl`, `jtag_readback.tcl` | the two Vivado entry points |

## The naming problem is real, and the doc has to settle it

There are **three** coexisting directory conventions for host programs, and
nothing says which to use for new work:

| Layout | Files | Used by |
| --- | --- | --- |
| `<Board>/<unit>/bin/` | `seq_*.py` (15), `run_*.py` (2) | pumice, reed-solomon |
| `<Board>/<unit>/build-<variant>/host/` | `host_*.py` (30) | stream (mon/obs/perf), pumice build-perf, cdc_counter_display, rs loop |
| `<Board>/<unit>/flows-<name>/host/` | `run_*.py` (4) | rapids, rapids_beats |

And the `host_*` prefix has grown informal sub-families that mean something to
their authors and nothing to a reader: `host_mon_*`, `host_obs_*`, `host_reg_*`,
`host_ext_*`, `host_bringup_*`, `run_sink_*`. Whether these are a convention or
an accident is exactly what is undocumented.

**This is the substance of the task, not a side note.** A naming chapter that
only describes `seq_*.py` would be describing the tidiest third of the tree.
State the rule, say which layout new work uses, and record why the others exist.

## A proposed rule, from the Reed-Solomon session (2026-09-30)

Offered with their own caveat that they are arguing for the layout they wrote, so
it is recorded as a proposal rather than a decision. It is the sharpest framing
available and the doc should start here.

**The split is not between three layouts but between two KINDS of thing**, which
is why three layouts grew:

- **A sequence** is a reusable, declaratively-ordered unit with dependencies.
  `bin/seq_*.py` earns its own file because the runner discovers it, resolves
  `requires`, and runs it **identically on the board and in the sim harness** --
  Reed-Solomon's sim tests run the same `seq_init`/`seq_smoke`/`seq_sweep`/
  `seq_random` files the board runs, with `board=None` and no parameter
  deviations, so a sequence-layer bug cannot hide in simulation.
- **A host program** is a CLI entry point: argument parsing, port discovery,
  printing. It should be thin -- construct a context and call the runner.

**The discriminating test:** can the file run unchanged against a cocotb UART
channel? If yes it is a sequence and belongs in `bin/`. If it parses `argv` it is
a program and belongs in `host/`. Their proposal is then
`bin/seq_*.py` + `host/host_*.py`, and **retire `flows-<name>/host/run_*.py` as a
third spelling of the second thing**.

### Measured against the tree: the rule has NO exceptions

The test holds in one direction outright: **all 15 `seq_*.py` contain zero
`ArgumentParser`**.

I first reported **six** files as exceptions, on the proxy "does it parse `argv`".
**That proxy was wrong and it manufactured all six.** The Reed-Solomon session
measured each one; none is a sequence, and none has the sequence SHAPE either --
`def run(self, ctx)` and `ctx.bus` both appear **zero** times in all six
(confirmed independently here). They are two legitimate categories:

- **Four thin CLI shims** (21-33 lines): `host_mon_compress`, `host_bus_meters`,
  `host_desc_perf`, `host_rw_perf`. Each bootstraps `sys.path` then does
  `from <name> import main; sys.exit(main())`, and the `ArgumentParser` lives in
  the same-named library in the area's `bin/` -- `bin/bus_meters.py`,
  `bin/mon_compress.py`, `bin/desc_perf.py`, `bin/rw_perf.py`, exactly one each
  (verified). The proxy looked in the shim instead of the library the shim calls.
  Correctly filed programs.
- **Two hardware debug scripts**: both `run_sink_once.py` (rapids and
  rapids_beats -- **not** Reed-Solomon's; that area has nothing in this list).
  They read `sys.argv[1]`/`[2]` positionally with a `/dev/ttyUSB1` default,
  construct a real serial `RapidsByteIO`, take a hardware lock through
  `board_guard.HardwareRun`, loop hunting an intermittent scheduler wedge, and
  deliberately leave the board frozen for an ILA snapshot. They cannot run under
  a cocotb channel, and `argv` has nothing to do with why.

**Do not add a second clause to the rule; replace the proxy.** The proposed
mechanical check is **"does the file construct its own transport?"** -- grep for
`UARTAxiBridge`, a `port=` argument, `find_port`, or a `/dev/tty` literal. A
sequence RECEIVES `ctx.bus` and never constructs one, which is exactly the
property that decides whether it runs unchanged in sim. Argparse presence is
downstream of that and, as the four shims show, easy to delegate out of view.

### The convention is already written down -- quote it

`host_bus_meters.py:14` states it, and it predates the proposal above:

> The implementation is `bin/bus_meters.py`, at COMPONENT level because it is a
> LIBRARY as well as a program -- host_ext_char and the cosim tests import its
> readers. **Entry points are `host_*` and live in a build; anything imported by
> more than one of them lives in bin/.** This file is the CLI half of that split.

The chapter should quote that line rather than paraphrase it.

**And note what it does NOT say.** The rule is about the `host_*` PREFIX, not the
directory. `build-loop/host/` holds `host_rs_loop.py` (the entry point, with the
`ArgumentParser`) plus `rs_loop.py` and `rs_loop_programs.py` -- neither parses
`argv`, both are correctly libraries sitting beside the entry point that uses them
(verified). A rule phrased "files in `host/` parse argv" wrongly flags those two;
"files named `host_*` are entry points" does not. Same distinction that makes
stream's `bin/` libraries legitimate.

A third category to NAME rather than relocate: hardware debug scripts. A script
whose purpose is to freeze real silicon for a logic analyser is honest about what
it is, and moving it buys nothing.

### Three things to put in the chapters, from the same session

1. **The `sys.path` trap, with the skeleton.** `rs_env.py` lives in the area's
   `bin/` **alongside** the sequences (confirmed:
   `projects/fpga-systems/NexysA7/reed-solomon/bin/rs_env.py`), so a host program
   under `build-*/host/` must put that directory on `sys.path` before importing
   `sequence`. They hit that exact `ImportError` running a board campaign for the
   first time. If the chapter shows the host-program skeleton, show the path
   setup -- it saves the next person the same trip.
2. **The 100 ms sim cap, and which lever to pull.** No sim-harness test may exceed
   100 ms of sim time, and when UART is the bottleneck the lever is **raising the
   sim baud, never shrinking the campaign**: 4 clocks per bit in sim against 868
   on the board, with the byte stream under test identical. (Consistent with the
   handbook; the UART chapter is where a reader will look for it.)
3. **Read the build's topology from a register, never assume it.** A
   single-decoder build failed every run because the host was faithfully scoring a
   checker that was tied off; a `TOPOLOGY` register fixed it. Belongs in the UART
   flow chapter as a rule about what the host may assume.

They offered to review a draft and are explicitly not taking the task.

## Scope

A chapter book following the house pattern, and the PDF:

- `projects/fpga-systems/docs/fpga_systems_mas/` with
  `fpga_systems_mas_index.md`, `fpga_systems_mas_styles.yaml`,
  `assets/images/logo.png`, and `ch0N_*/NN_*.md` pages.
- `projects/fpga-systems/docs/generate_mas_pdf.sh`, copied from
  `projects/components/retro_legacy_blocks/docs/generate_mas_pdf.sh` (DOCX+PDF
  via `md_to_docx.py`).
- Chapters, roughly: overview and layering; the UART flow (discovery -> probe ->
  link -> bridge -> registers); sequences and the `seq_*` contract; the board
  registry, locking and identity readback; **naming conventions and directory
  layout**; how a new board flow is stood up.

## Constraints that apply

- **No emojis** -- they break the LaTeX/PDF path.
- **One source per fact.** Do not restate `uart_link`'s API in prose that will
  rot; the per-family API docs ship in RDS-DV and the handbook holds method.
  This book is the fpga-systems AREA specification.
- Methodology belongs in `vault/handbook/fpga/`, which already has
  `uart-harness.md` and `boards.md`. This book documents the LAYER; where the
  two touch, link rather than copy.
- Chapters sit one level deeper than the index, so relative links from a
  `ch0N_*/` page need `../../` to leave the book.

## Acceptance

- The book builds to a PDF through `generate_mas_pdf.sh` with no LaTeX errors.
- `check_broken_links.py --ratchet` clean, and the book is linked from its index
  (an unlinked page never reaches the PDF).
- The naming chapter states a rule for new work and accounts for all three
  existing layouts, rather than documenting only `seq_*`.
- Every file in `projects/fpga-systems/bin/` appears somewhere in the book.

## References

- `projects/fpga-systems/bin/` -- the layer being documented
- `projects/components/retro_legacy_blocks/docs/rlb_top_mas/` -- the most recent
  book, usable as the structural template
- `bin/DOC_GENERATION.md` -- the pipeline mechanics
- `vault/handbook/fpga/uart-harness.md`, `vault/handbook/fpga/boards.md`
- [[TASK-022]] -- the lock, identity readback and identity record, which the
  board chapter has to cover

## Closed 2026-09-30

`projects/fpga-systems/docs/fpga_systems_mas/` -- 19 chapter pages across six
chapters, an index, a styles file, five mermaid diagrams with their sources, and
`generate_mas_pdf.sh`. Output: `FPGA_SYSTEMS_MAS_v1.0.pdf`, 48 pages.

| Chapter | Subject |
| --- | --- |
| 1 | Overview, layering, acronyms, references |
| 2 | The UART flow: discovery, probes, link and bridge, wire protocol, sim equivalence |
| 3 | Sequences: model, context, runner, writing one |
| 4 | Boards: registry, programming, locking and identity |
| 5 | Conventions: why the prefixes are load-bearing, path anchoring |
| 6 | Standing up a flow |

Diagrams are `.mmd` sources rendered to PNG by a Makefile in
`assets/mermaid/`, following the house pattern: layering, the UART flow as a
sequence diagram, the resolve-then-run flow, the program path with the lock and
the identity verdict, and the file layout.

## CORRECTION: the premise of this task was wrong

**This task was filed claiming three coexisting conventions that "nothing
currently says which to use". That is false, and the error was mine both times.**

There is **one** convention, and it is documented in two places that agree:

- `vault/handbook/fpga/cmn-infra/flow-layout.md` -- the skeleton and the
  filename table, with the rationale.
- `make/fpga_flow.mk:160-162` -- the same table, as the comment above the globs
  that implement it.

And the prefixes are not stylistic. They are **load-bearing**, because two
mechanisms discover files by globbing them:

    RUN_SCRIPTS   := $(sort $(wildcard $(SEQ_DIR)/run_*.py))
    SEQ_SCRIPTS   := $(sort $(wildcard $(SEQ_DIR)/seq_*.py))
    HOST_PROGRAMS := $(sort $(wildcard $(HOST_DIR)/host_*.py))

    def discover(self, path, pattern: str = "seq_*.py")

A misnamed file is not untidy, it is **invisible** -- never registered, never a
make target.

**The `flows-*/` "third convention" is the pre-migration layout.**
`flow-migration.md` names it explicitly as the thing being migrated away from.
Measured: nine build directories use `build-<name>/`; the two that do not are
`Genesys2/rapids/flows-rapids/` and `Genesys2/rapids_beats/flows-rapids-beats/`,
and **neither includes `make/fpga_flow.mk` at all**, so none of the discovery
above applies to them. Their `run_*.py` sitting in `host/` is a consequence of
predating the shared flow, not a second opinion about where runners go.

So the naming chapter is deliberately **thin**: it states that `[[flow-layout]]`
is the authority, records only what binds the conventions to this layer (the
globs), and reports the migration status as measured. Writing it as the task
originally scoped it would have produced a second copy of a handbook note --
which CLAUDE.md forbids, and for the reason on display here: the copy nobody
edits is the one the next session reads, and in this case the next session was
me, twice.

The earlier correction in this file -- six files wrongly reported as exceptions,
from an argparse proxy -- was the same error one level down. The Reed-Solomon
session measured those six and none was a sequence.

## What the book deliberately does not contain

- **Register maps.** Addressed by name through a generated map; a table here
  would be a second source nothing keeps in step.
- **Method.** Links to `vault/handbook/fpga/cmn-infra/` rather than restating:
  `uart-harness`, `boards`, `host-stack`, `sequences`, `flow-layout`,
  `flow-migration`, `area-structure`.
- **Per-area flows and the FPGA-side RTL.**

## Verification

- `generate_mas_pdf.sh` builds clean, rc=0. 48 pages, 6 embedded images (5
  diagrams + logo), **List of Figures populated with 5 entries**.
- The generator **fails by name** when a referenced diagram PNG is missing, which
  is the one build failure that is otherwise silent: a missing image drops out of
  the PDF without an error.
- `check_broken_links --ratchet`: PASS with the book TRACKED -- 2099 `.md` and
  6792 links, up from 2078 and 6768, with zero broken in the book. Staged first
  on purpose: the checker enumerates tracked files, so running it against an
  untracked book is a vacuous pass, which is exactly how 11 broken links shipped
  in a book earlier this session.
- Zero emojis (they break the LaTeX path).
- Every repo path cited in the book verified to exist; every `[[wikilink]]`
  resolved to a real handbook note. Two paths were wrong on the first pass --
  `vault/handbook/fpga/uart-harness.md` instead of `.../fpga/cmn-infra/...` --
  taken from a skill signpost rather than checked.
- `check_doc_examples`, `check_test_dut_family`, `filelist_registry --check` and
  `--audit`, `check_task_ids`: all pass.

## Follow-up worth considering, not filed

The two `flows-*` flows are a tracked migration backlog rather than a naming
question, so they belong to rapids, not to tooling. The book names them as the
measured exception; migrating them is `[[flow-migration]]`'s procedure and the
rapids area's call.
