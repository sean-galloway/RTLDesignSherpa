# TASK-024: fpga-systems has no specification -- document the UART flow and the host/seq naming conventions as a chapter book with a PDF

**Priority:** P2
**Status:** open
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
