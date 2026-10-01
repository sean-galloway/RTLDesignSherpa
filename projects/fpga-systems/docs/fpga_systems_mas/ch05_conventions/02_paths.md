# Resolving paths

**Anchor to a marker; never count directory levels.** This has a date and a cost
attached, recorded in `[[flow-layout]]`.

## What happened

The shared board and UART layer moved from `fpga/bin` to
`projects/fpga-systems/bin`, and every hand-counted path broke at once:

- `pumice_env.py` counted five levels to the repo root.
- `ddr2_char.py` carried its own copy of the same walk.
- `uart_link.py` counted three and silently resolved to
  `<root>/projects/projects/...`.
- A test asserted the literal string `fpga/bin/program_fpga.tcl`.

Four independent copies of one fact, each broken separately, none of which told
you what was wrong -- a wrong path produces an `ImportError` naming a module,
not a layout.

## The pattern

Each area keeps exactly one module that knows where the shared layer is. It
searches **upward for a marker file**, honouring `REPO_ROOT` first:

```python
_MARKER = os.path.join("projects", "fpga-systems", "bin", "uart_link.py")

def _repo_root() -> str:
    env = os.environ.get("REPO_ROOT")
    if env and os.path.isfile(os.path.join(env, _MARKER)):
        return env
    here = os.path.dirname(os.path.abspath(__file__))
    while True:
        if os.path.isfile(os.path.join(here, _MARKER)):
            return here
        parent = os.path.dirname(here)
        if parent == here:
            raise RuntimeError("cannot find the repo root")
        here = parent
```

then puts the shared directory, and any area-local directory, on `sys.path`:

```python
FPGA_BIN = os.path.join(REPO_ROOT, "projects", "fpga-systems", "bin")
for p in (FPGA_BIN, HOST_DIR):
    if p not in sys.path:
        sys.path.insert(0, p)
```

Cost is one `os.path.isfile` per level. Benefit is that the next move breaks
nothing.

## Using it

Import it first, for its side effect, before importing anything shared:

```python
import rs_env  # noqa: F401
from sequence import Sequence
from boards import get_board
```

The `noqa` is load-bearing documentation: a linter would otherwise remove an
import whose only purpose is the side effect, and the file would fail at the
next line.

## Why an entry point still needs it

`env_python` puts `projects/fpga-systems/bin` on `PYTHONPATH`, so `sequence`,
`boards` and `uart_link` import by bare name in a properly configured shell.
That does **not** cover the area's own `bin/`, where its drivers and sequences
live. A host program under `build-<variant>/host/` importing an area library
therefore still needs the environment module, and omitting it produces an
`ImportError` on a first board run -- found exactly that way in the
reed-solomon flow.

If the chapter's skeleton (Chapter 6) looks like it has a redundant import at
the top, that is the one.

## The corollary for generators

A tool that writes output must anchor its default output path to **its own
location**, not the current directory. `elaborate_a7ddrphy.py` defaulted to a
bare relative path and, run from the wrong directory, produced
`rtl-vivado/rtl-vivado/a7ddrphy/`.

## One name, one thing

Two files called `run_smoke.py` once lived in one flow -- the sequence runner in
`bin/` and an older end-to-end program in `host/`. Different code, same name,
and `make run-smoke` could only ever mean one of them.
