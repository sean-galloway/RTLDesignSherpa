# The sequence model

A campaign is an **init sequence** followed by one or more **test sequences**.
`sequence.py` provides the container; an area provides the sequences.

```python
runner = SequenceRunner(ctx)
runner.discover("projects/fpga-systems/NexysA7/pumice/bin")
report = runner.run(["init", "write_read"])
```

## Two rules, enforced rather than recommended

Both of the failure modes these prevent are silent, which is why they are
checked in code rather than written in a style guide.

### 1. A sequence never opens its own port

A sequence is handed a `SequenceContext` carrying an already-built bus. It does
not take a `--port`, does not call `find_port`, and does not construct a bridge.

That is what makes the identical sequence run against the FPGA and against a
cocotb simulation -- only the injected bus differs. A sequence that resolved its
own transport would break the equivalence of Chapter 2, which is the one
property the whole stack exists to preserve.

### 2. Names are declared and resolved up front

Every sequence declares a `name`. The runner resolves the entire requested
order, plus every `requires`, **before any traffic reaches the board**.

A misspelled name therefore raises immediately instead of skipping a step. This
matters more than it sounds: a skipped init looks exactly like a DDR2 timing
bug, and costs the same hour to chase.

## Anatomy

```python
class Sequence:
    name: str = ""
    description: str = ""
    requires: Seq[str] = ()

    def run(self, ctx) -> Any: ...
    def setup(self, ctx) -> None: ...      # optional, default no-op
    def teardown(self, ctx) -> None: ...   # optional, default no-op
```

The return value of `run` is stored in `ctx.results[name]`, which is how a later
sequence consumes an earlier one's output without either knowing the other's
internals.

Returning `False` explicitly marks the step failed. Any other value -- including
None -- is a pass.

## The decorator form

For steps needing no setup or teardown:

```python
@sequence("write_read", requires=("init",))
def write_read(ctx):
    """One-line description, taken from this docstring."""
    ...
```

This builds the same `Sequence` subclass. The description defaults to the first
line of the docstring.

## A real example

```python
class Smoke(Sequence):
    name = "smoke"
    requires = ("init",)
    description = "bypass, clean, e = t, e = t + 1"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        blocks = ctx.param("blocks", 16)
        ...
```

Note what it touches: `ctx.bus` for the device, `ctx.result("init")` for the
previous step's output, `ctx.param` for a run-level knob. No port, no baud rate,
no board.
