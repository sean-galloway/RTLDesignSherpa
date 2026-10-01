# Context and results

```python
@dataclass
class SequenceContext:
    bus: Any = None
    board: Any = None
    params: Dict[str, Any] = field(default_factory=dict)
    results: Dict[str, Any] = field(default_factory=dict)
    log: Optional[Callable[[str], None]] = None
```

## What a sequence is given

| Field | What it carries |
| --- | --- |
| `bus` | The by-name register interface -- a `DeviceBus`, a `Device`, or an area driver. Sequences address registers by name only. |
| `board` | The `Board` this is running against, or **None in simulation**. |
| `params` | Run-level knobs from the entry point's command line. |
| `results` | What earlier sequences returned, keyed by sequence name. |
| `log` | Where `ctx.say()` writes; defaults to `print`. |

## What it is deliberately NOT given

No port. No baud rate. No bitstream path. Transport is already resolved by the
time a sequence runs, by the entry point that built the context.

`board` being None in simulation is the tell that a sequence must not depend on
it for anything load-bearing. A sequence that needs the board object to work
cannot run in sim, and has given up the property of Chapter 2.

## Helpers

```python
ctx.say("message")              # to ctx.log, or print
ctx.param("blocks", 16)         # with a default
ctx.result("init")              # RAISES if init has not run
```

`ctx.result` raising rather than returning None is deliberate. Asking for
another sequence's result is asserting a dependency; if that dependency did not
run, silence would let the sequence proceed on a default and report a number
that means nothing. The fix is one word in `requires`.

## Passing data between steps

```python
class Init(Sequence):
    name = "init"
    def run(self, ctx):
        return {"levelled": True, "taps": taps}

class Measure(Sequence):
    name = "measure"
    requires = ("init",)
    def run(self, ctx):
        taps = ctx.result("init")["taps"]
```

Neither sequence imports the other. The contract is the dictionary and the
declared `requires`, which is what lets an area reorder or replace a step
without editing its neighbours.
