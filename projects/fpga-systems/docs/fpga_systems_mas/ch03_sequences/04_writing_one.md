# Writing a sequence

## The skeleton

```python
# <area>/bin/seq_measure.py
from __future__ import annotations

import <area>_env  # noqa: F401   -- side effect: sets sys.path
from sequence import Sequence


class Measure(Sequence):
    name = "measure"
    requires = ("init",)
    description = "sweep the delay line and record the eye"

    def run(self, ctx):
        width = ctx.param("width", 32)
        taps = ctx.result("init")["taps"]
        ctx.say(f"[measure] sweeping {width} points from tap {taps[0]}")
        ...
        return {"eye": eye}
```

Three things to copy exactly:

1. **`import <area>_env` first**, for its side effect. Chapter 5 explains what it
   does and why it is not a `sys.path` hack written inline.
2. **`requires` names every earlier step whose result you read.** If you call
   `ctx.result("init")`, declare it -- otherwise the runner cannot tell you
   scheduled them wrongly, and `ctx.result` will raise at the worst moment
   instead of at resolve time.
3. **Return something.** It lands in `ctx.results[name]` for later steps. Return
   `False` only to mean "this step failed".

## The file goes in the area's bin/

`seq_*.py` lives in `<area>/bin/`, not in a build directory, because sequences
are shared by every build in that area and by the simulation harness. The
prefix is how both `SequenceRunner.discover` and `make` find it -- see
Chapter 5.

## Checklist

- [ ] Does it touch `ctx.bus` only, never a port or a bridge constructor?
- [ ] Does it work with `ctx.board` as None, so it runs in simulation?
- [ ] Does `requires` list every result it reads?
- [ ] Does it address registers by name rather than by offset?
- [ ] Is the name unique within the area?
- [ ] Does `description` say what it does in one line, for `catalog()`?

The first two are the ones that matter. A sequence failing either has quietly
become board-only, and the sim half of the equivalence stops testing anything.

## What does NOT belong in a sequence

| Not this | Where it goes |
| --- | --- |
| `argparse` | The entry point |
| Port resolution | The entry point |
| Board programming | The entry point, or `make program` |
| Reusable drivers and verdict logic | A library in the area's `bin/` |
| Printing a final report | The entry point, from the `RunReport` |

A sequence that has grown an `ArgumentParser` is an entry point wearing the
wrong prefix, and it has lost the ability to be composed with others.
