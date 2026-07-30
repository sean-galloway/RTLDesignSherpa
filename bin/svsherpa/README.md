<!--
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2024-2025 sean galloway
-->

# svsherpa

Synthesizable SystemVerilog, written in Python.

A **thin emitter**, not an elaboration framework. SystemVerilog keeps the
semantics; Python supplies parameterization, loops, width algebra and checking.
The output is meant to be read, reviewed and committed like hand-written RTL.

```python
from svsherpa import *

m = Module("counter", subsystem="common", purpose="Enabled binary counter")
WIDTH = m.param("WIDTH", 8)
clk, rst_n, en = m.input("clk"), m.input("rst_n"), m.input("en")
count = m.output("count", WIDTH)

m.always_ff(clk, rst_n,
    reset = [count.set(ZERO)],
    body  = [If(en, count.set(count + 1))],
)
print(m.emit())
```

```systemverilog
module counter #(
    parameter int WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    output logic [WIDTH-1:0] count
);

    `ALWAYS_FF_RST(clk, rst_n,
        if (!rst_n)
            count <= '0;
        else if (en)
            count <= count + 1;
    )

endmodule : counter
```

## Why this instead of the alternatives

Amaranth, MyHDL, migen, PyMTL and friends are *elaboration frameworks*: they own
the semantics, build a netlist, and emit Verilog as a back end. That is why their
output is machine-shaped — mangled names, no `always_ff` idiom, no `unique case`,
no way to reach a house style or a project's reset macros. The generated file is
a build artifact you would never read.

svsherpa inverts that. There is no netlist and no semantic model of hardware. A
`Case` object is a `case` statement. An `If` is an `if`. The library's only jobs
are to render SV faithfully and to check the things Python can check. The output
is a file you would be willing to hand-review, and its diffs are readable.

The trade is real and worth naming: svsherpa will not schedule logic, infer
state machines, or stop you describing bad hardware. It stops you describing
*invalid* hardware.

## What it checks

These fire at build time, with the offending signal named.

**Errors** — the design cannot be correct:

| Check | Example caught |
|---|---|
| Multiple drivers | `q` driven by an `assign` and an `always_ff` |
| Assignment to an input | `assign a = ...` where `a` is `input` |
| Reserved words | a port named `output` or `always` |
| Duplicate identifiers | a signal reusing a port's name |
| Instance port names | typo'd or missing connection, checked against the child's real ports |
| Non-lvalue assignment | `(a + b).set(...)` |
| Non-lvalue select | `(a * b)[7:0]`, which is not legal SV |

**Warnings** — legal but usually wrong:

| Check | Example caught |
|---|---|
| Width mismatch | 8-bit source into a 4-bit target |
| Latch inference | `always_comb` with an `if` and no `else` |
| Logical operand width | `a && b` on 8-bit vectors (means `(a!=0) && (b!=0)`) |
| Undriven output | an `output` never assigned |
| Unused signal | a declared `logic` never referenced |

Width checking is deliberately conservative: only *provable* mismatches are
reported. `A_WIDTH` and `B_WIDTH` may well be equal at elaboration, so that pair
is left alone. `(WIDTH-1)+1` is normalised to `WIDTH`, so it does not warn either.

## Design decisions worth knowing

**Assignment does not name its operator.** You write `sig.set(value)`; the
enclosing block decides. `always_ff` emits `<=`, `always_comb` emits `=`, module
scope emits `assign`. The blocking/non-blocking bug is not expressible.

**Widths are symbolic.** A width is a small algebraic expression, not an int, so
`WIDTH-1`, `$clog2(DEPTH)+1` and `2*N-1` all work as widths *and* as
expressions — the same as in SV. `clog2(8)` folds to `3`; `clog2(DEPTH)` stays
symbolic.

**Indexing is dimension-aware.** On `logic [7:0] mem [16]`, `mem[i]` is 8 bits.
On `logic [N-1:0][W-1:0] q`, `q[i]` is `W` bits. Both are the mistakes that
unpacked and packed 2-D declarations invite.

**Expressions are immutable; only `Module` is mutable.** `If(...).Else(...)`
returns a new object, so a partially built conditional is safe to share.

**One Python wart, accepted deliberately.** `a == b` builds an SV `==`
expression rather than comparing objects, because reading like SV matters more
here. Expressions therefore hash by identity; use `same(x, y)` for structural
comparison. Python cannot overload `and`/`or`/`not`, so those are `.land()`,
`.lor()`, `.lnot()`.

**Precedence-aware rendering.** Parentheses appear only where SV needs them,
except that comparisons under `&&`/`||` are always parenthesised because that is
how it gets written by hand. `~(a | b)` keeps its parens — dropping them would
change the circuit, and `~|` would be a reduction NOR.

## Verification

The generator is only useful if its output really elaborates, so verification is
part of the library:

```python
report = verify(m)          # verilator --lint-only + yosys synth check
assert report.ok, str(report)
```

Each checker degrades to `skipped` when its tool is absent, so the suite still
runs without the full flow. `verify(m, style=True, waiver_file=...)` adds
`verible-verilog-lint` against the project waivers.

## Reset styles

Reset is a module-wide setting, because mixing styles within a design is how
reset bugs get in.

| `reset_style` | Emits |
|---|---|
| `macro` (default) | `` `ALWAYS_FF_RST(clk, rst_n, ...) `` — house style |
| `async_low` / `async_high` | `@(posedge clk or negedge rst_n)` |
| `sync_low` / `sync_high` | `@(posedge clk)`, reset tested inside |

`use_rst_asserted=True` emits `` `RST_ASSERTED(rst_n) `` instead of a hardcoded
`!rst_n`, which keeps polarity selection with `reset_defs.svh` where it belongs.

## Covered SystemVerilog subset

Everything in `verilog_condensed_lrm.sv`, each round-tripped through verilator
and yosys in `tests/test_toolchain.py`:

- all operator classes — arithmetic, relational, equality (incl. `===`/`!==`),
  logical, bitwise, shift, reduction
- `assign`, `always_comb`, `always_ff`, `always_latch`
- `if`/`else if`/`else`, `case`, `unique case`, `priority case`, `casez`
- Moore and Mealy FSMs; binary, one-hot and gray encodings
- `typedef enum`, `typedef struct packed` with named field access
- packed and unpacked arrays, inferred memories
- `generate` — `for` with `genvar`, `if`/`else` with labelled scopes
- parameterized instantiation, instance arrays
- `localparam`, `$clog2`, sized casts, concatenation, replication, `'0`/`'1`

Not covered: interfaces and modports (the LRM marks them optional), classes,
UVM, and anything non-synthesizable. `RawExpr` and `Raw` are the escape hatches.

## Layout

| File | Contents |
|---|---|
| `symint.py` | symbolic width algebra |
| `expr.py` | expression tree, precedence, width inference, lvalue rules |
| `signals.py` | signals, ports, parameters, declarations |
| `stmt.py` | `if`/`case`/blocks/assignment |
| `procs.py` | `always_comb`/`always_ff`, reset styles, latch analysis |
| `svtypes.py` | packed enums and structs |
| `instance.py` | sub-module instantiation |
| `generate.py` | `generate` constructs |
| `header.py` | SPDX and the structured doc banner |
| `module.py` | the `Module` builder and file emission |
| `tools.py` | verilator / verible / yosys verification |

Named `svtypes.py`, not `types.py`, because the latter shadows a stdlib module
and breaks the interpreter when the package directory is on `sys.path`.

## Running the tests

```bash
cd bin
python -m pytest svsherpa/tests -q
python -m pytest svsherpa/tests -q --cov=svsherpa --cov-report=term-missing
python -m pytest svsherpa/tests -q -m "not toolchain"   # skip verilator/yosys
```

## Possible next steps

- **Parameter legality via CP-SAT.** Headers already document constraints like
  *"MAX must fit within WIDTH-1 bits"*. Those are a finite constraint problem:
  prove no legal parameter tuple violates them, or enumerate legal tuples to
  drive a regression matrix. OR-Tools is already a project dependency.
- **WaveJSON generation.** The doc banner accepts a `wavedrom` field today, but
  it is authored. Since the generator knows the register and FSM structure, it
  could emit the diagram, and emit matching `TemporalConstraint` stubs for the
  cocotb wavedrom checkers.
- **Interfaces and modports**, if the optional part of the LRM becomes load-bearing.
- **Porting `bin/rtl_generators`.** The existing string-based `verilog/module.py`
  has no width tracking or checking; the arithmetic generators (Dadda, Brent-Kung,
  IEEE-754) would gain width checking for free.
