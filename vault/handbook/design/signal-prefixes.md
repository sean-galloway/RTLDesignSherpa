---
title: Signal prefixes r_ and w_
summary: The prefix states storage, not scope. What it promises, and the places in this repo where it currently lies.
---

# Signal prefixes: r_ and w_

The prefix answers one question and only one: **does this signal come out of a
flop?**

- `r_*` — driven by a non-blocking assign inside `always_ff`. It holds its value
  across a clock edge. Reading it costs you a cycle of latency.
- `w_*` — driven by `assign` or by a blocking assign inside `always_comb`. It
  settles within the cycle. Reading it costs you combinational depth.

That is the whole rule, and its value is that a reader counting pipeline stages
or hunting a timing path can do so from names alone, without opening every
`always_` block in the file. `rtl/` carries roughly 53 000 `w_*` and 4 600 `r_*`
references, so the convention is load-bearing: a wrong prefix is not a style nit,
it is a false statement about latency in the one place a reader trusts by
default.

## What the prefix does NOT mean

- **Not scope.** Both are module-internal. Ports never take `r_`/`w_` — they take
  the port convention (`i_`/`o_` on common blocks, bare protocol names on AMBA).
- **Not type.** Both are `logic`. `w_` does not mean `wire` the keyword.
- **Not direction of intent.** `w_foo_d` meaning "the D input of flop `r_foo`" is
  the idiom, and it is a `w_` because it genuinely is combinational.

## The failure this prevents

A name that lies about storage misleads exactly where it matters most: someone
counting read latency. The canonical shape is a signal named `w_` that is in fact
registered on some configuration path, so the page — and the reader — undercount
the pipeline by a cycle.

**This repo has that bug today.** `w_rd_data` in `rtl/common/fifo_sync.sv` (lines
~417/444/467) and `rtl/cdc/fifo_async.sv` (~897/924/944) is assigned with `<=`
inside `always_ff` in the registered and BRAM read paths. It is a flop wearing a
wire's name, in the read path, which is precisely where `REGISTERED` and
`MEM_STYLE` change the latency a reader is trying to count. It wants to be
`r_rd_data` in those branches. Left as-is deliberately for now — renaming touches
the mux-mode branch too and wants its own commit with a clean regression — but it
is the example to point at when someone asks why the prefix matters.

## Checking it

There is no gate for this yet. Until there is, the mechanical check is: for every
`w_*` in the file, confirm nothing assigns it with `<=`; for every `r_*`, confirm
nothing assigns it with `=` outside an `always_ff`.

```bash
# w_ signals driven by non-blocking assignment -- each one is a lie
python3 - <<'EOF'
import re, glob
for f in glob.glob('rtl/**/*.sv', recursive=True):
    s = open(f, encoding='utf-8', errors='ignore').read()
    for blk in re.findall(r'always_ff\b(.*?)(?=always_|endmodule)', s, re.S):
        for v in sorted(set(re.findall(r'\b(w_\w+)\s*<=', blk))):
            print(f'{f}: {v}')
EOF
```

Related: [[naming-and-style]] for the rest of the conventions,
[[signal-contracts-and-kmaps]] for naming decision logic, and
[[minimal-fsm]] — `r_state` / `w_next_state` is this rule applied to the two-process
FSM form.
