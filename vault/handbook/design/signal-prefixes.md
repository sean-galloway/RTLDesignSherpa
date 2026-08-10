---
title: Signal prefixes r_ and w_
summary: The prefix states storage, not scope. What it promises, the five-file lie the 2026-08-10 sweep fixed, and the two codified exceptions (mem arrays, register slice aliases).
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

**This repo HAD that bug, in five files** (fixed 2026-08-10 in the prefix
sweep). `w_rd_data` in `fifo_sync`, `fifo_async`, `gaxi_fifo_sync`,
`gaxi_fifo_async` and `gaxi_drop_fifo_sync` was assigned with `<=` in the
registered and BRAM read paths - a flop wearing a wire's name, in the read
path, precisely where `REGISTERED` and `MEM_STYLE` change the latency a
reader is trying to count. The fix that generalizes: **when one signal's
storage differs per generate branch, it cannot have one truthful name - move
the name into the branch.** Each registered branch declares a branch-local
`r_rd_data` and drives the output port from it; each mux branch drives the
port straight off the array. The shared misnamed intermediate disappears
entirely (only one branch elaborates, so per-branch port drivers are legal).

## Codified exceptions (decided in the 2026-08-10 sweep)

- **Memory arrays keep the bare name `mem`.** A RAM array is storage but not
  a signal a reader counts latency through by name - latency lives in the
  read path around it, which the r_/w_ names now state truthfully. Renaming
  would touch every FIFO in the family for no reader benefit.
- **A pure slice alias of a register keeps `r_`** (e.g.
  `assign r_wr_addr = r_wr_ptr_bin[AW-1:0]` in the FIFOs). The prefix
  answers "does this value come out of a flop?" - for a bit-slice alias the
  answer is yes: it holds across the edge exactly as its source does, and
  naming it `w_` would claim combinational settling where a reader counting
  the address path would then miss the register. The mechanical check must
  whitelist assign-of-r_-slice aliases.

## Checking it

There is no gate for this yet. Until there is, the mechanical check is: for every
`w_*` in the file, confirm nothing assigns it with `<=`; for every `r_*`, confirm
nothing assigns it with `=` outside an `always_ff`.

```bash
# w_ signals driven by non-blocking assignment -- each one is a lie.
# The target must be at STATEMENT position: a bare `w_x <=` match also hits
# less-than-or-equal COMPARISONS (`if (w_count <= AET)`), and that false
# positive sent the 2026-08-10 sweep chasing two innocent signals
# (w_almost_empty_count, w_tap_positions) before the pattern was anchored.
python3 - <<'EOF'
import re, glob
for f in glob.glob('rtl/**/*.sv', recursive=True):
    s = open(f, encoding='utf-8', errors='ignore').read()
    s = re.sub(r'//[^\n]*', '', s)
    for m in re.finditer(r'(?:^|\bbegin\b|\)|;)\s*(w_\w+)(?:\s*\[[^\]]*\])*\s*<=\s*[^=]', s):
        print(f'{f}: {m.group(1)}')
EOF
```

Related: [[naming-and-style]] for the rest of the conventions,
[[signal-contracts-and-kmaps]] for naming decision logic, and
[[minimal-fsm]] — `r_state` / `w_next_state` is this rule applied to the two-process
FSM form.
