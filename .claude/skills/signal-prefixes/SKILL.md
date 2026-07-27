---
name: signal-prefixes
description: Signal naming - r_ means flopped, w_ means combinational. Use when writing, renaming or reviewing any RTL signal, or when counting pipeline latency from a module you did not write.
---

# signal-prefixes

READ FIRST: vault/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: vault/handbook/design/signal-prefixes.md.

The prefix answers exactly one question: does this signal come out of a flop?

- `r_*` — non-blocking assign inside `always_ff`. Holds across a clock edge.
- `w_*` — `assign`, or blocking assign inside `always_comb`. Settles this cycle.

It is not scope, not type, not intent. Ports never take it — they take the port
convention (`i_`/`o_` on common blocks, protocol names on AMBA).

Why it is load-bearing rather than cosmetic: a reader counting pipeline stages
or chasing a timing path does it from names, without opening every `always_`
block. A wrong prefix is a false latency claim in the one place a reader trusts
by default. The handbook note names a live instance in this repo — a `w_rd_data`
that is a flop, in a read path, where `REGISTERED`/`MEM_STYLE` change the very
latency being counted.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
