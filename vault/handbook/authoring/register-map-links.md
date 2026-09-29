---
title: Register maps live in one place, and the README links to it
summary: A beside-code README states the register map ONCE, as a real markdown link to the MAS register chapter. The criterion for when to link, the exact link form, why a backticked path is invisible to the link checker, and the two shapes that correctly keep their table.
---

# Register maps live in one place, and the README links to it

[[doc-placement]] already gives the principle: a beside-code file is a link,
never a second copy. This note is the METHOD for the case that produces the most
drift in practice -- a register map restated in a block's `README.md` when the
block's MAS book already documents it.

## The rule

**A beside-code README does not carry a register-map table. It links to the MAS
register chapter.** One source per fact, and the register chapter is the source,
because it is the one a reader of the spec is sent to and the one kept in step
with the RDL.

## When the rule applies, and when it does not

Apply it when BOTH hold:

1. the README carries a table whose columns are offsets and register names, and
2. the block's MAS book has `ch05_registers/01_register_map.md` and that chapter
   **demonstrably lists the same offsets**.

Check (2) by opening the chapter, not by counting pages or matching names. Two
shapes correctly KEEP their table, and they define the boundary:

- **A table that argues rather than maps.** `rlb/pm_acpi`'s
  `| field | why |` explains which registers are storage-only and why
  (issue #54 H3). It is an argument about the design, not an address map, and
  the book does not carry it.
- **No table at all.** `rlb/ioapic` and `rlb/apbx_xbar` have no register table,
  so there is nothing to convert. Do not add a link where there was no
  duplication.

## The exact form

```markdown
Twelve 32-bit registers at word offsets 0x000-0x02C. The authoritative map,
field definitions and access rules live in the MAS register chapter:
[ch05_registers/01_register_map.md](../../docs/<block>_mas/ch05_registers/01_register_map.md).
```

Three things that matter:

- **A real markdown link, never a backticked path.** This is not style. The link
  checker's only link pattern is
  `LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+?)(?:#[^)\s]*)?\)")`
  (`bin/check_broken_links.py:60`). A bare path in backticks does not match it,
  so it is **not a link the checker can see** -- not merely unvalidated, but
  invisible. It will never be reported broken no matter how wrong it is.
- **`../../docs/...`, not `docs/...`.** From `rtl/<block>/README.md` the book is
  two levels up. `rlb/gpio` carried `` `docs/gpio_mas/...` `` for months; it
  resolved to `rtl/gpio/docs/...`, which does not exist, and nothing noticed
  because of the point above.
- **Keep the one-line summary.** "Twelve 32-bit registers at word offsets
  0x000-0x02C" is worth stating beside the code; the table is not. Keep any
  decode note too ("everything else in the window answers with PSLVERR") -- that
  is directory-level behaviour, not register documentation.

## Why this is a correctness fix, not tidying

A restated map does not merely duplicate -- it drifts, silently, because nothing
compares it to anything. Measured on RLB, 2026-09-29:

- `rlb/hpet`'s README documented `TIMER_CONFIG[5]` as `TIMER_SIZE - 0=32-bit,
  1=64-bit`. The book and the RDL have `[5] size_cap` as a READ-ONLY capability
  bit, `timer_32mode` at `[8]` with the OPPOSITE polarity, and a note that
  "the retired `timer_size` meant the opposite". The README also listed a
  `TIMER_ENABLE` at `[2]` that does not exist -- the book says
  `timer_int_enable` there is "the ONLY per-timer enable the spec defines".
- The same README's timer table listed `+0x0C` twice, as
  `TIMER_COMPARATOR_HI` and again as `RESERVED`.
- `rlb/gpio`'s own README records the previous round of this: "an earlier
  revision of this README carried a 16-bit LO/HI split map that never matched
  the RTL."

Anyone driving the block from the README would have got it wrong. Deleting the
table in favour of the link removed the defect.

## Verifying a conversion

1. Every new link resolves from its own directory -- normalise
   `rtl/<block>/README.md` + the relative path and stat it. Do not assume.
2. `python3 bin/check_broken_links.py --ratchet` -- the VALIDATED link count
   should RISE by the number of links added, and broken must not move. A
   conversion that leaves the count flat means the links are not being seen.
3. Sweep for survivors: no README should still match
   `^\| *(Offset|Address) *\|`.
4. The prose you meant to keep is still there. Check it, do not assume the
   replacement was surgical.

## What this cost to get right

Four successive measurements pointed the wrong way before one file was read end
to end: README-vs-book page counts said convert five, keyword overlap said
convert five, UPPER_CASE identifier overlap said convert `smbus` (the clearest
only-copy case in the set, scoring 88% because register NAMES appear in any
register chapter), and a string comparison scored `uart_16550` at 0% because the
book uses 16550 spec names (`IER`) where the README uses RDL names (`UART_IER`)
-- the same registers at the same offsets.

The measurement that worked was naming a control in advance: `smbus` was
designated "must score low or the method is invalid", and it scored highest.
Use a control.

Related: [[doc-placement]], [[checkable-claims]], [[module-doc-template]].
