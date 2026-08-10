---
title: Silent fallbacks and the false-negative trap
summary: Almost every wrong conclusion in DV comes from something that did not happen without saying so. Make absence loud, and never trust a zero from an unproven apparatus.
---

# Silent fallbacks and the false-negative trap

One session chasing a missing monitor packet produced **fifteen** wrong
conclusions. Every one had the same shape:

> something did not happen, nothing said so, and the absence was read as
> evidence about the design.

Not fifteen mistakes. One mistake, fifteen times.

## The catalogue (all real, all from one session)

| What fell back | To what | Reported as |
|---|---|---|
| `set_axi_timing_profile('slow')` -- name does not exist | `'fixed'`, WARNING only | "the timeout cone never fires" |
| `mon_ready` never driven (it is an INPUT) | arbiter wedges on client 0 | "the read monitor emits nothing" |
| capture sampled `valid` without `ready` | one stuck beat counted per cycle | 13,568 phantom packets |
| `if bfm:` on a BFM defining `__len__` | falsy when its queue is empty | "zero packets" while it held 608 |
| `getattr(dut, port, None)` then skip | arming did nothing | "the cone is dead" |
| `apb_addr_width` default 12 vs a map needing 13 | `0x10E0` -> `0x0E0`, `0x1100` -> `GLOBAL_CTRL` | "ten hookup defects" |
| `0xDEADBEEF` no-response sentinel | satisfied 4 of 5 per-bit checks | "the register works" |
| counting packets by TYPE, not agent | other blocks' completions | "the enable does not gate" |
| RDL `default` on a hw-mirrored status reg | `CHANNEL_IDLE=0xF` is CORRECT | "9 register defects" |
| bitstream copy path mismatch | WARNING, exit 0 | month-old `.bit` looked current |
| one of two root vars unset | built the OLD tree's bridge | a clean build of a stale design |

And, while writing the fix for the address trap, a `try/except` that returned
the floor on failure -- **a silent fallback inside the silent-fallback fix.**
It always returned 12 and re-broke the thing it was added to protect.

## Why these are worse than crashes

A crash costs minutes. A silent fallback produces a *plausible number*, and a
plausible number gets reported, acted on, and built upon. Several of these were
escalated as RTL defects with candidate root causes before the apparatus was
checked.

The asymmetry that matters: **a false positive is usually caught by the next
test; a false negative closes the investigation.** "No packets" ends the search
in the wrong place.

## The rules

### 1. Positive control before any negative conclusion
Never report "X did not happen" until the same apparatus, in the same
configuration, has been shown to detect X. If the positive case fails, you know
NOTHING about the negative -- do not report it.

Concretely: run the positive case FIRST. A pass/fail pair where the positive
fails is not evidence of a design problem; it is an untested instrument.

### 2. No silent skips -- missing means fatal
`getattr(obj, name, None)` followed by `if x is not None:` is a skip. In a test
that measures ABSENCE, a skip is indistinguishable from a pass. Raise, and say
what would have been meaningless:

```python
if sig is None:
    raise RuntimeError(f"no port {name} -- arming did nothing, so a "
                       f"'no packets' result would be meaningless")
```

### 3. A lookup miss is an error, not a default
Unknown profile name, unknown register, unknown mode: raise and list the valid
values. `set_axi_timing_profile` warned and substituted `'fixed'`; the stall
never happened and the test blamed the DUT.

### 4. Sentinels are checked by value, never by bit
`0xDEADBEEF` has bits 0,2,3,6 set, so it passes most "is bit N set?" tests.
Compare the whole word against the sentinel explicitly, first.

### 5. Size from the source of truth, never from a remembered constant
The APB width came from a hardcoded 12 while the register map needed 13. The map
knows. Ask it -- and if it cannot be read, fail rather than guess low, because
guessing low aliases addresses onto OTHER registers instead of erroring.

### 6. Attribute measurements, do not just count them
A shared bus carries several agents. Filter by the agent under test or you will
report someone else's traffic as your DUT's.

### 7. Field-level attributes beat register-level ones
`CHANNEL_IDLE` is `sw='rw'` at register level and `sw='r'` in every field. The
RDL `default` describes STORAGE; a hw-mirrored field has none, so its "default"
describes nothing. Build masks from fields.

### 8. Truthiness never, on framework objects
`if bfm:` calls `__len__`. Use `is not None`.

## The single question

Before believing any zero, ask: **if the thing I am looking for were happening,
would this code see it?**

If that has not been demonstrated *in this configuration*, the zero is about the
apparatus, not the design.

Related: [[bfm-usage]] (valid/ready gets a BFM, never a poke),
[[registers-by-name]], [[stale-sim-build]].
