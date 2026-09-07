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
| a gate whose flags differ from the consumer's | `--lint-only` cannot see scheduling loops | "lint is clean" while every `*_mon` build was broken |

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

### 9. A gate must run the flags its consumer runs
A gate reports on the invocation it makes, not on the design. `make lint` ran
`verilator --lint-only` and reported clean for weeks while a combinational loop
in `rtl/amba/monitor` broke the build of every monitor-variant bridge. Even a
real `-cc` model build reported nothing -- Verilator optimises across the loop
and it disappears. It takes `--public-flat-rw`, which cocotb always passes, for
the cycle to exist at all:

| invocation | UNOPTFLAT |
|---|---|
| `verilator --lint-only -Wall` | 0 |
| `verilator -cc -Wall` | 0 |
| `verilator -cc --public-flat-rw --trace` | 4 |

Elaborating the design is necessary and NOT sufficient. Before trusting a green
gate, ask what its invocation differs from the one that actually consumes the
RTL -- and close the gap rather than the ticket. `make build-check` in
`projects/components/bridge/rtl` exists for this. See
[[always-comb-block-fusion]] for the defect itself and [[TASK-081]].

### 10. A gate that fails on everything reports nothing
The same bridge lint gate failed 36 of 36 variants on PINCONNECTEMPTY from
deliberately-open pins. Nobody read it, so the real findings underneath were
invisible too. Waive what is idiomatic so the signal survives -- but never
waive the class you are hunting.

### 11. A green suite is not a compiled design, and the subset chooses which
A raw `pytest val/math -q` was green while five tests were failing to BUILD.
`ow_mant_interp` had been added to `math_bf16_fast_reciprocal` and one of its
three consumers was never reconnected; PINMISSING is an ERROR under the flags
cocotb passes, so `math_bf16_newton_raphson_recip` never elaborated. Its tests
did not fail an assertion -- they never ran, and "396 passed" counted the ones
that did.

What hid it was the LEVEL. `pytest <area>` runs the default `TEST_LEVEL=FUNC`
subset, which never elaborated that module at all; `make run-all-full-parallel`
does, and found it in fifteen minutes. So: **`make clean-all &&
make run-all-full-parallel`, in every area, every time** -- the same two
commands work in `val/common`, `val/math`, `val/amba` and every
`<component>/dv/tests`, because they all include `make/tests.mk`. A raw pytest
green is a statement about a subset, and never the one you want to publish.

Cheaper than either: `bin/check_port_consumers.py` (pre-commit) lints exactly
the filelists that list a .sv whose PORT SET changed, and reports only
PINMISSING/PINNOTFOUND/PINCONNECTEMPTY. Narrow on purpose -- areas carry
pre-existing warnings, and per rule 10 a gate that fails on those reports
nothing.

### 12. Two copies of one header are two designs
`reset_defs.svh` decides whether every flop in the repo resets asynchronously.
When it was made unconditionally async, EIGHT tracked copies kept the old
conditional -- one of them live in `timing_characterization`, whose flops would
have elaborated SYNCHRONOUS while the rest of the tree was async. Both trees
compiled. Both passed. Nothing diffed them.

Seven of the eight turned out to be dead artifacts, and deleting them is not
the fix, because the reason they rotted -- nobody diffs a copy -- outlives the
deletion. `bin/check_shared_include_copies.py` does the diff, and fails on any
tracked copy that has drifted from the canonical file. A component may still
vendor a shared header to keep its filelist self-contained; what it may not do
is vendor one that DISAGREES. If a component genuinely needs different
semantics, give it a different BASENAME so the divergence is declared rather
than discovered -- see [[NEXYS-007]].

### 13. A retry that re-rolls the seed is not a retry, it is a second lottery
Every test wrapper draws `os.environ.get('SEED', str(random.randint(0,100000)))`
and every area runs `--reruns 3`. `pytest-rerunfailures` re-executes the whole
wrapper, so the retry draws a NEW seed: a seed-dependent failure gets up to
three fresh chances not to happen, and the run prints `401 passed, 1 rerun`.

Worse, the evidence is destroyed twice over. `--tb=short` prints no traceback
for a rerun that ends up passing, and the per-test log is named for test and
worker, so the passing retry OVERWRITES the failing attempt's log on that same
worker. Nothing survives to reproduce.

Randomised stimulus exists to find what directed tests miss. Retry-until-green
is exactly the policy that discards those finds -- the suite does the search
and then throws away the hits. `1 rerun` in a green summary is not a flake
reported; it is a result deleted. Pin the seed to the test NODEID so a retry
repeats the run it is retrying, and only then judge how much rerun budget is
still earning its keep. See [[TOOL-015]].

### 14. A mechanical sweep needs a mechanical check, and "it has no tests" is the reason to add one
A single commit converted every remaining flop to `ALWAYS_FF_RST` and left
SIXTEEN files Verilator cannot parse. The converter replaced the wrong `end`
with the macro's closing paren, misled by sources whose closing `end` was
misindented to line up with the inner one. Not a subtle defect: the files
could not be READ.

It survived a week because of where the damage landed. One file had a test,
and that one area's FULL run reported ten failures. The other fifteen lived in
two trees nothing runs -- and that, chased one step further, turned out to be
the more interesting finding: both were duplicates that should not have
existed (see rule 15). The blast radius of a sweep is every file it touches;
the observed radius is only the files something runs. Those are not the same
set, and the difference is exactly where a sweep's damage goes to hide.

Two corollaries, both learned the expensive way here:

**Repair from the last known-good version, not from the damaged text.** A
first repair pattern-matched `) else` and destroyed four unrelated files'
`assert property (...) else $error(...)`. The second took each file at the
commit's PARENT and re-ran the repo's own converter, whose `find_block_end`
does real begin/end depth tracking. Re-deriving is verifiable; patching
corruption is guesswork wearing a regex.

**Ask whether the sweep should have touched the file at all.** Fifteen of the
sixteen were in trees that documented themselves as macro-free ON PURPOSE. I
took that at face value and reverted them. That was wrong in a way rule 15
covers: the documented reason had expired, and I had not tested it.

`bin/check_sv_parses.py` (pre-commit) now fails any staged .sv that does not
parse. It reports only genuine syntax errors -- not missing modules, not width
warnings -- so per rule 10 it stays worth reading.

### 15. A file that explains why it is a duplicate is still a duplicate
Two trees in this repo declared themselves "macro-free forks" and gave reasons
in their own headers. I read the reasons, believed them, and reverted a sweep
that had touched them. Sean asked one question -- "the macros are designed to
support asic and fpga" -- and both reasons collapsed.

`timing_characterization/rtl/asic_only/` was 37 files, a full duplicate of
`rtl/`, same module names, differing ONLY in reset spelling. Synthesised
through Yosys + slang against ASAP7 it produced a byte-identical mapped
netlist: 396 cells, 97 flops, every cell type matching. Its stated purpose --
one source that can be characterised at several flop topologies -- had expired
when `ALWAYS_FF_RST` became unconditionally async, and the flow reading it
STILL passed `-DUSE_ASYNC_RESET`, a define meaningful only to the macro tree it
was cloned from. That dead flag was the tell.

`formal/cdc/cdc_handshake/cdc_handshake_formal.sv` claimed Yosys could not take
the macro. Ninety-two other `.sby` units stage `reset_defs.svh` and read it
with `-Iincludes`. Its own `.sby` had simply never staged it. Converted, staged,
and it proves PASS. Its header also called itself a copy of
`rtl/amba/cdc/cdc_handshake.sv` -- a file that does not exist anywhere.

**The rule.** A duplicate's justification is written once, by whoever made it,
and then never re-checked against a repo that keeps moving. Test the
justification, do not read it: preprocess both copies, synthesise both, or run
the tool the claim is about. Numbers settle it in minutes. And treat a dead
flag -- a define the file cannot use, an option the flow ignores -- as evidence
of where the file was cloned FROM.

This is rule 12 one level up. There the copies of `reset_defs.svh` had drifted;
here the copies had not drifted at all, and were still wrong, because the
reason for copying had.

### 16. Check what your gate's glob actually matches
`filelist_registry.py --blindspots` exists to find tests that hand-list RTL
instead of taking a filelist. It reported PASS while three tests in one
component were doing exactly that, one of which could not BUILD.

Its glob was `projects/**/dv/tests/test_*.py`. Project tests live one level
down, in `fub/`, `macro/`, `top/` -- the Pattern B layout
`/GLOBAL_REQUIREMENTS.md` mandates. **The gate saw 96 of 172 tests and was
blind to 76 of them, 44%**, and every one of the blind ones was in a level
subdirectory, which is to say the normal case rather than an edge case.

A gate that inspects a set is only as good as the set. Before trusting a PASS,
print the population: how many files did it actually look at, and is that the
number you expected? One line of arithmetic separates "no violations" from "no
violations among the half I looked at". Widening this glob turned up two more
real violations immediately, both latent rather than firing -- they pass today
only because their DUTs' includes happen to be supplied by hand.

Related: rule 1 (positive control), rule 10 (a gate that fails on everything
reports nothing). This is the third variant: a gate that PASSES on almost
nothing.

## The single question

Before believing any zero, ask: **if the thing I am looking for were happening,
would this code see it?**

If that has not been demonstrated *in this configuration*, the zero is about the
apparatus, not the design.

Related: [[bfm-usage]] (valid/ready gets a BFM, never a poke),
[[registers-by-name]], [[stale-sim-build]].
