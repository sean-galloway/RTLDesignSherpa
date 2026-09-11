---
title: Generated RTL discipline
summary: A fix applied to generated RTL without back-porting its generator resurrects the bug on the next regeneration; regen-and-diff is the audit.
---

# Generated RTL discipline

CLAUDE.md's Critical Rule #0 covers one direction: change a generator, delete
and regenerate everything it produces. This note records the INVERSE failure,
which Rule #0 does not catch and which accumulated silently for months.

**Fixing the generated .sv without back-porting the generator plants a
time bomb: the next regeneration silently resurrects the bug.** The header
says `AUTO-GENERATED - DO NOT EDIT MANUALLY`, but under deadline the .sv gets
the fix and the .py does not — and nothing runs the generator again for
months, so nothing notices.

*Case (2026-08-10, found during MATH-007):* regenerating the bf16 + ieee754
families into a temp dir and diffing against the tree found **13 generated
files carrying tree-only hand-fixes**, three of them whole bug classes:

- the MATH-001 RNE fix (guard export, true sticky, `G & (R|S|LSB)`) in
  bf16/fp32 mantissa_mult + multiplier — the generators still emitted the
  folded sticky that MATH-001 removed;
- the count_leading_zeros bit-reverse wrappers in five adder/FMA generators —
  dead wrong since d62b794d fixed CLZ to count from the MSB; a regen would
  have reintroduced reversed operands into working RTL;
- the e4m3 exp=15 round-carry overflow wrap guard in `fp8_e4m3_multiplier`
  and `fp16_to_fp8_e4m3` — and back-porting it into the shared conversion
  template propagated the fix to `bf16_to_fp8_e4m3` and `fp32_to_fp8_e4m3`,
  where the same bug was still LIVE (input ~510 silently returned +0.0 with
  no flags; before/after sim proved it).

The same sweep found the formal harnesses for both mantissa_mults still
asserting the pre-MATH-001 folded-sticky contract — a fix has to land in the
generator, the RTL, the docs, the TB model, AND the formal properties, or the
next audit relitigates it.

## The rules

- **Fix the generator first, then regenerate.** If the fire drill demanded a
  direct .sv edit, back-port to the .py in the same change — the generator diff
  is part of the fix, not a follow-up.
- **Regen-and-diff is the audit, and it is cheap.** Regenerate everything into
  a temp dir and diff against the tree (ignore the `// Created:` date line).
  Any hunk is either an un-backported hand-fix (back-port it) or an intended
  generator improvement (adopt it). Zero-diff is the healthy state.
- **A shared template fixed once fixes every instantiation** — that is the
  point of generating. The e4m3 wrap guard was hand-fixed in one conversion
  and latent in two siblings until the template got the fix.

## Generated code has a SIZE contract with the tools, not just a content one

Adding registers to an RDL is not a neutral act. Measured 2026-08-31: nine new
registers grew a PeakRDL regblock from `'h88` to `'hb4`, and that was enough to
push the generated module across **Verilator's inlining threshold** — at `'h88`
`obs_regs_top` is inlined with no separate C++ class, at `'hb4` it gets its own
class and its struct output port is emitted as `VL_OUT8(hwif_out,0,0)`, one
bit. So a regeneration can change how a downstream tool STRUCTURES the design,
not just what the design contains.

State the evidence precisely, because the first version of this note did not:

- **Verified here:** the inline flip at `'h88` -> `'hb4`, by building the same
  consumer closure at both sizes.
- **Verified here:** at `'h88`, with a correctly resolved source list, that
  closure verilates AND compiles with zero errors.
- **Reported by the consuming session, not verified here:** that `'hb4` broke
  their real build. Plausible and consistent, but their diagnostic repro was
  later found faulty, and re-testing `'hb4` would mean re-breaking a shared
  tree, so it stays unverified.
- **RETRACTED:** an earlier version of this note claimed a *pre-existing
  structural* Verilator typedef bug underneath all this. There is none. See
  the next section for what actually produced that illusion.

The durable part regardless: **`verilator --lint-only` cannot see any of this.**
Lint passes clean at both sizes with every waiver removed; only the C++ codegen
and compile differ. If your gate for generated RTL is lint, it is blind to the
class — run an actual `--cc` plus `make -f V<top>.mk` on at least one consumer.

## Never pass a raw `-f` filelist straight to verilator

This is the trap that manufactured the "structural Verilator bug" above, and it
cost two sessions most of a day.

These filelists compose with `-f`, and the same sub-filelist is reached down
several paths, so **a filelist expands with duplicates**. It is not a
combining-two-tops artifact — a SINGLE filelist self-duplicates. Measured
2026-08-31 over `rtl/amba/filelists/` + the misc observers: **66 filelists
affected**, `amba_all.f` at 322 redundant entries of 700,
`axi4_intf_master_observer.f` at 69 of 119.

Verilator does not deduplicate. Compile a package twice and it mints two
distinct C++ types for one typedef, and struct assignments across module
boundaries then fail with `__struct__0` vs `__struct__1`. Add `-Wno-fatal` and
verilate marches past that and emits a degraded one-bit struct port. Both look
exactly like RTL defects. Neither is.

The real build is immune only because `get_sources_from_filelist()` dedupes.
So: resolve through the Python helper, the way the build does —

    python3 -c "
    import os
    from TBClasses.shared.filelist_utils import get_sources_from_filelist as G
    s, inc = G(repo_root=os.environ['REPO_ROOT'], filelist_path='<path>.f')
    print('\n'.join(s))"

— and never hand a bare `-f` to verilator, `--lint-only` included. The earlier
wording here said "for anything past `--lint-only`"; that was too generous.
`make lint` was handed a raw `-f` and reported 81 MODDUP warnings on the stream
harness, i.e. the lint gate and the simulator were compiling different designs.

**The flow now does this for you (2026-08-31).** `make/fpga_flow.mk` grew a
`flat-filelist` target: it runs `bin/flatten_filelist.py --resolve-env
--absolute-paths`, which expands the `-f` tree and dedupes keeping first
occurrence, so compile order survives. `lint` depends on it and passes the
flattened list. The target FAILS rather than falls back if the flatten does not
happen, and asserts the result actually is duplicate-free -- a silent fallback
to the raw list would restore the bug invisibly. Verified byte-identical to the
Python helper's closure: stream build-mon 158 sources / 158 unique, MODDUP
81 -> 0; pumice build-perf 134.

`bin/flatten_filelist.py` already existed and already deduped. Nobody had wired
it into the flow, which is the more useful lesson: check for the tool before
writing the workaround.

Still open: fixing it at the SOURCE, so the graph does not self-duplicate in the
first place (dedupe in the filelist graph, or a `--check-dup` in
`bin/filelist_registry.py`). The flatten step makes every make-driven consumer
safe; it does nothing for someone typing verilator by hand.

## Regenerate into the directory the FILELIST consumes

Check where the build actually reads from before running the generator. A
second, orphaned copy of generated output is a live trap: it satisfies nothing,
drifts silently, and captures the next regen that uses a default `-o`.
*Case: `projects/components/misc/rtl/generated/` was referenced by no filelist,
Makefile or script, had already diverged from the real
`rtl/regs/generated/`, and swallowed the first regen attempt — the build kept
compiling the stale copy while the "regenerated" one sat unused. It bit a second
time on 2026-09-01: extending `obs_regs.rdl` left the orphan holding a regblock
with none of the new registers, indistinguishable at a glance from the live one.
REMOVED that day (95 files), along with an orphaned `rtl/regs/obs_regs_top.md`
that no longer matched the generated docs. The single source is now
`rtl/obs_regs.rdl` -> `rtl/regs/generated/` (RTL + docs + regmap), plus the
hand-maintained `rtl/regs/obs_regs.vlt` waiver the filelists name directly.
Regenerate with an EXPLICIT `-o`, never the default:*

```
python3 bin/peakrdl_generate.py projects/components/misc/rtl/obs_regs.rdl \
    -o projects/components/misc/rtl/regs/generated --no-html
```

*The rule the case argues for: a shared regblock lives ONCE, in the component
that owns it, and consumers reference it from a filelist (or at most take a
copy) — they never generate their own. `obs_regs` is consumed by both Genesys 2
stream and NexysA7 pumice this way.*

## A generator edit must be checked against every TOPOLOGY it emits, not every file

Fixing BRIDGE-011 (gate `awready` on the tracking FIFO being not-full) took
THREE regressions to land, and all three were the same mistake: I validated the
change on `bridge_2x2_rw` -- one config, all-AXI4, read and write -- and
generalised to 36 configs whose adapters are not shaped like it.

| break | what I assumed | what was true |
|---|---|---|
| 44 failed | every adapter has a write channel | read-only bridges have no write block, and I had put BOTH channels' declarations in it |
| 44 failed | the crossbar-facing block is the AXI4 timing wrapper | APB/AXIL slaves use a SHIM instead, so the gated ready had no driver |
| 5 failed | a shim's `pfx` means "the crossbar" | in `*_mon` variants it is the INTERNAL wrapper-to-shim net; gating both collapsed two nets onto one signal (MULTIDRIVEN) |

The generator emits a small number of TOPOLOGIES -- wrapper only, shim only,
wrapper->shim chained, read-only, write-only -- and a change to a handshake
has to be reasoned about in each. "It regenerated cleanly and 2x2 passes" is
evidence about one topology.

Cheap check that finds all three in seconds, no simulation:

```bash
for f in */*.sv; do
  grep -q "logic w_sub_awready;" "$f" || continue
  n=$(grep -cE "\.(fub_axi_|s_axi_)awready\(w_sub_awready\)" "$f")
  [ "$n" -eq 1 ] || echo "DRIVERS=$n $f"      # 0 = undriven, 2 = multidriven
done
```

Requiring EXACTLY ONE driver catches the undriven case and the multidriven case
in the same sweep. A regression run costs five minutes and reports these as
`SystemExit`, which looks like a test failure rather than what it is.

*The rule: after changing a generator, enumerate the topologies it emits and
assert a structural invariant over ALL generated output before simulating.
The blast radius of a generator edit is every shape it can produce, not the
one you were looking at.* See [[feedback_confirm_scope_shared_rtl]] for the
same failure in hand-written shared RTL.

Related: [[filelists]] (the same one-source rule for compile closures);
the kimi-review-rounds rule 6 case in `vault/handbook/authoring/` — "fix the
source comment or the doc error regrows" is this note's rule applied to prose.

## `swmod` behind `peakrdl_to_cmdrsp` is a LEVEL, not a pulse

PeakRDL-regblock's `swmod` output is documented as "asserted when software
modifies the field". It is combinational on the cpuif request:
`decoded_reg_strb & req_is_wr`. Behind an interface that presents one request
per cycle that is a one-cycle pulse. Behind `peakrdl_to_cmdrsp` it is not:
the bridge HOLDS `regblk_req` from the accept cycle through `CMD_WAIT_ACK`
(its header says why -- shortening it once broke every register read through
the bridge), so every write presents to the regblock for TWO cycles and
`swmod` is a two-cycle level. The field storage itself loads at the end of
the first cycle, so it also lags the first `swmod` cycle by one.

Consumers that treat `swmod` as a pulse therefore execute their side effect
twice. That is invisible when the side effect is idempotent -- a W1C clear, a
counter load, a set or clear mask -- and fatal when it is not: a TOGGLE mask
applied twice cancels itself. *Case (2026-09-08, gpio #44): the strobe-driven
rewrite of GPIO_OUTPUT_TGL passed SET, SET-again and CLEAR and failed only
TOGGLE, `expected 0x0000FF0F, got 0x000000F0`. hpet consumes the same signal
as a level today and is correct only because both its uses are idempotent;
the pit_8254 round_3 review traced the same two-cycle request from the
counter-load side ("each COUNTERx_DATA write strobes TWICE").*

The shape that works, in the config_regs wrapper (never in the generated
file): rising-edge-detect the `swmod` level (one transaction, one pulse),
then delay the pulse ONE flop so it lines up with the field storage the
write landed in. Read the strobe's data from the field value in that aligned
cycle, or from `regblk_wr_data & regblk_wr_biten` in the level cycle if the
consumer needs the pre-storage value. The gpio wrapper
(`projects/components/retro_legacy_blocks/rtl/gpio/gpio_config_regs.sv`) is
the reference; its header explains the alignment.

Two things this rule is NOT: it is not a reason to shorten the bridge's
request (see the bridge header), and `singlepulse` is not the escape hatch
for a mask register -- SystemRDL restricts `singlepulse` to one-bit fields.

*The rule: a generated strobe's width is a property of the cpuif it sits
behind, not of the generator. Before consuming `swmod`, `swacc` or any
`decoded_reg_strb`-derived signal, read the bridge that drives `s_cpuif_req`
and count the cycles; if the side effect is not idempotent, edge-detect and
align.* Related: [[fsm-discipline]] (the converter's WAIT_ACK is the
state that makes the level), [[registers-by-name]].

## A protocol branch with no fixture in the batch is dead code

A generator can carry a code path for years without emitting it once. The
bridge generator had an AXI4-Lite *master* branch -- port emission, tie-off
defaults, the wide-slave aligner -- and a TB-template branch that drove APB
master ports through `master_apb[i].read/write`. No fixture in
`bridge_batch.csv` had a non-AXI4 master, so neither branch had ever been
generated, linted or simulated. When BRIDGE-014 added the first APB master
fixture the template's call went straight to `AttributeError`: the APB4
master BFM had no `read`/`write` at all (only the APB5 subclass did), and
nothing had ever asked.

The rule: every `protocol` value the validator accepts on a master port, and
every one it accepts on a slave port, must appear in at least one fixture in
the batch. The batch is the generator's regression; a branch outside it is
not tested by the 30 fixtures that pass, it is merely not exercised by them.
When adding a protocol value, add the fixture in the same commit and let the
`--bulk` regeneration, the lint sweep and the gate run be the proof.
