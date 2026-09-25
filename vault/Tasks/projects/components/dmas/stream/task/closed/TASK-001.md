# TASK-001: finish the STREAM workbook so its maps prove the decisions

> **Was `STREAM-KMAP` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-25. The five priority targets are discharged against
all four acceptance clauses, consistent with how [[PUMICE-KMAP]] was done.

**Scope, stated honestly:** the five targets are complete; the workbook as a
whole is NOT. `rtl_sop` went 1 -> 10 of 37 maps and `depends_only_on` 1 -> 8, so
**26 maps still render "VERDICT: NOT CHECKED"**. Those are the same shape of
work and now purely mechanical -- supply the RTL sum-of-products and the
sufficiency sentence -- but they are not done, and "the workbook is finished"
would be the overclaim this task exists to stop.

## What was actually missing

The entry's "meets only two of the six criteria" was ACCURATE, which I doubted
and had to correct. Measured before starting, across 35 computed maps: axis
triples 1, `depends_only_on` 1, `rtl_sop` 1, encoded don't-cares **0**. The
machinery all existed -- `_qm_minimize` (Quine-McCluskey with don't-care
absorption), the X/`DCFILL` rendering, the derived-vs-RTL verdict -- and was
simply never fed. Criteria 1 and 2 (computed from cited RTL, Gray-ordered) hold
universally; criteria 3-6 were the gap.

## The `relations=` port (TOOLING-KMAP item 0, discharged locally)

Stream's `kmap()` had no way to say why a cell is unreachable: `fn` had to
return `None` by hand, so an author's mistaken invariant silently deleted a real
case. Ported pumice's `relations=` -- `(text, reachable_predicate, citation)` --
which marks failing cells X and feeds them to the minimiser as don't-cares.

Added beyond pumice: the invariant is **CHECKED**. A predicate that excludes
nothing is a claim doing no work; one that excludes everything is inverted.
Both now fail the run. Proven by mutation in both directions before use. Full
hardware reachability is not decidable from the map, so what is checked is that
the claim bites -- and the docstring says exactly that rather than implying more.

Four unreachability claims already written in PROSE were converted to checked
predicates: `m_axi_wvalid` requires `r_w_active` (`WR_ENG:720`), the one-hot
scheduler FSM (`SCHED:228,:232`), the one-hot descriptor FSM (`DESC_ENG:726,
:753`), and the commit/issue ordering (`SCHED:907,:1005`). Each had been
rendering as a real 0 or 1 in a cell that cannot occur.

## The five targets

1. **Monitor cfg -> packet-class (`stream_core`).** COMPL emission mapped on
   four decomposed axes, each with its own equation and cite. Two axes
   resolving to one signal -- the original aliasing defect -- would be visible
   here by construction.
2. **`axi_write_engine` drain strobe / WLAST.** Axes DECOMPOSED: `m_axi_wvalid`
   is itself three terms (`WR_ENG:720-722`), and mapping it as one axis hides
   the registered-vs-combinational AND that fixes a separate defect, a 1-cycle
   dry window leaking stale data onto the bus.
3. **`descriptor_engine` prefetch + fifo_threshold.** `cfg_prefetch_enable` and
   `cfg_fifo_threshold` were DEAD; they now reach the cone only through
   `w_prefetch_limit`'s three-arm mux, and the axis list is what shows an axis
   no RTL drives.
4. **`scheduler` timeout/error latch and clear.** Records that "timeout" is
   OVERLOADED: this is the SCHEDULER timeout, and a bare window is recoverable
   and deliberately NOT latched -- only an escalated one is. Two mechanisms
   sharing a word is how the monitor's timeout went untested at this level.
5. **`stream_alloc_ctrl` / `stream_drain_ctrl` space accounting.** See the
   finding below -- this one did not come out as the task predicted.

## Three findings

**1. `use_mon` is redundant GIVEN the tie-off invariant.** Target 1's verdict
reads DIFFERS on purpose. The derived cover drops `use_mon`: the invariant
`USE_AXI_MONITORS=0 => int_cfg_*_compl_enable=0` (`CORE:869`) makes the four
`use_mon=0 && cfg_compl=1` cells unreachable, and Quine-McCluskey absorbs them.
Verified mechanically: those four X cells are exactly that set, and over the
reachable space the 3-term cover is equivalent to the RTL with no mismatching
cells. The term is worth keeping as defence in depth -- it makes a monitors-off
build independent of the CSR plumbing being right -- but if `CORE:869` were ever
removed it would stop being redundant and start being load-bearing. `rtl_sop`
was deliberately NOT tuned to force a green verdict.

**2. Target 5 is a CONTRACT, not a structural impossibility.** The task expected
don't-cares resting on "ordering guarantees elsewhere". The RTL provides none:
`rd_ptr` advances by the full `rd_size` gated only on `!rd_empty`
(`DRAIN:111`), so over-drain is REACHABLE and permanently corrupts the
occupancy. The only protection is a caller contract (the write engine's
`w_effective_avail` stale-view correction, `WR_ENG:366-383`) plus a
simulation-only `$error` inside `translate_off` (`DRAIN:171-181`). The map
therefore marks NOTHING unreachable -- zero X cells -- and says so.

**3. A default split across levels.** `stream_core.sv:202` defaults
`DATA_MON_ENABLE_COMPL_LOGIC` to `1'b0` while `stream_top_ch8.sv:111` defaults
`DESC_MON_ENABLE_COMPL_LOGIC` to `1'b1`. Same-named knob, opposite default,
one level apart. Not changed here -- flagged.

## Verification

- generator RC=0; **124 citations all resolve** (was 83); the gate greps every
  quoted snippet on every run.
- 10 sheets, unchanged count; the four contract sheets byte-stable at
  14/16/13/10 rows; growth confined to the five k-map sheets touched.
- Verdicts: 7 IDENTICAL, 1 DIFFERS (finding 1), 26 NOT CHECKED (the remaining
  scope above).
- The `relations=` port was proven output-NEUTRAL before any map used it: with
  zero callers, every sheet rendered identical row counts.

**Not done:** the 26 unchecked maps, and TOOLING-KMAP items 1-4 as *shared*
tooling -- the machinery added here lives in stream's generator, not `bin/`.
