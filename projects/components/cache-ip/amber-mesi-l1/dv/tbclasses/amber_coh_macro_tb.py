"""amber_coh_macro testbench -- macro suite 4: coherence/snoop loop group

Task 9.5 macro composition: the PROMOTED Task 7 ad-hoc composition as a
named macro regression cell. The DUT is the wrapper amber_coh_macro_test
(REAL amber_control with the pending_fill_bypass / victim leaves +
landed tag/data/repl arrays + REAL amber_snoop_resp on the house
axi4ace_snoop_slave transport; fill/drain timing stubs per D-12) -- the
amber_snoop_resp_th wiring carried verbatim, so this class extends
AmberSnoopRespTB rather than rebuilding the suite:

  gate  -- table30_directed (one transaction per reachable HAS Table 3.0
           cell) + EWriteHitPromotes, the Task-7 found-and-fixed pin
           (HIT_WR E->M promotion one-hot, amber_control.sv:944)
  func  -- pool soak + zero-gap AC pairs (pipelining_zero_gap) +
           reset_recovery + SnoopVictimLineDuringGather +
           real_control_loop (randomized snoops against an amber
           simultaneously serving random CPU traffic: pending-fill
           bypass reference, staged-buffer service, stale-entry rule
           with the cross-set way+tag collision discrimination -- the
           sn_stale_gnt set-narrowing pin, amber_control.sv:531-535)
  full  -- deeper soak/loop at sign-off scale (6000 snoops / 1200 loop
           transactions), the T7 pins must stay green

The mid-transaction window handling, the ACEComplianceChecker per-
transaction compliance, and the concurrent-aware slice scorer are all
inherited; the geometry grid here varies SETS/WAYS (tiny 16/2 + default
128/4) with the responder bus/line at the pkg defaults, matching the
macro bring-up ladder convention.

Macro-scoped adaptations (the Task 7 suite itself is untouched):
  * directed-composition set selection falls back to a fixed set when
    the pool wraps the whole tiny-geometry set space (the compositions
    are set-content independent by construction);
  * the plain-transaction slice scorer's eviction accounting is
    reconciled after each call (see _reconcile_retired) -- at 2-way
    tiny geometry the set can hold a snoop-invalidate corpse of a line
    beside its live re-installed copy, and the control suite's
    unconditional retirement over-retires the line-level state where
    the loop scorer's _retire_line_at already applies the live-copy
    rule;
  * the real_control_loop 'oth'-snoop target selection excludes every
    resident of the transaction's set (see _pick_other_line) -- the
    inherited rule excludes the PLANNED victim only, but a mid-fill
    kill re-fetches through a RE-SELECTED victim chosen from the set's
    residents; snooping that line 'mid-drain' corrupts the model
    (content popped while the drain bookkeeping still needs it). The
    DUT handled the composition correctly (buffer service at M); this
    is the scoreboard's stability guarantee, widened to cover the
    re-fetch re-select the tiny geometry makes routine.

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import random

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_snoop_resp_tb import (
    AmberSnoopRespTB,
)


class AmberCohMacroTB(AmberSnoopRespTB):
    """Coherence/snoop loop macro: the promoted Task 7 closed loop.

    The superclass owns every scenario (this is the promotion, not a
    rebuild); the subclass carries the macro cell's identity on the
    bring-up ladder and the tiny-geometry model adaptations."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.log.info("AmberCohMacroTB: coherence/snoop loop group "
                      "(promoted Task 7 composition: control + snoop_resp "
                      "+ pending_fill_bypass + victim)")

    def _macro_set(self, pool_addrs):
        """Set selection for the directed compositions: the Task 7
        discipline wants a set the pool never touched, which exists at
        128 sets but not when the pool wraps the whole tiny geometry's
        set space. The compositions themselves are set-content
        independent (their own installs make the composition line the
        eldest), so fall back to a fixed set when nothing is free."""
        pool_sets = {(a >> self.OFFSET_BITS) & self.SET_MASK
                     for a in pool_addrs}
        if len(pool_sets) < self.SETS:
            return next(s for s in range(self.SETS) if s not in pool_sets)
        return 0

    # ------------------------------------------------------------------
    # Task-7 found-and-fixed pin (HIT_WR promotion one-hot): the parent
    # body is geometry-safe except for the _free_set assumption; reuse
    # it with the macro set selection by temporarily overriding the
    # allocator the parent's helper consults.
    # ------------------------------------------------------------------
    async def _e_write_hit_promotes(self):
        orig = self._free_set
        self._free_set = lambda _used: self._macro_set(
            [0x1000 + i * self.LINE_BYTES for i in range(24)])
        try:
            await super()._e_write_hit_promotes()
        finally:
            self._free_set = orig

    async def _snoop_victim_during_gather(self):
        orig = self._free_set
        self._free_set = lambda _used: self._macro_set(
            [0x2000 + i * self.LINE_BYTES for i in range(64)])
        try:
            await super()._snoop_victim_during_gather()
        finally:
            self._free_set = orig

    # ------------------------------------------------------------------
    # Eviction-accounting reconciliation (tiny-geometry adaptation).
    #
    # The control suite's _score_slice retires a victim slot's old line
    # UNCONDITIONALLY (self.line_state[evicted] = 'I'). That is sound
    # only while a line never has two slot claims in one set. The snoop
    # service leaves {tag, I} corpses in place, and a refill can re-
    # install the same line at the OTHER way; the set then holds a
    # corpse beside a live copy (routine at 2-way tiny geometry where
    # the pool wraps four sets). Evicting the corpse must NOT retire
    # the line -- the DUT/array keep the live copy. The loop scorer
    # already retires through _retire_line_at, which checks for other
    # live copies; the plain-transaction scorer predates that rule.
    # Rather than perturb the landed suites, the macro reconciles the
    # txn's set after each plain scoring: any line the accounting
    # retired to 'I' that still has a LIVE slot copy in the model (the
    # tap-maintained slot view is exactly what the DUT array holds) gets
    # its line-level state re-derived from that copy. Only the
    # over-retired signature is repaired -- every other drift class
    # still scores as a loud mismatch.
    # ------------------------------------------------------------------
    def _score_slice(self, addr, line, set_idx, beat, we, be, wdata, res,
                     rsp_data, sl, label):
        super()._score_slice(addr, line, set_idx, beat, we, be, wdata, res,
                             rsp_data, sl, label)
        self._reconcile_retired(set_idx)

    def _reconcile_retired(self, set_idx):
        for w in range(self.WAYS):
            dead = self.tags.get((set_idx, w))
            if dead is None or self.line_state.get(dead, 'I') != 'I':
                continue
            for w2 in range(self.WAYS):
                if (self.tags.get((set_idx, w2)) == dead
                        and self.slot_state.get((set_idx, w2), 'I') != 'I'):
                    self.line_state[dead] = self.slot_state[(set_idx, w2)]
                    self.log.info(
                        f"reconcile: line {dead:#x} over-retired by plain "
                        f"eviction accounting; live copy at set {set_idx} "
                        f"way {w2} -> {self.line_state[dead]}")
                    break

    # ------------------------------------------------------------------
    # oth-snoop target selection (re-fetch re-select adaptation).
    #
    # The inherited contract: an 'oth' target is "installed, not the
    # txn line, not the victim slot; stable across the whole in-flight
    # window". The victim slot exclusion names the PLANNED victim, read
    # before the request is accepted. That is sufficient only while the
    # victim at gather equals the victim at plan time -- true at 128
    # sets for the suite's native churn, but at 2-way tiny geometry a
    # mid-fill kill re-fetches, and the re-fetch's victim is RE-SELECTED
    # from the transaction's set (the killed commit left a fresh corpse
    # that changed the repl ranking). Any set-mate can therefore become
    # the actual victim; an 'oth' snoop on one hits the draining-victim
    # composition the scoreboard does not model (the model pops the
    # line's content at the invalidate while the drain bookkeeping
    # still needs it -> KeyError). The DUT serves the snoop correctly
    # from the staged buffer (SINK_WB_ACK); the widening here keeps the
    # SCOREBOARD's stability guarantee honest. Residents of the txn's
    # set are excluded; a guaranteed-absent fresh line remains the
    # fallback (an I-line snoop is still a full ACE transaction).
    # ------------------------------------------------------------------
    def _pick_other_line(self, line, victim_line, seen_lines):
        set_idx = self._set_of_line(line)
        residents = {self.tags.get((set_idx, w)) for w in range(self.WAYS)}
        residents.discard(None)
        cands = [l for l in dict.fromkeys(seen_lines)
                 if l != line and l != victim_line
                 and l not in residents
                 and self.line_state.get(l, 'I') != 'I']
        if cands:
            return random.choice(cands)
        fresh = (random.randrange(1, 1 << 8) << self.SET_BITS) \
            | random.randrange(self.SETS)
        if fresh != line and fresh != victim_line and fresh not in residents:
            return fresh
        return None
