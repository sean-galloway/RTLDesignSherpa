<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Formal Targets (Liveness and Safety)

**Status:** planned contract. Scope per amber D9: SymbiYosys at the tiny
16-set/2-way geometry, control-layer only. The tiny geometry is not a
limitation for these properties — set oversubscription (2 outstanding per
set at 2 ways) and MSHR-full (2+ entries at the tiny config) are reachable
exactly there.

## Liveness (the J5/J6 deadlock corner, proven)

1. **Oldest-entry progress.** The oldest valid MSHR entry eventually
   retires. (A fill once AR-accepted always completes; the commit pipeline
   always drains.)
2. **Drain progress.** A valid WB entry eventually BRESP-retires.
3. **Snoop progress.** A presented snoop is eventually granted, EXCEPT
   within the bounded anti-livelock window — whose bound is the fourth
   property:
4. **Bounded hold-off.** After an upgrade grant, snoop service to that
   line resumes within a fixed cycle bound (the granted write's commit).
5. **The composed corner.** MSHR-full ∧ WB-full ∧ snoop pending ⇒ some
   progress event (fill beat, commit, drain beat, BRESP, or snoop grant)
   within a fixed bound.

## Safety (inherited, re-run with MSHRs present)

- The `ap_grant_crresp`-class decode pins: CRRESP at grant equals the
  Table 3.0 decode at the resolved reference state (now with three answer
  sources: array / pending-fill / WB).
- BypassNeverAnswersInvalid, generalized per entry: a pending-fill answer
  is never at the Invalid row, and no CD beat is presented before its fill
  beat landed (PF_GUARD).
- No two valid MSHR entries share a line (merge, never duplicate fetch).
- No two in-flight misses in one set claim the same victim way (set
  oversubscription).
- Write-back ownership (jet BUG-005, 2026-11-25): the head's drain does
  not start while a snoop on the head is served from the WB buffer
  (`ap_wb_no_drain_in_svc`), and an entry a snoop passed on before its
  drain started never drains (`ap_wb_ended_never_drains`); covers
  `cp_wb_ended` and `cp_wb_passed_snoop`.

## What is deliberately not proven here

Full-cache proofs at 128-set/4-way (amber D9 scopes formal to the tiny
geometry; the FULL soak grid covers the large geometry dynamically), and
the fabric side (the pair fabric is amber's, already proven). jet's
fabric has one rule amber's lacks: two write-backs to one line in
presentation order (jet BUG-005). It is checked in simulation only, at the
cache ports (the pair rig's `_check_wb_order`); jet has no fabric proof
(jet-prime's `ap_wb_order` covers the same rule on its pipelined fabric).
Random traffic on jet never presents two same-line write-backs at once
(the requester's line buffer is busy until the absorption lands); the pair
rig's directed `WbSameLineOrder` scenario builds the case with a valve on
the memory's AW channel and fails with the hold removed (BUG-005).
