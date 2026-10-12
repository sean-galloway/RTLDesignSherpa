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

# Doctrines Added by the Common-IP Campaign

The original five doctrines live in
[02_family_doctrine.md](../../02_family_doctrine.md) and remain in force;
they are not restated here. The Phase-2 campaign (2026-10-09 → 2026-10-10)
settled six more, recorded as doctrine 6 onward in the same shape: one rule,
its reason, and where it was learned.

## 6. Timing CSRs are cycle counts — frequency coupling is explicit

Every timing CSR in the family holds a count of MC-clock cycles, never
nanoseconds. Its correct value is a function of the MC clock frequency; a
frequency change invalidates the whole timing set at once, and software must
re-derive and reprogram it before traffic resumes. Stale values violate real
DRAM timings and present as data corruption, not errors.

**Reason.** pumice's own books carried timing registers "in cycles" without
ever saying what binds them to; the LiteDRAM `BUILD_CLK_HZ` reading 100 MHz
on a 75 MHz engine clock (2026-10-03 char results) is the same failure
operating in a shipping flow. Learned 2026-10-10; every HAS now carries the
warning at the register map, and this doctrine makes it family-wide.

## 7. Parameterize width, never personality

Build parameters express widths, depths, and counts — never behavioral
strategy. Runtime-selectable behavior is a CSR/config bit (doctrine 1);
strategy selection that would require illegal parameter cross-products is a
family boundary, not a parameter. The test, three parts: (a) all parameter
combinations must be legal; (b) a parameter changes the amount of
elaborated hardware, not runtime behavior; (c) DV cost stays linear in the
parameter, not per-product.

**Reason.** The refresh-controller divergences across the three rocks
({REFpb, Mode A/B/C, FGR, MPC, ZQCS}) fail (a) — the cross-products are
illegal — so generation features of refresh stay in thin rock children over
an extractable `mc_refresh_base`, per the two-customer rule. Page-policy
strategies pass (runtime `policy_mode` enum) but will split at ~4+
strategies. Learned from the scheduler-merge knob inventory
([mc_scheduler_knobs.md](../../mc_scheduler_knobs.md), 2026-10-10).

## 8. Safety is structure, policy is a CSR, and the two never mix

Safety-critical behavior is fixed RTL structure — no runtime bit may disable
it. Runtime-selectable policy (page policy, refresh mode, placement) is a
CSR. When a feature could be either, decide first which it is; if a runtime
bit could violate a DRAM or DFI safety limit, the bit is the defect.

**Reason.** The campaign's review of "which refresh features go behind
params" produced exactly three mechanisms — CSRs for policy, params/family
boundary for features, structure for safety — and the rule exists so the
question is asked once, at design time, not per pull request.

## 9. RAS features are discussed as needed — never enumerated ahead

The RAS plane (`mc_ras_plane`) is defined as a transform pair (ECC
insert/check) plus scrub-as-maintenance-client, with `HAS_ECC` ∈
{OFF, DETECT, CORRECT} and a reserved CSR surface. Beyond that, RAS features
are added only when a customer needs them, at which point the partner
decides. The skeleton is deliberately *not* a menu.

**Reason.** "Possible more features in the ras plane are controlled by
params. we will discuss as needed." (partner, 2026-10-10.) A plane whose
feature list is speculative is a plane nobody can validate; the transform
pair is the only RAS structure with two customers today.

## 10. The return path is its own contract — and perfect is the enemy of good

Read data returns on `mc_rd_return_ring` under its own ordering contract
(AXI-ID reorder); it does not ride the descriptor seam, and the seam's
symmetry goal must not absorb it. Unify the seams in a future revision if a
real customer appears; until then a separate, honest contract beats an
elegant one that is wrong.

**Reason.** The descriptor seam (Ch 2.2) is command-direction; forcing the
read-data reorder through it would couple every drop-in feature to AXI
ordering. Partner ruling, 2026-10-10: "never let the perfect get in the way
of the good."

## 11. A block with one customer stays rock-side

The two-customer rule, promoted from the common-ip README to doctrine: a
block moves to common-ip only when it has two live customers at extraction
time; speculative one-customer abstractions stay in the research controllers
no matter how clean the dedup looks.

**Reason.** Common-ip exists so features compose across controllers, not so
that code is written once. Every block in common-ip today met the rule at
extraction; every block still rock-side (init sequencer, mode register,
refresh personalities, page policy, power-down) is there because it has one
customer, and its extraction is a later campaign's decision, made when the
second customer exists.
