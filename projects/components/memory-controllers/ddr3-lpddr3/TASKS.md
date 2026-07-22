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

# ddr3-lpddr3 — Open Tasks

*Stub. To be populated as RTL work begins.*

## Advanced scheduling / refresh modes (see `../ADVANCED_MODES_ROADMAP.md`)

DDR3/LPDDR3 **inherits the DDR2/LPDDR2 commodity baseline** — all scheduling policies, all
page policies, REFab, JEDEC ±8 postpone/pull-in scheduling (config-bit-selectable, per the
pumice-ddr2-lpddr2 design-requirements "Advanced modes" section).

- [ ] **LPDDR3 per-bank refresh** (`refpb_rr`, REFpb round-robin) — the only per-bank
  scheme that is commodity at this tier; carry it forward from the LPDDR2 support.
- [ ] The DDR2-paper model-only modes (out-of-order per-bank refresh, write-refresh
  parallelization, refresh pausing, SARP/DSARP) are LPDDR4/DDR5 or research → assigned to
  `ddr4-lpddr4`, not here.

### [ ] RESEARCH — find DDR3/LPDDR3-specific new / exotic scheduling / paging / refresh mechanisms

DDR3 does not add controller-directed per-bank refresh, but the DDR3 era and DDR3-specific
device features (ZQ calibration, temperature-compensated refresh, self-refresh / power-down,
where Rowhammer was found) opened their own research space. **Survey the literature +
`/mnt/data/github/dfi-specs/ddr2-lpddr2/` papers**, extract each as a config-bit-selectable
mode (same methodology: OFF-by-default, faithful-DRAM-model red→green, commodity-legal vs
model-only split, `*_STATS` telemetry), and split commodity-legal-on-DDR3 vs model-only.
Seed candidates to evaluate (confirm DDR3/LPDDR3 applicability + commodity legality):

- **Retention-aware refresh — RAIDR** (Liu 2012, `.../ddr2-research/liu_2012_raidr_dram_refresh.pdf`): profile per-row retention, refresh weak rows at tREFI and strong rows far less often (Bloom-filter row bins). Needs retention profiling; the *scheduling* half (variable per-row/bin refresh interval) is controller-side.
- **Temperature-compensated / adaptive refresh (TCR)** — DDR3 devices expose temperature (MR / ASR auto-self-refresh); scale tREFI with temperature. Commodity-legal.
- **Elastic / adaptive refresh scheduling** — beyond the ±8 postpone: smooth refresh into idle windows using demand prediction. Commodity-legal.
- **Subarray-Level Parallelism — SALP** (Kim 2012): overlap accesses to different subarrays of the same bank. DRAM-microarch → **model-only** (candidate for ddr4 instead — evaluate).
- **ChargeCache** (Hassan 2016): track recently-closed rows and use their higher charge to shorten tRCD/tRAS for near-future reactivation. Controller-side row-address cache + a timing knob; **commodity-legal** in sim, board-legal only if the PHY lets tRCD be lowered per-command.
- **Rowhammer-aware targeted refresh / PARA** (Kim 2014): DDR3 is where Rowhammer was discovered — probabilistic adjacent-row refresh as a scheduling/refresh policy. Commodity-legal (extra refresh traffic).
- **Self-refresh / power-down entry-exit scheduling** — DDR3 precharge-/active-power-down + self-refresh; idle-timer-driven entry as a selectable power mode.
- **ZQ calibration scheduling** (DDR3 ZQCS/ZQCL) — periodic maintenance interleaved with demand traffic; a scheduling knob.

Deliverable: a `docs/design-requirements.md` "Advanced modes" section for `ddr3-lpddr3`
mirroring the pumice-ddr2-lpddr2 one (`../pumice-ddr2-lpddr2/docs/design-requirements.md`),
listing each confirmed mechanism with bullet detail +
its CSR mode/knobs + commodity-vs-model-only.
