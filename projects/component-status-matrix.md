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

# Component Status Matrix

Point-in-time roll-up of every leaf component under `projects/components/`,
grouped by status: **IP** (active development) first, **NS** (not started)
next, **Done** (qualified) at the bottom.

**Evidence cut: 2026-10-11.** Update this file at milestones; it drifts by
design.

| Level | Meaning |
| --- | --- |
| **IP** | Active development toward qualification: README/PRD says draft/active, RTL is still landing, or the qualification campaign itself is in progress |
| **NS** | Scaffold only: README/PRD/spec with no RTL, or `.gitkeep` shells |
| **Done** | Qualified: RTL + DV + docs present, board validation or owner-confirmed 1.0. **Open issue-tracked follow-ups do not demote a Done component** — post-1.0 work is the normal steady state, not "in progress" (owner rule, 2026-10-11) |

## IP — active development

| Component | Evidence | Notes |
| --- | --- | --- |
| cache-ip/amber-mesi-l1 | PRD v0.6 draft (D3/D11 decided 2026-10-07); active RTL commits through 2026-10-10 | HAS v1.0 + MAS present; qualification not yet run |
| mem-ctrl-ip/common-ip | Phase-2 extraction landed 2026-10-10; 8 shared layers + 17 FUBs; absorbing wrapper dissolution | common HAS/MAS present; mid-extraction |
| mem-ctrl-ip/product-ip/granite-ddr2-lpddr2 | Scaffold README "not built"; vault TASK-001 (wrapper dissolution + product top) | pkg + filelist + config only |
| mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2 | README "implemented and characterized"; vault BUG-024 + TASK-042 open | Board-validated Nexys A7; LPDDR2 runtime ZQ pending |
| mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3 | README "verified in simulation; board work in progress"; vault TASK-006/007/008 open | HAS v0.8; 221 tests passing, 9 formal blocks; board campaign is the qualifier |
| fabric-gen-ip/delta | README "[PASS] Active Development"; generated RTL exists; DV suite TODO | PRD + perf models present; CocoTB suite not built; re-homed from noc-ip 2026-10-12 |

## NS — not started / scaffold only

| Component | Evidence | Notes |
| --- | --- | --- |
| cache-ip/basalt-moesi-l2 | README "pencil only"; PRD v0.1 all rows OPEN | Gated behind onyx v1 |
| cache-ip/jet-mesi-l1 | README "Scaffolded 2026-10-04 — README + PRD only"; placeholder rtl/dv/docs | Waits for amber |
| cache-ip/onyx-ace-ccu | README "Scaffolded 2026-10-05 — README + PRD only"; placeholder rtl/dv/docs | Waits for amber pair rig |
| compute-eng-ip | Area README only (2026-09-29); hive re-homed to riscv-ip | Empty area |
| dfx-ip/jtag-axil-agent | README "Scaffold (2026-10-11) — spec pending"; no RTL | Config-plane agent spec |
| dfx-ip/jtag-tap | README "Scaffold (2026-10-11) — spec pending"; no RTL | IEEE 1149.1 TAP spec |
| dfx-ip/riscv-debug | README "Scaffold (2026-10-11) — spec pending"; no RTL | DTM/DM spec |
| mem-ctrl-ip/product-ip/diorite-ddr4-lpddr4 | Scaffold "not built"; config doc only | v4 product placeholder |
| mem-ctrl-ip/product-ip/gabbro-ddr3-lpddr3 | Scaffold "not built"; config doc only | v3 product placeholder |
| mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4 | README "structure only — no HAS, no RTL" | v4 research placeholder |
| riscv-ip/garuda-rv32imaf | `.gitkeep` shells; area README "planned, structure only" | FP OoO rung placeholder |
| riscv-ip/gyrfalcon-rv32ima | `.gitkeep` shells; area README "planned, structure only" | OoO capstone placeholder |
| riscv-ip/hive-serv | PRD/CLAUDE v0.1 "early specification"; no RTL | SERV/VexRiscv control-cluster spec |
| riscv-ip/merlin-rv32i | `.gitkeep` shells; area README "planned, structure only" | 5-stage placeholder |
| riscv-ip/peregrine-rv32im | `.gitkeep` shells; area README "planned, structure only" | Advanced in-order placeholder |

## Done — qualified

| Component | Evidence | Notes |
| --- | --- | --- |
| dma-ip/rapids | Owner-confirmed Done 2026-10-11; byte-granular RTL + DV landed | PRD still says "validation in progress" — see note 1 |
| dma-ip/stream | Owner-confirmed Done 2026-10-11; README "95%"; HAS/MAS present; Genesys-2 campaign complete | README "final integration pending" — see note 1 |
| ecc-ip/bch | Owner-confirmed 1.0; Genesys-2 board validation complete | README doc revs still say v0.1 — see note 1 |
| ecc-ip/reed-solomon | Owner-confirmed 1.0; Genesys-2 board validation complete | README has stale "no RTL yet" line — see note 1 |
| fabric-gen-ip/lattice-apbx-xbar | README/PRD "Production Ready" v1.0; formal harnesses; 9/9 tests, >750 transactions | lattice HAS/MAS/GAS v1.2 |
| fabric-gen-ip/bridge | Owner-confirmed Done 2026-10-11; 1.0 + AXI3 support; HAS/MAS v1.9 | Follow-ups #98/#99 + TASK-014/015/016 tracked as issues — see note 2 |
| legacy-ip/retro_legacy_blocks | README "Version: 1.0", 10 shipped address windows | RLB TOP MAS v1.0 + per-block MAS |
| riscv-ip/kestrel-rv32i | rv32ui battery 42/42 spike lockstep; riscv-formal 42/42; doc book v0.1 | KESTREL HAS/MAS v0.1 |
| utility-ip/converters | README "Production Ready" v1.2; converter MAS v1.9; AXI3 suite landed | AxLOCK fix tracked as #98 — see note 2 |
| utility-ip/misc | README "Five complete utility modules" v1.2 | Includes the error injector |

## Notes

1. **README lag** — bch, reed-solomon, stream, and rapids are owner-confirmed
   Done, but their READMEs/PRDs still self-report draft/pending ("v0.1 doc
   revs", "no RTL yet", "95%, final integration pending", "validation in
   progress"). A README status pass on those four would bring the
   self-reports in line with the matrix.
2. **Post-1.0 follow-ups** — bridge (#98, #99, TASK-014/015/016) and
   converters (#98) carry open, issue-tracked follow-ups. Per the owner
   rule, tracked follow-ups on a qualified component do not demote its
   status; the issues are the tracking system working as intended.
3. **rapids-beats** — no longer a separate tree; retained inside rapids as
   the Genesys-2 stepping-stone configuration.

## Adjacent areas (not component leaves)

| Area | What it is | Status |
| --- | --- | --- |
| projects/asic-trials/timing_characterization | Portable timing-characterization harness (`char_top`) for per-technology delay budgets; v3.1, ASAP7 worked example, 45 tests | IP |
| projects/fpga-systems/ | Board validation harnesses: NexysA7, Genesys2 (dma/ecc/mem-ctrl), DE10-Standard fabric-benchmark (PRD v0.3) | IP |
