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

**Evidence cut: 2026-10-11.** Status derives from open GitHub issues, open
vault tasks, README/PRD status lines, doc maturity, and commit recency — not
from intent. Update this file at milestones; it drifts by design.

| Level | Meaning |
| --- | --- |
| **IP** | Active development: open issues/tasks, or README/PRD says draft/active, or landing commits within ~2 weeks |
| **NS** | Scaffold only: README/PRD/spec with no RTL, or `.gitkeep` shells |
| **Done** | Qualified: RTL + DV + docs present, no open issues or vault tasks, board validation or README completion statement |

## IP — active development

| Component | Evidence | Notes |
| --- | --- | --- |
| cache-ip/amber-mesi-l1 | PRD v0.6 draft (D3/D11 decided 2026-10-07); active RTL commits through 2026-10-10; no open issues/tasks | HAS v1.0 + MAS present; PRD still labels itself draft |
| dma-ip/rapids | PRD "Active Development — Validation in Progress"; daily commits through 2026-10-10; active known_issues note | Byte-granular product RTL active; `*_beats` retained as Genesys-2 stepping stone |
| dma-ip/stream | README "Nearly Complete — 95% Done" / "Final Integration Pending"; fix commit 2026-10-10; no open issues/tasks | Owner previously listed it at 1.0; README disagrees — see note 2 |
| fabric-gen-ip/bridge | Open GH #98 (converter AxLOCK), #99 (TB BFM template + test debt); vault TASK-014/015/016; AXI3 landed 2026-10-11 | Reached 1.0 + AXI3; open follow-ups keep it active — see note 3 |
| mem-ctrl-ip/common-ip | Phase-2 extraction landed 2026-10-10; 8 shared layers + 17 FUBs; absorbing wrapper dissolution | common HAS/MAS present |
| mem-ctrl-ip/product-ip/granite-ddr2-lpddr2 | Scaffold README "not built"; vault TASK-001 (wrapper dissolution + product top) | pkg + filelist + config only |
| mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2 | README "implemented and characterized"; vault BUG-024 + TASK-042; board-validated Nexys A7 | HAS/MAS v0.5; LPDDR2 runtime ZQ pending |
| mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3 | README "verified in simulation; board work in progress"; vault TASK-006/007/008 | HAS v0.8; 221 tests passing, 9 formal blocks |
| noc-ip/delta | README "[PASS] Active Development"; generated RTL exists; DV suite TODO | PRD + perf models present; CocoTB suite not built |
| utility-ip/converters | Open GH #98 (AXI3 AxLOCK encoding swap); README "Production Ready" v1.2 | Converter MAS v1.9; functional AXI3-path bug keeps it active |

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
| ecc-ip/bch | RTL + dv + docs landed; Genesys-2 board validation complete; no open issues/tasks | Owner-confirmed 1.0; README doc revs still say v0.1 — see note 1 |
| ecc-ip/reed-solomon | Encoder/decoder cores + GF layer in rtl/; Genesys-2 board validation complete; no open issues/tasks | Owner-confirmed 1.0; README has stale "no RTL yet" line — see note 1 |
| fabric-gen-ip/apbx-xbar | README/PRD "Production Ready" v1.0; formal harnesses; 9/9 tests, >750 transactions | apbx HAS/MAS |
| retro_legacy_blocks | README "Version: 1.0", 10 shipped address windows; no open issues/tasks | RLB TOP MAS v1.0 + per-block MAS |
| riscv-ip/kestrel-rv32i | rv32ui battery 42/42 spike lockstep; riscv-formal 42/42; doc book v0.1 | KESTREL HAS/MAS v0.1 |
| utility-ip/misc | README "Five complete utility modules" v1.2; no open issues/tasks | Includes the error injector |

## Notes and flagged reconciliations

1. **bch / reed-solomon** — classified Done on owner confirmation (1.0)
   plus completed Genesys-2 board validation and zero open work. Their
   READMEs lag reality: bch still labels PRD/HAS/MAS as v0.1 and RS
   carries a stale "no RTL yet" line. A README/doc-rev pass would remove
   the confusion; the rows flip back to IP if any of that surfaces open
   work.
2. **stream / rapids** — previously named at 1.0 by the owner, but their
   own README/PRD say "95%, final integration pending" and "validation in
   progress", and stream took a fix commit yesterday. Left at IP until
   the owner's label and the components' self-reports agree; flip either
   way once they do.
3. **bridge** — reached 1.0 and took AXI3 support on 2026-10-11; kept at
   IP purely for the open, actively-tracked follow-ups (#98, #99,
   TASK-014/015/016). Post-1.0 issue-tracked evolution is the agreed
   model, so this row flips to Done when the follow-ups close.
4. **rapids-beats** — no longer a separate tree; retained inside rapids as
   the Genesys-2 stepping-stone configuration.

## Adjacent areas (not component leaves)

| Area | What it is | Status |
| --- | --- | --- |
| projects/asic-trials/timing_characterization | Portable timing-characterization harness (`char_top`) for per-technology delay budgets; v3.1, ASAP7 worked example, 45 tests | IP |
| projects/fpga-systems/ | Board validation harnesses: NexysA7, Genesys2 (dma/ecc/mem-ctrl), DE10-Standard fabric-benchmark (PRD v0.3) | IP |
