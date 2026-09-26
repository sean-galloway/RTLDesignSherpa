# TASK-002: Cross-Technology Comparison Reports

> Migrated 2026-09-25 from
> `projects/asic-trials/timing_characterization/TASKS.md` as **TASK-002**
> (tooling TOOL-001), ID unchanged. That checklist recorded "9 task blocks";
> the file actually held FOUR. Classified against the tree, not the Status line.


**Confirmed still open 2026-09-25.** `docs/baseline_results.md` does not
exist. The only cross-technology artifact is a mermaid diagram
(`docs/timing_char_has/assets/mermaid/synthesis_cross_tech.*`), which is a
picture, not swept results.

**Status:** Planned
**Priority:** P2 (Standard)
**Effort:** 1 day

**Description:**
Run baseline synthesis sweeps on available targets and document results in
`docs/` with comparison tables.

**Acceptance Criteria:**
- [ ] At least two FPGA targets compared (e.g., Artix-7 vs. UltraScale+)
- [ ] Carry chain width sweep results
- [ ] NAND depth sweep results
- [ ] DSP vs. LUT multiplier comparison
- [ ] Results documented in markdown tables

**Files:**
- `docs/baseline_results.md` (to be created)

---
