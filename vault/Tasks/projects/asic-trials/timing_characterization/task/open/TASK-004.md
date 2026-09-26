# TASK-004: PDF Generation for Synthesis Guide

> Migrated 2026-09-25 from
> `projects/asic-trials/timing_characterization/TASKS.md` as **TASK-004**
> (tooling TOOL-001), ID unchanged. That checklist recorded "9 task blocks";
> the file actually held FOUR. Classified against the tree, not the Status line.


**Confirmed still open 2026-09-25.** `docs/` carries four generators
(`generate_has_pdf.sh`, `generate_mas_pdf.sh`, `generate_wp_pdf.sh`,
`generate_wp_fpga_pdf.sh`) and four built PDFs, none from `SYNTHESIS_GUIDE.md`,
which lives at `rtl/syn/SYNTHESIS_GUIDE.md`.

**Status:** Planned

> Status (2026-07-22): the project now has styled PDF generation via
> `docs/generate_has_pdf.sh`, `docs/generate_mas_pdf.sh`, and
> `docs/generate_wp_pdf.sh` (HAS/MAS/white-paper); a `docs/generate_pdf.sh`
> for SYNTHESIS_GUIDE.md specifically has still not been created.
**Priority:** P3 (Low)
**Effort:** 0.5 day

**Description:**
Add markdown-to-PDF generation script for SYNTHESIS_GUIDE.md, following
the pattern used by bridge and stream components.

**Acceptance Criteria:**
- [ ] `docs/generate_pdf.sh` script
- [ ] Clean PDF output from SYNTHESIS_GUIDE.md
- [ ] No emoji issues in LaTeX pipeline

**Files:**
- `docs/generate_pdf.sh` (to be created)

---
