# TASK-030: generate_*_pdf.sh REPO_ROOT depth bug — sweep remaining scripts

**Priority:** P3
**Status:** OPEN
**Owner:** tooling
**Filed:** 2026-10-11 during bridge citations work (commit e0be98508 + script fix)

## What happened

`bridge/docs/generate_{has,mas}_pdf.sh` computed
`REPO_ROOT="${SCRIPT_DIR}/../../../.."` — one level short for their
`projects/components/fabric-gen-ip/bridge/docs` location, resolving to
`<repo>/projects` instead of the repo root. Any invocation relying on
`${REPO_ROOT}/bin/...` (e.g. `md_to_docx.py`) failed. Both bridge scripts
fixed 2026-10-11 (five `..` segments) and the HAS regeneration verified.

## Scope

Same `SCRIPT_DIR}/../../../.."` pattern exists in six more scripts; depth
analysis says all are wrong for their locations:

- `projects/components/fabric-gen-ip/apbx-xbar/docs/generate_{has,mas}_pdf.sh`
  (same 5-deep layout as bridge — one level short)
- `projects/asic-trials/timing_characterization/docs/generate_{wp_fpga_pdf,wp_pdf,synthesis_guide_pdf,has,mas}_pdf.sh`
  (3-deep layout — four `..` segments overshoot above the repo root)

## What to do

1. For each script, compute the correct depth from its actual location (or,
   better, resolve upward by searching for the `bin/md_to_docx.py` anchor so
   the scripts stop hardcoding depth at all).
2. Verify each fixed script by regenerating its PDF from the correct CWD
   (these scripts use CWD-relative paths internally — run from their `docs/`
   dir).
3. Note the CWD convention in each script's `--help` text if not already
   stated.

## Done when

- [ ] all eight generate scripts resolve repo-root tools correctly
- [ ] at least one regeneration per area (bridge done; apbx-xbar,
      timing_characterization) verified

**Progress 2026-10-12:** apbx-xbar pair fixed (4 `..` -> 5 `..` in both
`generate_has_pdf.sh` and `generate_mas_pdf.sh`) as part of the fabric-gen-ip
docs batch (docs-review TASK-016); verified by successful v1.1 builds.
Remainder: timing_characterization (4 scripts) still open.
