# Pumice LPDDR2 Docs Lane — close-out plan

Date: 2026-10-08

The pumice LPDDR2 training RTL (commit `0439f9d80`) and the rowhammer
generator RTL (commit `9ce4cd1da`) are committed, pushed, and FUB-tested.
This lane closes the documentation debt those commits opened, plus the
rowhammer driver recipe deferred from the approved rowhammer design.

Binding technical spec for all training-layer content:
`docs/superpowers/specs/2026-10-07-pumice-lpddr2-training-design.md`
(the spec is the authority; where this plan and the spec disagree, the
spec wins).

## Global Constraints

- Style/voice: follow `docs/kimi_humanization_style_guide_has_mas.md`
  exactly. No emoji anywhere.
- Version source of truth for each book is the ch00 `| Version |` row and
  the index `**Version:**` line; `generate_{has,mas}_pdf.sh` `REV=`
  default and the styles-yaml subtitle must match. After the task, no
  stale current-rev references may remain (grep to confirm).
- Artifact naming: `DDR2_LPDDR2_{HAS,MAS}_vX.Y.{pdf,docx}` in
  `projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/docs/` (the dir
  holding `generate_has_pdf.sh` / `generate_mas_pdf.sh`). Artifact
  retirement follows the scoria/andesite precedent: only the newest
  artifact set is kept — remove the superseded `v0.4`–`v0.6` pdf/docx
  pairs when the new set lands.
- Revision-history rows are dated 2026-10-08 and use the row format of
  the book they belong to (match sibling rows exactly).
- Structural precedent: the scoria and andesite HAS/MAS books already
  document their training layers — mirror their chapter/block-page
  structure, adapted to pumice DDR2/LPDDR2 facts. Do not invent a new
  layout.
- Multi-agent trunk: implementers MUST NOT run any git-mutating command
  (no add/commit/reset/rebase/checkout). Do not touch files outside the
  task's listed paths; other agents work in this tree concurrently.
  Untracked/dirty foreign files you see are not yours — leave them.
- Doc builds need pandoc + soffice + lualatex + Noto fonts. Verify with
  `command -v` before building. If a tool is missing, build what you can
  and report the gap — never fabricate an artifact.

## Task 1: pumice HAS rev 0.9 — training layer

Bring the pumice Hardware Architecture Specification to rev 0.9 so the
book matches the committed LPDDR2 training RTL.

Paths (all under `projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/docs/`):
book dir `pumice_has/`, build script `generate_has_pdf.sh`, styles yaml,
output artifacts in the docs dir root.

1. Read the spec (path above) and the committed RTL for facts:
   `../rtl/macro/pumice_training_layer.sv`, `../rtl/fub/pumice_zq_ctrl.sv`,
   `../rtl/fub/pumice_lp_cal.sv`, plus the scheduler-layer `trn_cmd`
   arbiter client, the cmd-FIFO MRR flag (format `{mrr, ap, col, row,
   bank, rank, op}`), the formatter MRR CA word (JESD209-2F §5.12,
   CA3r=H), and the rd_aligner cal-capture sideband. Also read
   `../rtl/top/pumice_csr.rdl` CSR block 0x0A0–0x0B8 (7 CSRs).
2. Bump the book to 0.9 everywhere the rev appears: index
   `**Version:**`, `generate_has_pdf.sh` `REV=` default, styles-yaml
   subtitle, and the ch00 `| Version |` row if present.
3. ch00 revision history: add the 0.9 row (2026-10-08) summarizing the
   training-layer content — ZQ calibration, LP calibration (digital
   drift compensation), MRR readout, the maintenance arbiter policy
   (init > refresh > trn > demand, all-banks-idle grant, `cal_busy`
   folded into `w_out_safe` per the BUG-003 fire==valid discipline).
4. Add the training-layer chapter content, mirroring how scoria's and
   andesite's HAS books document their training layers: block
   responsibilities, calibration flows, MRR path, arbitration policy,
   CSR summary, and the `pumice_core_tb_top.sv` tie-off note
   (training enables tied off in the core TB).
5. Build: from the docs dir, `./generate_has_pdf.sh --rev 0.9`. Confirm
   `DDR2_LPDDR2_HAS_v0.9.pdf` and `.docx` are produced and the build log
   is clean.
6. Retire superseded artifacts: remove `DDR2_LPDDR2_HAS_v0.4`–`v0.6`
   pdf/docx pairs.
7. Consistency sweep: grep the book for stale `0.4`/`0.8` current-rev
   references and fix any that denote the book's own current revision.

## Task 2: pumice MAS rev 0.8 — training blocks + contracts

Bring the pumice Micro-Architecture Specification to rev 0.8 with block
pages and contract rows for the training layer.

Paths: book dir `pumice_mas/`, `generate_mas_pdf.sh`, styles yaml,
artifacts in the docs dir root — same docs dir as Task 1.

1. Same fact sources as Task 1: the spec, the RTL, and
   `pumice_csr.rdl` (names + resets of the 7 CSRs at 0x0A0–0x0B8).
2. Bump the book to 0.8: index `**Version:**`, `generate_mas_pdf.sh`
   `REV=` default, styles-yaml subtitle, ch00 version row if present.
   ch00 revision history: add the 0.8 row (2026-10-08).
3. ch02: add block pages for `pumice_training_layer` (macro),
   `pumice_zq_ctrl` (fub), `pumice_lp_cal` (fub) — mirror the scoria /
   andesite MAS block-page template (purpose, parameters, interfaces,
   registers, behavior, verification pointers).
4. ch04 contracts: add rows for the new interfaces — MRR cmd-FIFO
   format `{mrr, ap, col, row, bank, rank, op}`, formatter MRR CA word,
   rd_aligner cal sideband, the `trn_cmd` arbiter priority
   (init > refresh > trn > demand), and the CSR map additions
   0x0A0–0x0B8 with names and reset values from the RDL.
5. Build: `./generate_mas_pdf.sh --rev 0.8`; confirm
   `DDR2_LPDDR2_MAS_v0.8.pdf` and `.docx`.
6. Retire superseded artifacts: remove `DDR2_LPDDR2_MAS_v0.4`–`v0.6`
   pdf/docx pairs.
7. Consistency sweep as in Task 1, for rev 0.8.

## Task 3: rowhammer methodology doc + driver recipe

Deliver the host-side half of the approved rowhammer design (the RTL
half shipped in `9ce4cd1da`).

Facts already committed (read them, do not re-derive):
`rtl/amba/shared/axi4_master_wr_pattern_gen.sv` and
`rtl/amba/shared/axi4_master_rd_crc_check.sv` — `cfg_hammer_en`
(address index = `count[0]`, ping-pongs base / base+stride_0 per txn),
2-bit `data_mode` (0=LFSR, 1=ADDR_HASH, 2=FILL with
`cfg_fill_pattern[31:0]`), rd-side `o_err_bits[31:0]` saturating
popcount. CSR: `projects/fpga-systems/rtl/mem_char_framework/rtl/chargen_regs.rdl`
field layout `data_mode[16:15]`, `hammer_en[17]`,
`max_outstanding[23:18]`, plus base/stride registers as they exist.

1. Methodology doc at
   `projects/fpga-systems/rtl/mem_char_framework/docs/rowhammer_methodology.md`:
   double-sided recipe (aggressor base = victim_row − 1, `stride_0` =
   2 × row_pitch, BL1, `hammer_en=1`, `data_mode=FILL` with
   `cfg_fill_pattern` = 0x00000000 / 0xFFFFFFFF on alternate aggressors),
   victim readback with `o_err_bits` popcount as the observable,
   refresh-window accounting (activations per tREFI, tREFW budget) and
   the tie to the deferred per-bank-refresh PARA work (TASK-009), a
   single-sided variant, and an explicit scope/safety note (DV and
   characterization methodology on owned hardware — not a production
   feature). Include the register-programming table.
2. `rowhammer()` recipe method in the mem_char_framework host driver —
   read `dv/` first (e.g. `chargen_driver.py`, `ddr2_char.py`) and match
   the existing driver API conventions. The method programs the recipe
   (base/stride/pattern/hammer_en), runs the hammer, reads the victim,
   and returns the `err_bits` summary. Keep it thin — the driver talks
   through the existing regmap accessors, no new register paths.
3. Tests: add a pytest for the recipe method beside the existing driver
   tests, run it. Env: `source venv-cocotb2/bin/activate` from the repo
   root, then `python -m pytest <path> -q`. Existing amba generator
   suites must still pass if you touch shared fixtures (run
   `python -m pytest val/amba/test_axi4_master_wr_pattern_gen.py val/amba/test_axi4_master_rd_crc_check.py val/amba/test_axi4_master_pat_crc_pair.py -q`).
