<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Active (in progress)

---

## PUMICE-001 — Runtime-config axes corrupt data (board + sim)
**Status:** active 2026-07-23 — two RTL fixes landed, board re-validation pending. Issue #42.

**Fixes landed 2026-07-23 (commit fab57682):**
- `pumice_cmd_arbiter`: auto-precharge column guard. Under CLOSE the xDA
  precharges the bank as part of the access, but the generic guard deliberately
  does not gate columns against columns and `r_bank_row_active` is a cycle
  stale, so the next entry on the same bank+row still saw "row active" and
  issued a second column into a bank already committed to precharge. On the
  DRAM that column has no open row and the access lands wherever the device
  last had one (batch-2 row-1 writes landed on row 0, clobbering batch 1 —
  64 beats / 48 unique). Guards the bank for 2 cycles after a fired AP column,
  exactly as `r_guard0/1` do for ACT/PRE. No-op under OPEN/HYBRID.
- `pumice_top`: `REFRESH_TUNING.page_policy_or` carries the SOFTWARE encoding
  (0=build default, 1=OPEN, 2=CLOSE, 3=HYBRID) while `page_policy_e` is
  OPEN=0/CLOSE=1/HYBRID=2. The raw cast made software-OPEN run CLOSE and
  software-CLOSE run HYBRID — the entire open_page/reorder config-axis
  corruption keyed off this.

Verified: `pumice_cmd_arbiter` FUB passes on a clean build; macro+top 54 passed
(the 1 failure is PUMICE-002, pre-existing).

**Still open:** board re-run of the config-axis families on a rebuilt bitstream.

**Board baseline (2026-07-22, first rearch config-axis run):** baseline/inorder
9/14 (col_major fails only at scale 1000); bank_interleave / open_page /
reorder 0/14. multiid showed 7 EXTRA read returns (hist 64007 != 64000) —
suspect rd-CAM duplicate issue under reorder. Correctness at the baseline
config is SOLID (soak gate green); these are the runtime
page-policy/scheme/reorder paths.

Full map + signatures:
`projects/NexysA7/ddr2-characterization/char_results/FINDINGS_pumice_board_2026-07-22.md`
(+ `char_2026-07-22_wrapup.csv`). Tools: CMD_HISTORY_EN checker,
dfi_rd_return_checker, ILA flow.

**Sim repro available:** `test_ddr2_char_char_families` fails the
bank_interleave family over the DFI loopback — the config-axis defect is
digital and wave-debuggable in sim; start there, no board required.
See PUMICE-003, same class.
