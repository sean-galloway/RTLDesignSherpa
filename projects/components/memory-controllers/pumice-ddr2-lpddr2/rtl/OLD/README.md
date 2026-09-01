# Set aside, not deleted

## pumice_rbl_table.sv, pumice_row_pred_table.sv (2026-09-01)

The Axis-2 paging predictors behind `PAGE_POLICY_CFG.policy_mode` 5 / 6 / 7:

| mode | name | table |
|---|---|---|
| 5 | `adapt_access` | `pumice_row_pred_table` — tagless direct-mapped 2-bit saturating counters, {bank, XOR-folded row} index |
| 6 | `rbl_static` | `pumice_rbl_table` — set-associative row miss-counter, tag = row, true-LRU |
| 7 | `rbl_dyn` | as 6, plus a divider-free per-epoch threshold hill-climb |

**Why they are here.** They did not fit the timing budget on the Nexys A7. On
the first synthesis since PUMICE-006 landed, these two instances were **60% of
all failing endpoints** (`u_rbl` 1546, `u_row_pred` 1049 of 4307) with a
single-generator harness in front of them -- so the harness was not the cause
and shrinking it did not help.

Their cost is not storage. The tables are tiny: 1280 and 1024 bits, together
12.5% of ONE BRAM18 on a part with 135 of them. The area is the PARALLEL ACCESS
logic -- rbl compares a 14-bit tag across 4 ways and updates a true-LRU on
every lookup; row_pred initialises all 512 entries in a single cycle. That is
why BRAM was not the answer either.

**They are functionally correct and mutation-proven.** Every mode was directed-
tested and each verdict forced to prove the test went RED. Nothing here is
broken; it is a design that does not fit this part at this frequency.

**What this costs.** [[PUMICE-013]] wanted these characterized ON SILICON, and
that is no longer possible in this build. Modes 5/6/7 now decode to the default
(no auto-precharge). Modes 0-4 are unaffected. The sim-side directed tests
(`test_pumice_core_rbl`, `test_pumice_core_acc`) go with them.

**Restoring:** `git mv` the two files back to `rtl/fub/`, restore the two
instantiations in `pumice_page_policy.sv` and the entries in
`rtl/filelists/fub/`. The CSR field is unchanged, so nothing in software or the
register map has to move.
