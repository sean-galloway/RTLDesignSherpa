# PUMICE-023: the char-framework sim is the board gate and must run before any pumice RTL commit

**Status:** open 2026-09-08  **Priority:** P1

`ddr2_char_framework/dv/tests` (test_ddr2_char_uart + test_ddr2_char_char) is
the only suite that builds the board's x16 / strict-timing configuration. The
arbiter fix passed all 213 pumice fub/macro/top tests and failed 7 there
(write side, fixed by the write-staged gate). Its Makefile `run-all-*` targets
were being swallowed by the `run-%` pattern into a nonexistent test id, so the
area had silently stopped gating; aliases added 2026-09-08. Pre-existing
failures to triage: `smoke_rate2_faithful`, `smoke_rate2_rdphase1`,
`smoke_rate2_strict`, `pagehit_rate2_x16_free_earlyen` (all fail at
79fb58a66, before this session). Add this directory to the pumice regression
convention (`regressions` skill) and to the components master Makefile.
