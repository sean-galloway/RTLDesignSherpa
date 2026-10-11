# TASK-017: Implement arbiter_matrix_weighted — weighted matrix arbiter for rtl/common

**Status:** CLOSED 2026-10-11 (commit `db58ccffa`)
**Priority:** P2

Add a weighted matrix arbiter to the `rtl/common` arbiter family. The design extends `arbiter_matrix` with per-client credit counters so that the priority matrix rotates only after the current winner has consumed its full weight in grants.

## Definition of done

- [x] RTL: `rtl/common/arbiter_matrix_weighted.sv`
- [x] Filelist: `rtl/common/filelists/arbiter_matrix_weighted.f`
- [x] Testbench class: `bin/TBClasses/common/arbiter_matrix_weighted_tb.py`
- [x] Test runner: `val/common/test_arbiter_matrix_weighted.py`
- [x] Test plan: `val/common/testplans/arbiter_matrix_weighted_testplan.md`
- [x] Documentation: `docs/markdown/rtl-common/arbiter_matrix_weighted.md`
- [x] Index updates: `docs/markdown/rtl-common/index.md`, `rtl/common/CLAUDE.md`
- [x] Area master filelist: `rtl/common/filelists/common_all.f`
- [x] Formal wrapper: `formal/common/arbiter_matrix_weighted/`
- [x] Vault task filed and closed with resolution
- [x] Lint clean (`make -C rtl/common verible` / declaration-order check)
- [x] Tests pass (`TEST_LEVEL=func pytest val/common/test_arbiter_matrix_weighted.py -q`)
- [x] Committed with explicit pathspec (feat + task-close)

## Resolution

Implemented in `db58ccffa`. The key RTL fix was driving the registered no-ACK grant from the post-rotation matrix (`w_grant_next_*` computed from `w_matrix_next_no_ack`) instead of the current matrix, preventing the winner from receiving one extra grant after its credits were exhausted. Functional, GATE, and FULL regression sweeps pass; Verible and declaration-order checks are clean.

## Notes

Design follows Dally & Towles, *Principles and Practices of Interconnection Networks*, ch. 17 §18.5 (matrix arbiter) and §18.4.4 (weighted arbiters). Weight semantics mirror `arbiter_round_robin_weighted`: per-client down-counters, weight=0 disables the client, and weight changes take effect at the next credit reload.
