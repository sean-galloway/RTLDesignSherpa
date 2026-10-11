# TASK-017: Implement arbiter_matrix_weighted — weighted matrix arbiter for rtl/common

**Status:** active
**Priority:** P2

Add a weighted matrix arbiter to the `rtl/common` arbiter family. The design extends `arbiter_matrix` with per-client credit counters so that the priority matrix rotates only after the current winner has consumed its full weight in grants.

## Definition of done

- [ ] RTL: `rtl/common/arbiter_matrix_weighted.sv`
- [ ] Filelist: `rtl/common/filelists/arbiter_matrix_weighted.f`
- [ ] Testbench class: `bin/TBClasses/common/arbiter_matrix_weighted_tb.py`
- [ ] Test runner: `val/common/test_arbiter_matrix_weighted.py`
- [ ] Test plan: `val/common/testplans/arbiter_matrix_weighted_testplan.md`
- [ ] Documentation: `docs/markdown/rtl-common/arbiter_matrix_weighted.md`
- [ ] Index updates: `docs/markdown/rtl-common/index.md`, `rtl/common/CLAUDE.md`
- [ ] Area master filelist: `rtl/common/filelists/common_all.f`
- [ ] Formal wrapper: `formal/common/arbiter_matrix_weighted/`
- [ ] Vault task filed and closed with resolution
- [ ] Lint clean (`make -C rtl/common verible` / declaration-order check)
- [ ] Tests pass (`TEST_LEVEL=func pytest val/common/test_arbiter_matrix_weighted.py -q`)
- [ ] Committed with explicit pathspec (feat + task-close)

## Notes

Design follows Dally & Towles, *Principles and Practices of Interconnection Networks*, ch. 17 §18.5 (matrix arbiter) and §18.4.4 (weighted arbiters). Weight semantics mirror `arbiter_round_robin_weighted`: per-client down-counters, weight=0 disables the client, and weight changes take effect at the next credit reload.
