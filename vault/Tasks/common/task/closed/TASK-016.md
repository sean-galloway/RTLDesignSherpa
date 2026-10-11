# TASK-016: Implement arbiter_matrix — matrix fair arbiter for rtl/common

**Status:** CLOSED 2026-10-11 (commit `6628c4b02`)
**Priority:** P2

Add a matrix (rotation-in-distributed-state) fair arbiter to the `rtl/common` arbiter family, following the conventions of `arbiter_round_robin` for ports, reset style, filelists, tests, and documentation.

## Definition of done

- [x] RTL: `rtl/common/arbiter_matrix.sv`
- [x] Filelist: `rtl/common/filelists/arbiter_matrix.f`
- [x] Testbench class: `bin/TBClasses/common/arbiter_matrix_tb.py`
- [x] Test runner: `val/common/test_arbiter_matrix.py`
- [x] Documentation: `docs/markdown/rtl-common/arbiter_matrix.md`
- [x] Index updates: `docs/markdown/rtl-common/index.md`, `rtl/common/CLAUDE.md`
- [x] Area master filelist: `rtl/common/filelists/common_all.f`
- [x] Lint clean (`make -C rtl/common verible` / declaration-order check)
- [x] Tests pass (`TEST_LEVEL=func pytest val/common/test_arbiter_matrix.py -q`)
- [x] Committed with explicit pathspec and task moved to closed

## Notes

Design follows Dally & Towles, *Principles and Practices of Interconnection Networks*, ch. 17 §18.5: grant `g[i] = req[i] & ~∃j(req[j] & M[j][i])`, update on grant to `k` clears row `k` and sets column `k`. Stores only the `N(N-1)/2` upper-triangle bits of the matrix.
