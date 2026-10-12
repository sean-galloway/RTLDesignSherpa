# TASK-011: val/math: cell-level coverage for prefix/compressor/subtractor cells

**Priority:** P3
**Status:** open
**Owner:** TBD

Cell-level math modules without a dedicated test root (found by the GTKW coverage audit, 2026-10-12):

- `math_prefix_cell`, `math_prefix_cell_gray` — prefix-tree cells (parents: the prefix adders, tested)
- `math_compressor_4to2` — compressor cell (parents: dadda/wallace trees, tested)
- `math_subtractor_full` — single-bit full subtractor (parents: subtractor_full_nbit etc., tested)

Also noted during the audit, NO task needed (covered as children of tested parents): the brent_kung subcells (`math_adder_brent_kung_bitwisepg/black/gray/grouppg_*/pg/sum`) and `math_multiplier_basic_cell`.

## Done when
- each listed cell has a directed unit test
