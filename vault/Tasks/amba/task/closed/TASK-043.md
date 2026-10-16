# TASK-043: CXS family (Arm IHI 0079, Issues A-D) -- RTL, filelists, tests, docs

**Priority:** P2
**Status:** closed 2026-10-15
**Owner:** Sean

`rtl/amba/cxs/`: `cxs_master`, `cxs_slave`, `cxs_master_cg`, `cxs_slave_cg`,
plus `cxs_pkg` (CXSCNTL layout, per-issue legality `config_error`),
`cxs_cntl_track`, `cxs_odd_byte_parity`. One parameterised family for every
issue -- each issue is a strict superset, so `CXS_ISSUE` selects the legal
property set and elaboration stops with a rule number on an illegal one.
Filelists `rtl/amba/filelists/cxs_*.f` and `amba_all.f`.

Verification: RDS-DV `components/cxs` BFMs (CXS-001 there), TB classes
`bin/TBClasses/cxs/`, runners `val/amba/test_cxs_{master,slave}[_cg].py`.
GATE 15/15, FUNC 40/40, FULL 58/58. Six RTL mutations killed (send without
a credit, no credit return, grant past the pool, ACK drop with credits out,
CXSDATACHK ignored, deactivation mid-packet).

Found and fixed on the way: the receiver's ACTIVEREQ synchronizer reset its
check bit to 0, so the pair read as a parity error for the flush cycles after
every reset (check bit now crosses inverted); `gaxi_fifo_sync` cannot be
built 1 deep, so a one-credit receiver floors its FIFO at 2.

Docs: `docs/markdown/rtl-amba/cxs/` (README + 4 module pages), book
`docs/pdfs/RTL_AMBA_CXS.pdf`. Follow-up: amba TASK-044 (`_monlite`).
