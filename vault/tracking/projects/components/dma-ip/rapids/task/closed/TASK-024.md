# TASK-024: swappable network planes (AXIS / CXS) for both RAPIDS trees

**Priority:** P2
**Status:** closed 2026-10-15
**Owner:** sean galloway

Owner request (2026-10-15): CXS versions of the RAPIDS IP, made by replacing
the endpoint inside, with TSTRB carried in CXSUSER, and as separate "planes"
for CXS and AXIS so they can be swapped easily at the top level.

## Done

- The network endpoints moved out of `rapids_src`/`rapids_snk` (byte and beats)
  into `rtl/plane/rapids_plane_{axis,cxs}_{rx,tx}.sv`. All four planes share
  one parameter set and one inner interface. The plane monitor is client 1 of
  each half's monbus_arbiter, reached through `src_/snk_plane_mon_*`.
- `rtl/top/rapids_top_base.sv` and `rtl/top_beats/rapids_beats_top_base.sv` hold
  everything except the planes. `bin/gen_plane_tops.py` generates `rapids_top`,
  `rapids_cxs_top`, `rapids_beats_top` and `rapids_beats_cxs_top`, and `--check`
  reports a stale top. The AXIS tops keep their old interface exactly.
- The amba adapters `axis_to_cxs` and `cxs_to_axis` are in `rtl/amba/cxs/`.
- Found and fixed: `monbus_group_core` dropped every PROTOCOL_CXS packet.
  CXS packets now go through the AXIS mask slot. The formal model was updated:
  prove PASS, cover 19/19.
- Tests: `dv/tests/top/test_rapids_cxs_top.py` (6 cells) and
  `dv/tests/top_beats/test_rapids_beats_cxs_top.py` (4 cells). The TB is
  `dv/tbclasses/rapids_cxs_top_tb.py`. The core TBs check `check_plane_monbus`.
- Gate: RAPIDS all six areas 510/510 after clean-all; CXS suites FUNC 12/12
  (byte) and 8/8 (beats); val/amba monbus 29/29
  FUNC; both Genesys2 harness filelists lint clean.
- Docs: `docs/rapids_planes.md`, `docs/markdown/rtl-amba/cxs/axis_to_cxs.md`.

## Not in scope / follow-ups

- On the beats tree at FUNC, 16 one-beat egress packets back to back outrun
  the CXS lite's 4-entry queue: 12 completions are delivered and 4 reported
  dropped. That is the lite's documented drop-and-count contract, and the
  test checks the accounting. Raise the plane's OUT_DEPTH if every event matters.

- The HAS/MAS books still describe the endpoint inside rapids_src/snk.
- No CXS FPGA harness. CXS link options (parity, multi-packet flits) are fixed
  by the plane profile.
