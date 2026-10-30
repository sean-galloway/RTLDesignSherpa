# TASK-050: CHI monitor-lite: chi_monitor_lite, the two _monlite wrappers, decoder, tests, docs

**Priority:** P2
**Status:** active 2026-10-30
**Owner:** sean galloway

Owner 2026-10-30, after TASK-049 landed: "is there an ocelus monitor-lite for
chi similar to the ones for cxs/axi4/ace?" and, on the answer that CHI
cannot reuse either core: "my 'similar' comment is in relation to it being
lean and gate count efficient." The CHI Ocelus in the lite discipline, built
on the axi_monitor_lite recipe (stamps not counters, one retire per cycle, a
scan pointer for timeouts, no per-slot FSM, no CAM).

## Scope

- rtl/amba/includes/ocelus_chi_pkg.sv: the PROTOCOL_CHI (4'h7) event codes;
  PROTOCOL_CHI added to ocelus_common_pkg. chi_pkg gains the Size, ExpCompAck,
  RespErr, DBID and PCrdType offsets, the opcode constants the monitor
  decodes, is_read_opcode and data_packets.
- rtl/amba/ocelus/chi_monitor_lite.sv: request slots keyed by TxnID (toward
  the requester) and DBID (from it), four debts per slot, a snoop table,
  link / credit / backpressure episodes from the CXS lite, 22 candidates
  into the lite's two-pick, two-bank queue and drop report.
- rtl/amba/chi/chi_{rnf,hnf}_port_monlite.sv generated from the ports
  (verbatim parameters and ports); filelists for all.
- bin/TBClasses/monbus: CHI*Code enums + lookup, test_monbus_chi.py parity.
- val/amba/monitor-lite/test_chi_{rnf,hnf}_port_monlite.py over
  bin/TBClasses/chi/chi_monlite_tb.py; GATE/FUNC/FULL, mutation checks.
- docs/markdown/rtl-amba/monitor/chi_monitor_lite.md, wrappers page Table 5,
  book and index rows, rtl/amba/CLAUDE.md.

## Not in scope (follow-ups)

- (Done 2026-10-30 on the owner's instruction: both group cores filter by
  `ocelus_common_pkg::filter_family()`, no hard drop; CHI takes the stream
  masks, APB/ARB/WB the AXI masks.)
- A formal harness (axis_monitor_lite has one; this block has sim only).
- _monlite_cg wrappers (clock gating is FPGA-only here, as for CXS).

## Done (2026-10-30, uncommitted, awaiting the owner's commit call)

- RTL: ocelus_chi_pkg.sv, chi_monitor_lite.sv, chi_{rnf,hnf}_port_monlite.sv
  (generated), 4 filelists, registry PASS; lint clean on 6 parameter sets
  including N=1/M=1/OUT_DEPTH=1, AGE_WIDTH 8, DATA_WIDTH 512, NODEID 11,
  USE_MONITOR=0.
- Review (rds-rtl-review against IHI 0050 H) found 7 HIGH tracking holes
  before any test ran: TxnID reuse before DBID-keyed debts (B2.5), Comp not
  capturing the DBID (B2.4.3), Comp before DBIDResp, PrefetchTgt, the Zero
  writes, SnpDVMOp's two flits, two snoops retiring in one cycle; plus
  CompStashDone/CompPersist, late ReadReceipt, AGE_WIDTH slice, clear not
  re-stamping episodes. All fixed; lesson in handbook
  design/transaction-monitor-keys.md.
- Tests: val/amba/monitor-lite/test_chi_{rnf,hnf}_port_monlite.py over
  bin/TBClasses/chi/chi_monlite_{tb,common,model}.py. Clean build: GATE 6/6,
  FUNC 16/16, FULL 26/26 (13 cells per wrapper incl. USE_MONITOR=0); counted
  verdict (FULL dw128: 848 packets checked, 448 TXN, 14 SNP, 60 RETRY, every
  error/timeout/credit/channel/stream class non-zero, 20 drops reported).
  Three mutations red/green. Base port tests still green.
- Cost (yosys generic synth): 1,912 flops / 13,925 cells / 49,135 NAND2 vs
  the CXS lite's 850 / 5,685 / 20,133; about 40 percent of a default RN-F port.
- Docs: monitor/chi_monitor_lite.md, wrappers page Table 5, book + index
  rows, rtl/amba/CLAUDE.md; Python CHI*Code enums + parity test.
- Not stimulated by the BFMs (RTL present, untested): plain Comp on a
  CopyBack write, the Zero writes, SnpDVMOp shared slot, double snoop retire.
