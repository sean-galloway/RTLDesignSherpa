# ISSUE-001: riscv-ip FPGA microarchitecture review

> Source: owner, 2026-11-18: "I recently had the cache-ip and mem-ctrl-ip
> checked for fpga optimization. Can you do the same for riscv-ip?" Scope: every
> riscv-ip directory with RTL (common-rv32i, kestrel, merlin, gatling), built out
> of context on the Nexys A7 part (xc7a100t-1) at 100 MHz.

**Priority:** P2. The big structures are already FPGA-shaped. The findings are
area (13-27% of each core) and merlin's 100 MHz timing.
**Status:** OPEN (2026-11-18)
**Owner:** TBD
**Report:** [assets/issue001_fpga_uarch/00_FPGA_UARCH_REVIEW.md](../../assets/issue001_fpga_uarch/00_FPGA_UARCH_REVIEW.md).
It holds the method, every measured number, the ALU equivalence check and the
reproducing script.

## Measured anchors (OOC, routed, 10 ns)

| Block | LUT | FF (FDCE) | WNS |
|---|---|---|---|
| kestrel_core | 1,149 | 100 (97) | +0.388 |
| merlin_core | 1,583 | 814 (811) | -0.141 |
| gatling_core | 1,538 | 897 (409) | +0.464 |
| rv32i_alu, in each core | 374 | 0 | |

## Rows

| # | Area | Finding | Effect | State |
|---|---|---|---|---|
| 1 | common-rv32i | ALU builds three barrel shifters and a second 33-bit compare | variant measured: -306 / -205 / -231 LUT (kestrel / merlin / gatling), kestrel WNS +0.85 ns; 2,001,280-vector equivalence, 0 mismatches | done: common-rv32i [TASK-001](../../task/closed/TASK-001.md), suites + riscv-formal green |
| 2 | merlin | pipeline registers reset and flush the whole payload | FDCE 811 -> 134; x0-init and load-use reads fixed; suite 54/54, riscv-formal 42/42 | done: merlin-rv32i [TASK-003](../../../merlin-rv32i/task/closed/TASK-003.md) |
| 3 | merlin | forwarding compare -> branch -> redirect / flush fan-out is the critical path (11-15 levels) | (a) done with row 2 in merlin-rv32i TASK-003: 1,378 -> 1,262 LUT, WNS over 3 placer directives -0.216..+0.227 -> +0.065..+0.241; path now load data -> forward -> branch | (a) done; (b) register the redirect = owner decision |
| 4 | gatling | per-context PC / cause / halt in async-reset flops with loop write and mux read | PC file -> 22 LUTRAM: 1,308 -> 1,200 LUT, 894 -> 772 FF, WNS over 3 placer directives +0.190..+0.470 -> +0.424..+0.660; cause / halt stay flops (the ports show every context at once) | done: gatling-rv32i [TASK-004](../../../gatling-rv32i/task/closed/TASK-004.md) |
| 5 | all | RVFI-only state (gatling order_q 256 FF, merlin ~256 carried FF, kestrel retire_count) | trimmed on the board; costs only where RVFI is consumed | no-action |
| 6 | kestrel/gatling mem | gaxi_skid_buffer W channel 2-4 LUT per flop | shared rtl/amba IP; memory systems have 3-3.7 ns slack | no-action here |
| 7 | kestrel | board runs 75 MHz (single-cycle by design) | row 1 may lift it; needs a board build | open, after row 1 |

The issue resolves when each open row is a task in its own area (common-rv32i,
merlin-rv32i, gatling-rv32i, kestrel-rv32i) or is closed on a measurement.
