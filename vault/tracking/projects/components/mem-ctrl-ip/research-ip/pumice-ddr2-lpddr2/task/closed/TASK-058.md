# TASK-058: granite store fairness lever (conditional per-bank cap), pick-core tRFC counters, board bring-up of the day's text

> Source: owner, 2026-10-24, on the list closing TASK-057: "Do 1/2/3 please"
> -- 1 the per-direction pool share in the store that TASK-057 named as the
> real mixed fix, 2 the pick-core arbitration cones, 3 board bring-up of the
> day's text on the Nexys A7. Related: TASK-057 (depth 6 = +8 percent mixed,
> -4 percent streams), TASK-056 (pick payload by array index), handbook
> `design/per-bank-queues-admit-from-the-pool.md`.

**Priority:** P2
**Status:** closed 2026-10-24 (conditional cap 6 is granite's default: every stream cell cycle-identical, mixed 98.1 -> 106.5 MB/s, no area; tRFC / tZQCS counters 8 bits, -51 cells / -8 flops, cycle-identical; the rest of the pick core is the arbiter itself; board: BUG-031 found, root-caused to a double driver in mc_rd_intake, fixed, flow gate added, leveled smoke + 128 MB memtest + char PASS; board LUT/FF since TASK-054 corrected)
**Owner:** TBD

## What landed

- **`BANK_CAP_MIXED`** (`mc_bank_fifo_store.sv`, granite default 6, store
  default 0 = off): a per-bank queue cap that applies ONLY while the other
  direction holds any entry. `aw_push_ready` / `ar_push_ready` /
  `rd_cam_ins_ready` gain one term each: `(cap == 0) || !any_other_dir ||
  (count[bank] < cap)`. A direction streaming alone keeps pool-deep queues
  (the eight-injector streams are untouched); with both directions present
  no bank may hold more than six of one direction's eight slots, which is
  the share TASK-057's flat cap bought at the cost of the streams. Plumbed
  through `granite_core` / `granite_top_geared` / the char macro, harness,
  UART TB top, both tests (`GRANITE_BANK_CAP_MIXED`), the proxy
  (`TEST_BANK_CAP_MIXED`) and both `create_project.tcl` knob lists.
- **`RFC_W`** (`mc_bank_pick.sv`, through `mc_scheduler_plane`, granite
  default 8): the tRFC and tZQCS recovery counters were 16 bits because the
  CSR fields are; DDR2 tRFC at <= 100 MHz is 35 cycles. `sat_rfc()` clamps
  a CSR value above the counter's range to its maximum (conservative).
- **`run_smoke.py --controller {pumice,granite}`**: the board smoke runner
  passes the controller to `DDR2CharDriver` (TASK-057's regmap selection),
  so the granite bitstream is driven through granite's own map on silicon.

## Measured

**Store cap** (proxy, board geometry, 75 MHz, mismatched 0 everywhere; the
grid is the TASK-054 defaults):

| cell (wr / rd MB/s) | pool-deep | flat cap 6 (TASK-057) | conditional cap 6 |
|---|---|---|---|
| 1 thread, 4 families | 568.2 / 569.6 .. 311.1 / 358.5 | within a few cycles | **identical** (4 / 4 cells) |
| 8 threads incremental | 556.9 / 557.4 | 534.6 / 556.9 | **identical** |
| 8 threads row_major | 557.6 / 557.5 | 535.3 / 557.5 | **identical** |
| 8 threads col_ilv | 533.5 / 543.8 | 508.8 / 534.3 | **identical** |
| 8 threads col_major | 459.7 / 458.5 | 461.9 / 458.4 | **identical** |
| mixed, 8 threads (union) | 98.1 | 106.5 | **106.5** (184 550 vs 200 290 write cycles) |

The hypothesis from TASK-057 held exactly: the cap's whole benefit is the
share it denies a bank when the other direction is waiting, and its whole
cost was binding on a lone stream. Conditioned on the other direction's
presence it keeps the gain and loses the cost, so 6 is the default. Area:
ASAP7 store 6 342 -> 6 317 comb cells at the same 806 flops (a cap-off
variant of the same text came out 6 599, so the term is inside this flow's
abc noise band, about 2 percent on a 6k-cell block).

**Pick core.** ASAP7, the planes-kept flow on `granite_top_geared`:
`u_bank_pick` 2 543 comb / 216 flops -> 2 492 / 208 with the 8-bit
counters (standalone 2 811 -> 2 798 cells); cycle-identical at 1 and 8
threads and on mixed. The rest is the arbiter function: the pre-abc
attribution puts about 1 500 cells in the per-pair request / class decode
(`r_req`, `r_cls`, `w_spec`, `w_hint`, `r_stale`) and the class-priority
select (`w_sel`, `w_pick`), the remainder in the fire-stage payload muxes
TASK-056 already reduced. There is no further dead width in it; the next
cut would change what the arbiter computes (fewer classes, or no age
promotion), which is a policy decision with a bandwidth measurement
attached, not an area item.

**Whole core, ASAP7** (`granite_top_geared`, planes kept, dead bits
pruned): 21 155 comb / 3 842 flops at TASK-056 -> 21 055 / 3 834 with both
defaults. Scheduler plane 7 546 comb (page policy 2 516, pick 2 492, bank
timers 1 823, global timers 399, refresh 188), store 6 317, AXI plane
3 848, CSR 2 156, DFI plane 852, init 242.

**Board, Nexys A7-100T.** The day's text does not read on silicon, and had
not since TASK-054: `init` PASS in 0.7 s, every write at rate, no read of any
length ever returning a beat (pumice **BUG-031**). The host, harness and PHY
were cleared with the 2026-10-23 pumice bitstream; the read-FIFO depth, the
same-clock crossing, the AXI depths, snarf and the store backend were cleared
by knob builds; strict rddata_en-anchored PHY timing in sim passed at the
board tuple. A commit bisect in detached worktrees (each built and probed with
its own host) put the boundary inside TASK-054, and splitting that commit put
it in the AXI plane / intakes, not the store. Root cause: `mc_rd_intake` drove
`map_req_o` twice (a common assign and the `HAS_ADDR_MAP` branch's constant
zero). Legal Verilog, lint-clean in Verilator, dead in the board
configuration; Vivado reported `Synth 8-6859`, had merged the net with the AR
skid's valid, and tied it to GND. Fix: one driver per generate branch;
`make bitstream` / `make synth` now fail on that message (it was in every
build log since TASK-054, four times, and in none before). Fixed text on the
board: leveled init PASS, `write_read` PASS mismatched 0, **128 MB memtest
PASS 32 / 32 chunks**; char: PASS, smoke profile at txn_scale 1000, bl8, open_page (the shipping
default): incremental **rd 577.8 / wr 576.0 MB/s**, col_major 333.0 / 291.8
(peak 600 at 75 MHz x 64 bits); the proxy's single-thread incremental cell
on the same text is 569.6 / 568.2. bank_interleave 192.8 / 193.0,
close_page and inorder 74.6 / 59.8 (the reference corners). The board
measures the design the proxy measured, on the first granite silicon run
since 2026-10-12.

**Correction to the TASK-054..057 board figures.** With the AR valid grounded,
synthesis folded the read side of the store, the return ring and the intake
away, so every granite_core LUT / FF quoted since TASK-054 measured a design
without its read path. Honest board trend, same flow:

| text | granite_core LUT | FF | WNS |
|---|---|---|---|
| before TASK-050 (5.10 baseline) | 9 956 | 5 160 | +0.106 |
| TASK-053 (last text that read on silicon) | 6 090 | 4 417 | +0.367 |
| TASK-054 .. TASK-057 as reported | 4 171 .. 3 939 | 2 709 .. 2 567 | (dead read path) |
| **today, fixed** | **5 631** | **3 532** | +0.134 |

The day's real saving on the board is 459 LUT / 885 FF, not 2 150 / 1 850.
Every bandwidth and cycle claim stands: the net was dead in simulation, so
the proxy and the suites measured the real design. The ASAP7 numbers move
only in the read intake (1 045 -> 1 210 cells, 231 -> 296 flops): the
planes-kept flow could not fold across the kept hierarchy the way Vivado's
flattening did. The rule, in the handbook: a board utilization is a
measurement only after that bitstream has passed the board smoke.

**Final build** (today's text, cap 6 + `RFC_W` 8, the intake fixed): 5 631
LUT / 3 532 FF, WNS +0.134 ns, 0 failing endpoints, 0 multi-driven reports.

## Gates

After the intake fix: Verilator lint on `granite_top_geared` unchanged (3
pre-existing warnings); granite UART smoke 1 / 1; granite suite 6 / 1 xfail;
granite proxy std_n1 cycle-identical to the grid; pumice `run-all-func-both`
218 + 218 passed; fixed board build 0 multi-driven reports, WNS +0.134;
Nexys A7 leveled init + write_read + 128 MB memtest PASS, char below.

Before the fix (unchanged by it, the net being dead in sim):

Contract battery 12 / 3 xfail; granite suite 6 / 1 xfail at the TASK-057
defaults, at `BANK_CAP_MIXED=6` and at the final defaults (clean-all
each); pumice `run-all-func-both` 32 + 218 + 218 passed (the shared store
and pick changed; pumice's CAM store does not instantiate the cap);
proxy lanes `rfc8` and `cap6` 5 / 5 cells each, mismatched 0, compared
cycle-for-cycle to the committed grid; Verilator lint on
`granite_top_geared` through its filelist adds nothing (the three
remaining warnings predate today); board smoke, memtest and char above;
task-tracker check PASS.
