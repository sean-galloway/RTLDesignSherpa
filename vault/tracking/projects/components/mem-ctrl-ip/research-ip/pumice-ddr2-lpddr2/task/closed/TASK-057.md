# TASK-057: the harness host drives granite through granite's regmap; bank-queue depth 4 and 6 measured

> Source: owner, 2026-10-24, on the list closing TASK-056: "Do 1/3 for now.
> For the bank fifos see the perf impact if they are 6 or 4 deep." Related:
> TASK-056 (granite's CSR is a strict subset of pumice's since then), TASK-050
> (the first depth-4 measurement, on the position-array store), handbook
> `design/per-bank-queues-admit-from-the-pool.md`.

**Priority:** P2
**Status:** closed 2026-10-24 (host selects the controller's regmap, granite flow identical on granite's own map; depth 6 = -4 percent 8-thread writes / +8 percent mixed, depth 4 = the TASK-050 loss again; pool-deep stays the default)
**Owner:** TBD

## What landed

- **`DDR2CharDriver(controller="pumice" | "granite")`** (`build-perf/host/
  ddr2_char.py`): the driver used to load pumice's regmap for whichever
  controller sat behind the harness, which only worked because granite's map
  was pumice's. `CONTROLLER_REGMAPS` maps the name to the generated regmap
  (granite's is `regs/generated/granite_csr_regmap.py`); the device attribute
  stays `drv.pumice` because every method on it is by-name and
  controller-agnostic, but the names that resolve and the reset values the
  shadow assumes are the selected controller's. The granite proxy and the
  granite UART test select `"granite"`.
- **`Device.has(reg)`** (`bin/TBClasses/harness/device.py`): membership in the
  regmap, so a caller programming an optional block asks instead of catching
  the `ValueError` a by-name access raises.
- **`REF_CTRL` guard** in `pumice_char.py`'s config `apply()`: the one write
  in the shared flow to a register granite does not have. The default (no
  refresh elasticity asked for) is simply not written; a config that asks for
  `refresh=` on a controller without the register raises with the controller
  named. The telemetry readers were already wrapped (`_try_page_stats`,
  `_try_stall_stats`).

## Measured

**Bank-queue depth.** Since TASK-054 the per-bank queues are linked lists
through the slots, so `BANK_FIFO_DEPTH` caps by count and buys no area at
any value: this is purely the bandwidth question. Against the committed
defaults (pool-deep, 8), board geometry, mismatched 0 everywhere:

| cell (wr / rd MB/s) | pool-deep (default, 8) | depth 6 | depth 4 |
|---|---|---|---|
| 1 thread incremental | 568.2 / 569.6 | 567.2 / 570.1 | 563.6 / 568.0 |
| 1 thread row_major | 576.5 / 574.4 | identical | identical |
| 1 thread col_ilv | 460.8 / 452.5 | 460.5 / 454.0 | **384.6 / 417.4** |
| 1 thread col_major | 311.1 / 358.5 | identical | identical |
| 8 threads incremental | 556.9 / 557.4 | **534.6 / 556.9** | **429.4 / 475.6** |
| 8 threads row_major | 557.6 / 557.5 | **535.3 / 557.5** | **429.0 / 476.3** |
| 8 threads col_ilv | 533.5 / 543.8 | 508.8 / 534.3 | 414.2 / 458.0 |
| 8 threads col_major | 459.7 / 458.5 | 461.9 / 458.4 | 386.4 / 421.1 |
| mixed, 8 threads (union) | 98.1 | **106.5** | 65.7 |

Depth 4 is the TASK-050 result again, now on the linked-list store with the
lean intakes: 23 percent off the eight-thread writes, 15 off the reads, 17
off one-thread col_ilv, and mixed down a third (it completes now; on the
position-array store it deadlocked). At BL4 x16 one 8-beat burst is eight
same-bank entries, so a cap of four blocks the single in-order address
channel half way through every burst, for every bank behind it. Depth 6 is
the interesting point: one-thread streams within a few cycles of pool-deep,
eight-thread writes 4 percent down (the cap bites once per burst instead of
twice), reads untouched, and **mixed 8 percent UP** -- with two threads per
bank, a cap keeps one bank's writes from taking every pool slot, which is
the fairness the pool-deep rule gives away. Since TASK-054 the cap buys no
area (the queues are lists through the slots, there is no position storage
to size), so it is a pure policy knob: pool-deep stays granite's default on
the streams the eight-injector requirement is written for, and 6 is the
setting to reach for when concurrent read / write per bank is the workload.
The right fix for mixed is not a cap but a per-direction share of the pool;
that is a design item, not a knob.

**Granite regmap.** The granite proxy on granite's map is cycle-identical to the committed grid at 1 and 8 threads and on mixed, the granite UART smoke test passes, and no register-lookup error appears in any log (the telemetry readers fall back to "no telemetry" through their try / except). The pumice proxy on the shared host (default controller) is cycle-identical to pumice's 2026-10-23 grid at one thread, which also confirms that today's shared-RTL knobs left pumice's bandwidth untouched.

## Gates

Granite UART smoke test 1 / 1 on granite's regmap; granite proxy on
granite's regmap cycle-identical at 1 and 8 threads and on mixed; depth 4
and 6 lanes 5 / 5 cells each, mismatched 0; pumice proxy std_n1 on the shared host cycle-identical to pumice's grid; py_compile on the
driver, the shared host, the device helper and both granite tests;
task-tracker check PASS. No RTL changed in this task, so no lint, build or
suite is owed.
