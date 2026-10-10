# TASK-026: board validation: WRITE TARGET MET (570 MB/s), READ CEILING FOUND

> **Migrated from `PUMICE-022`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-022` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** closed 2026-09-10 — measured on silicon; read shortfall re-filed as PUMICE-025

Nexys A7 (210292BFA3EE), 75 MHz / DDR2-300, base-tier bitstream at
3c66f442d. Peak is 600 MB/s (75 MHz x 8 B).

**Integrity first:** a7 read leveling found a clean eye (bitslip 0, tap 4,
width 10); 32 MB memtest 8/8 chunks clean, 0 dirty; every characterization
point passed its integrity check (12/12, then 13/13, then 32/32). So the
whole 2026-09-08/09 body of work -- read return ring, write-lead block, JEDEC
timings, restored paging modes, base-build order modes, pre-pick muxing --
is data-clean on hardware.

**Bandwidth, best config (`open_page` and equivalents, row_major BL8):**

| Direction | Measured | Target | Peak | Result |
|---|---|---|---|---|
| Write | **570.0 MB/s** | 510 | 600 | **MET** (95.0% of peak) |
| Read | **291.7 MB/s** | 450 | 600 | missed (48.6% of peak) |

> **CORRECTED 2026-09-10.** The first pass reported `refresh_credit` at
> 574.0/292.2 as the best config. That was an ARTIFACT of run order, not a
> result. `pumice_char.ControllerConfig.apply()` only programmed a mode axis
> when the preset set it, so a preset that left `page_mode` unset inherited
> the previous config's. `refresh_credit` is a CLOSE-page preset and ran
> straight after `rbl_dyn`, inheriting `page_mode=7`, whose predictor kept the
> page open. Standalone it measures 33.8/35.8, which is the correct
> close-page number. apply() now programs every axis on every config
> (0 = build default) so nothing is inherited; the re-run is 36/36
> integrity-clean and order-independent.

For scale: this path measured 12.7 MB/s flat on 2026-07-08 and ~2% of peak.
Writes are now essentially at the data-path limit.

**The read ceiling is structural, not a tuning problem.** Read bandwidth is
291.7-292.2 MB/s and read latency 49.2 cycles in EVERY configuration that
streams at all, and it does not move with:
- burst length -- bl4 290.8, bl8 291.7, bl16 291.7 (identical). This rules out
  an outstanding-transaction or Little's-law limit: more bytes per transaction
  would raise it.
- access pattern -- incremental, row_major identical.
- paging mode -- open_page, adapt_time, adapt_access, rbl_dyn all 291.7.
- scheduling -- age_threshold identical to FR-FCFS.

48.7% of peak, invariant to everything above the return path, is the signature
of a return path that moves one AXI beat every other cycle while the write path
moves one per cycle. Re-filed as PUMICE-025 with this evidence.

**Mode characterization (row_major BL8, MB/s write/read):**

Re-measured order-independently, 36/36 integrity:

| Config | Write | Read | Note |
|---|---|---|---|
| `open_page` | 570.0 | 291.7 | the ceiling; four configs tie here |
| `age_thr` | 570.0 | 291.7 | starvation bound is FREE |
| `adapt_time` | 570.0 | 291.7 | |
| `adapt_access` | 570.0 | 291.7 | predictor holds the page open |
| `rbl_dyn` | 570.0 | 291.7 | **hill-climb works on silicon** |
| `rbl_static` | 33.8 | 36.9 | miss_thresh=2 too aggressive for streaming |
| `inorder` | 33.8 | 35.8 | 16x cost, as sim predicted |
| `refresh_credit` | 33.8 | 35.8 | CLOSE-page; credits do not rescue close-page |
| `baseline` | 33.8 | 35.8 | CLOSE-page reference |

The split is binary: anything that keeps the page open reaches 570/291.7,
anything that closes per access sits at ~34/36. Nothing lands in between,
which is what a command-bus-bound design looks like -- see the BL4 note in
PUMICE-025.

Two results worth keeping:
- **rbl_dyn vindicates the dynamic threshold.** `rbl_static` at the same base
  miss threshold collapses to 33.8 MB/s because it closes pages on a streaming
  pattern; `rbl_dyn`'s per-epoch hill-climb backs the threshold off and
  recovers full bandwidth. That is precisely the "lesser-known alternative
  that wins in a specific situation" the mode work exists to demonstrate, and
  it only shows on real traffic.
- **age_threshold is free.** Same bandwidth as plain FR-FCFS, so the
  starvation bound costs nothing until it engages. It is the mode to reach for
  when in_order is being considered for latency reasons -- in_order costs 17x
  on this pattern.
