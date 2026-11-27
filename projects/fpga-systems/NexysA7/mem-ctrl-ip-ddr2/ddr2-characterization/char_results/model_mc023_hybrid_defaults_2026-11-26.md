# MC-023 item 4 closed: the refresh drain and `behind_lag` are the SKU defaults

> memory-controllers MC-023, 2026-11-26. Follows
> `model_mc023_hybrid_behind_lag_2026-11-25.md`. Three changes landed before the
> comparison could be trusted, then the model's default moved.
> Proxy: `test_granite_char_perf`, 100 MHz, `TEST_DUAL=1`, 4 generators,
> `mixed` bl8, TXN 8000, tREFI 780, `TEST_REF_ALIGN`, the SKU build
> (`TEST_STORE_MERGE_EN=0`, read path 6 / 6, strict read timing).

## 1. The RTL's refresh period was tREFI + 1 (d36ee4882)

`mc_xddr2_refresh_ctrl` (and the scoria / andesite copies) reloaded the
interval and expired at 0. A CSR value of N refreshed every N + 1 cycles, so
the model at 780 was being compared with an RTL at 781. The counter now
reloads N - 1 (0 stays 0).

## 2. The proxy's pre-pass ended on a wall clock (9dc43c4ae)

The mixed family writes the read region in an untimed pre-pass, with the perf
meters frozen. `wait_engine` extends its deadline on the write meter, so it saw
no progress, and every pre-pass ended on its bare 120 s wall-clock bound
(`prepass_ok` false on nearly every record). In simulation that bound falls at
a cycle that depends on machine load:

- Usually it fell after the pre-pass. The bus then idled 29k .. 69k cycles
  before GO, a different amount each run.
- Once, on a loaded machine at offset 0, it fell at 207,232 of 256,000 writes,
  and the record read 1482 / 582.

`TEST_REF_ALIGN` reloads the refresh counter at launch, but not the pending
refresh state the idle gap leaves behind. So the per-offset modes of every
earlier mixed proxy sweep depended on load. The meters now run through the
pre-pass, and a record whose pre-pass did not finish fails. Three parallel
runs at offset 0 give byte-identical DRAM traces.

## 3. The RTL reference at 780, deterministic (16 offsets, 0 .. 750 step 50)

| mode | wr / rd | offsets |
|---|---|---|
| slow (every run 256 columns) | 280 / 280 (281 / 282 at 100, 700) | 10 |
| write-cap break | 264 / 264 | 2 (150, 650) |
| fast (read-cap break) | 302 / 596 .. 600 | 4 (450, 500, 600, 750) |

How the 264 mode starts (pick probe at offset 650, cycle 532192):

- The write batch reads 255 and `refresh_req_i` rises in the same cycle.
- The demand block holds the 256th column.
- The cap flip (`r_batch_done && w_rd_col_any`) still turns the bus to reads.
  The run ends at 255, and the leftover write waits for the next write turn.

What follows is a stable cycle:

- Write runs of 256 / 257 / 259 / 266. A run passes the cap when the reads'
  row is closed; the flip waits for a read column.
- In those cycles the reads' ACT is preferred under the writes' columns
  (`w_row_pref_mask` flips at the cap), giving 3-cycle W->R turns at tWTR.
- The read run after a short turn takes 411 cycles instead of 301.

The fast mode is the same event on a read cap.

## 4. The model

The model has every branch in section 3, line for line:

- `xdir_ok`, the row preference at the cap, and the cap flip at batch 255
  with `col_any` of the other direction;
- the demand block on a pending refresh;
- with `ref_drain_pb`, the RTL's drain: PRE at +1, PRE at +3, REF at +5 after
  the last column.

`granite_sku100 mixed_bl8` with `ref_drain_pb` + `behind_lag` 1, 260 GO phases
(0 .. 1554, step 6 ticks):

| | slow 280 / 280 | broken |
|---|---|---|
| RTL, 16 offsets | 10 (62.5 %) | 6 (37.5 %): fast 4, 264 mode 2 |
| model, 260 phases | 165 (63 %) | 95 (37 %): fast 95 |

The model leaves the slow mode at the RTL's rate. What differs is which cap
the breaking refresh lands on: in the model's walk it is always a read cap.
In 64 debug-logged phases, a refresh episode never started at write batch 255
while traffic was running (it did start at 253 / 254, which do not break, as
on the RTL). The 264 mode is a third of the RTL's breaks, and the model's
walk does not reach it. That residue is recorded, not chased (owner,
2026-11-26: this was the last model-vs-RTL item).

## 5. Default

`ref_drain_pb = True` and `behind_lag = 1` are now the SKU defaults
(`bin/char_model.py`). `sku_norefdrain` is the model before them.

The SKU board compare on the new defaults
(`compare_model_sku_mc023_defaults_vs_board_sku100rpap_2026-11-26.md`) gives
**53 in / 4 out**:

- The four OUT cells are bank_interleave write sides at ~518 (incremental_bl16,
  row_major_bl4 / bl8 / bl16). That is the level the board shows at 2 of 8
  offsets, at the wrong proportion. Filed and deferred as MC-026.
- The board set predates the tREFI fix (d36ee4882). The re-run is MC-027,
  deferred.

Model tests 50 / 50. Changed: the config-shape test lists `sku_norefdrain`'s
two fields. The read-priority test compares against the symmetric register's
slow mode, because `open_page` at GO phase 0 is now in the race's fast mode
(571 reads, against 280 at phase 780).
