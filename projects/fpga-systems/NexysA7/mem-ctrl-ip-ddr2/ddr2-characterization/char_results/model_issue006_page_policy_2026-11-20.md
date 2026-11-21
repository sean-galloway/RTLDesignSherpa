# Model: the page policy is the RTL's -- the hybrid the board's `defaults` runs, and the flat close-on-drain its `open_page` writes (memory-controllers ISSUE-006), 2026-11-20

Until today the SKU model had one page policy: the exact close-on-drain
auto-precharge (a column closes its row when no same-row entry sits behind it
in its bank), standing in for both the board's `defaults` preset and its
`open_page` preset. Two findings said the stand-in was wrong for `defaults`:
the by-mode compare of MC-021's close-out (the board's `defaults mixed_bl8` in
the slow mode on five of five runs where `open_page` was fast on three, and
the model with a fast phase for both), and MC-019's proxy (the RTL issuing
~700 demand PREs per `col_ilv` run under `defaults`, 424 of them on the row
lane, where the model issued none). Both are the page policy.

## 1. What the presets are

Read from `pumice_char.py`'s `ControllerConfig.apply` and `mc_page_policy.sv`:

- `defaults` = the RDL resets: `PAGE_POLICY_CFG.policy_mode` 4 (the hybrid),
  `PAGE_TIMEOUT_CFG.tr_init` 2. The pick's auto-precharge rule is the exact
  close-on-drain term WITH `ap_conflict_only`: a column closes its row on a
  known conflict (a different-row entry queued behind it) always, and on a
  drained queue (nothing behind it) only where the bank's history arms it
  (`drain_close_ok`: the bank's last ACT opened a different row than the one
  before AND that previous row served at most `DRAIN_ARM_MAX_COLS` = 8
  columns, disarmed when an ACT reopens a row a predicted close had just
  closed). A row left open is closed by its idle timer -- `tr_init` 2 cycles
  with no command to the bank and no head hitting the row -- as the pick's
  lowest-priority command, a PRE into a slot no demand command takes, or by
  the next row's demand PRE when that arrives first.
- `open_page` = `page_policy_or` OPEN, policy_mode 0, tr_init 0: the legacy
  flat rule, the exact close-on-drain everywhere, no history gate, no
  timeout. This is what the model had.
- `close_page` and `bank_interleave` = `page_policy_or` CLOSE, policy_mode 0:
  every column closes (the model's `page_close`).

The proxy's `TEST_PAGE_POLICY=1` wrote the flat field alone and left
policy_mode at its reset, so the MC-019 proxy's "open_page" rows were the
hybrid too; the knob writes mode 0 and tr_init 0 with the policy now, as the
board preset does.

## 2. The term

`GraniteSKU` carries `mc_page_policy`: `page_mode` (0 / 1 / 2 / 3 / 4 as the
CSR), `tr_init`, `drain_arm_max_cols` 8, `pred_cmd_reg` (the bank-pick
build's PRED_CMD_REG: the policy's history sees the issued command one slot
late). Per bank: the row image, the drain-arm history (`last_row`,
`to_closed`, `keep_open`, `drain_arm`, `ap_closed`, `row_cols`) updated from
the issued-command view (main, timeout and lane commands; PREab closes
every bank), the registered `drain_close_ok`, the idle countdown and its
sticky `expired`, re-warmed by any command to the bank or by a head of either
direction hitting the open row (the plane's registered `open_row_demand`),
and the registered background-close request (the lowest expired bank with
no demand for its row and no keep-open verdict). The pick's auto-precharge
reads `drain_close_ok`; the timeout PRE fires when no demand command does,
never on the winner's bank, at the bank's PRE timer. `sku_to_pre` counts
them; the CSV carries `to_pre`.

The one defect found on the way: the delayed command view has to be compared
against the row image of ITS cycle. With the live image, an ACT seen one slot
late found its own row already open and read as "we closed a row we needed":
`keep_open` set on every row change, `drain_close_ok` never armed, every row
change a PRE + ACT instead of an auto-precharge, and the first run of the
term cost `defaults col_major_interleaved_bl4` 18 percent against the board
where the RTL's hybrid costs nothing. The RTL's registered image lags the
fire by the same cycle its command view does ("an ACT's bank is closed in
the image both when it fires and a cycle later", the PRED_CMD_REG note), and
the model now keeps last slot's image for that compare.

## 3. The result

`granite_sku100` is the hybrid (the board's `defaults`); `granite_sku100_open`
is mode 0 (the board's `open_page`, the policy the model had);
`granite_sku100_bi` / `_close` are mode 0 with every column closing.
Model CSVs `model_ramulator2_ddr2_granite_sku100{,_open,_bi,_close}_s9_2026-11-20.csv`,
the two mixed cells at GO offset 480 beside them.

`compare_model_sku_vs_board_sku100s4_s9_2026-11-20.md` (one run per cell):
**56 in / 1 out**, the one out the open_page mixed row against the board's
fast-mode single number (the mode question). Read by mode against the
board's five windows runs, `compare_model_sku_vs_board_sku100s4_s9_modes_2026-11-20.md`:
**57 in / 0 out.**

| cell | board | hybrid (defaults) | mode 0 (open_page) |
|---|---|---|---|
| defaults mixed_bl8 | 272 / 273 (545) x5, one mode | 274 / 274 (547) at GO 0 and 480; 0 of 40 phases fast (rd 273.5-273.9) | - |
| open_page mixed_bl8 | 311 / 522 x3, 272 / 272 x2 | - | 274 / 274 at GO 0, 309 / 568 at 480; 2 of 40 phases fast |
| defaults col_major_interleaved_bl4 / 8 / 16 | 765 / 762, 768 / 767, 772 / 770 | +0.9 / +1.2, +0.4 / +0.6, +0.5 / +0.7 % | (open_page +1.1, +0.9, ...) |
| defaults row_thrash_bl8, random_bl8 | 768 / 766, 723 / 750 | +0.4 / +0.7, +0.4 / -0.8 % | - |

Every `defaults` cell is within 1.2 percent; the SKU's other presets did not
move (their configurations are mode 0, as the board's). The hybrid issues
what the flat rule never did: on `col_major_interleaved_bl8` 4,884 lane PREs,
2,096 conflicts and 4 background closes per run (mode 0: none of each), on
`random_bl8` 15,766 lane PREs and 2,437 background closes. The counts are not
the proxy's (424 lane PREs on its 4-generator `col_ilv` at 512
transactions; a different stream), the kind and the sign are.

The question ISSUE-006 was filed on is answered the way the board answered
it: under the hybrid the mixed cell has ONE mode. The fast mode is a race on
a zero-column write turn that begins with the holder's PRE closing a row the
lane had just opened for the waiter (ISSUE-005); under the hybrid that row's
column auto-precharges only on a known conflict, and the turn structure that
lets the race start does not form. The board's five slow runs of five were
the predictor, not the draw.

## 4. Record

- `granite_sku_controller.cpp` (`m_page_mode`, `m_tr_init`, `m_drain_arm_max_cols`,
  `m_pred_cmd_reg`, `ap_policy()`, `page_policy_slot()`, the timeout PRE in
  the fire stage, `sku_to_pre`), `timed_loadstore_trace.cpp` unchanged;
  `char_model.py` (`ModelConfig.page_mode` / `tr_init`, `granite_sku100_open`,
  `BOARD_PRESET_OF` one preset per config, the `to_pre` column);
  `test_char_model.py` (`test_hybrid_page_policy_issues_the_demand_pres_the_boards_defaults_do`;
  the two-mode test moved to `granite_sku100_open` with the hybrid asserted
  one-mode; 42 / 42 pass).
- `test_granite_char_perf.py`: `TEST_PAGE_POLICY` writes policy_mode 0 and
  tr_init 0 with the policy (the board preset's form).
- The GO sweep (session scratch `issue006/go_sweep_*.csv`): 40 phases at
  39-tick steps, both configs.
