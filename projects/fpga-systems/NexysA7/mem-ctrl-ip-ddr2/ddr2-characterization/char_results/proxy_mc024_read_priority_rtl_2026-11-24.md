# MC-024: the read-priority direction register in RTL -- proxy, formal, timing

> memory-controllers MC-024, 2026-11-24, after the owner's two decisions
> (`SCHED_DIR_RP` resets 512 / 128; `SCHED_POLICY.dir_mode` resets 0, "power
> up should be the most generic setting"). The model pricing is
> `model_mc024_read_priority_2026-11-24.md`.

## 1. What was built

- `mc_bank_pick` `HAS_RD_PRIO` (granite builds it, `GRANITE_SCHED_RD_PRIO`):
  `rd_prio_en_i`, `wr_starve_i[11:0]`, `wr_burst_i[7:0]`. A 12-bit saturating
  counter of cycles a write head (the registered records) waits with no write
  column, its compare registered (`r_wr_starved`); the next-state branch
  `w_rp && !r_dir && w_wr_starved` after the two column-fire branches; the
  cap `r_batch_done <= w_rp ? (w_dir_nxt && wr_burst != 0 && batch_nxt >=
  wr_burst) : today's`. `dbg_dir_cause_o` 3 = write starvation.
- `mc_scheduler_plane` / `granite_core` / `granite_top_geared` plumbed from
  the CSRs; pumice, scoria and andesite tie the mode off.
- CSRs: `SCHED_POLICY.dir_mode[24]` (reset 0) and `SCHED_DIR_RP` @ **0x194**
  (`wr_starve[11:0]` reset 512, `wr_burst[23:16]` reset 128). Not 0x080 as
  the task first said: `OBS_ROW_HIT[8]` held 0x080-0x09C (pumice, and granite
  until the 2026-10-24 narrowing), a retired hole by the map's rule. The
  regblock deleted and regenerated (`bin/peakrdl_generate.py -o`); the diff
  is the two fields. `SCHED_DIR_RP` joins granite's config false paths.
- Host: `Pumice.set_dir_mode` (a map without the field raises on read
  priority rather than measuring the wrong mode); `ControllerConfig.read_priority`
  written on every config; preset `rd_priority`; proxy knobs `TEST_DIR_MODE`,
  `TEST_WR_STARVE`, `TEST_WR_BURST`.
- The SKU model's starvation flag now follows the RTL's registration (the
  compare on the counter's current value, a slot behind the count): 512 /
  128 on the mixed cell 299 / 456, union 599, unchanged within noise.

## 2. Proxy: the mixed cell, both open-page presets, five refresh phases

`test_granite_char_perf`, 100 MHz, `TEST_DUAL=1`, 4 generators, `mixed` bl8,
`TEST_TXN=512`, a clean build. Write / read MB/s, 0 mismatched beats on
every run.

| preset | 778 | 779 | 780 | 781 | 782 |
|---|---|---|---|---|---|
| `defaults`, read priority | 297.6 / 456.4 | 297.8 / 456.2 | 301.1 / 455.5 | 304.5 / 457.0 | 301.7 / 455.7 |
| `open_page`, read priority | 297.0 / 456.4 | 296.8 / 455.8 | 297.4 / 456.6 | 298.5 / 456.1 | 302.0 / 456.2 |
| `defaults`, symmetric (`proxy_mc023_refresh_lock`) | 299.0 / 514.3 | 280.3 / 282.2 | 280.0 / 282.0 | 277.0 / 278.8 | 279.3 / 281.4 |
| `open_page`, symmetric | 280.7 / 282.7 | 280.5 / 282.4 | 286.7 / 330.8 | 300.3 / 506.7 | 285.2 / 308.9 |

**One mode on all ten** (455.5 .. 457.0 reads), against the symmetric
register's refresh-placed race; the model priced 299 / 456.

Mode 0 is today's register: `defaults` 778 at the reset reads 299.0 / 514.3
and `open_page` 781 300.3 / 506.7, both identical to the runs before the RTL.
`open_page` 781 with `dir_mode` 0 WRITTEN read 279.6 / 281.7: the extra
register write moves GO against the refresh counter, which is the ISSUE-005
draw (the reset run at the same phase is the fast mode), not the mode.

## 3. Formal (`formal/mc_common/mc_bank_pick`, all seven tasks PASS)

- `equiv` / `equiv_n4`: the DUT built `HAS_RD_PRIO = 1` with the mode off
  and the knobs free per cycle, against the golden copy on every output
  (BMC 20, both shapes).
- `rdprio` (new, BMC 24): the mode on, the knobs anyconst (wr_starve 1..4,
  wr_burst 1..3), free inputs, a reference starvation counter kept from the
  ports. `a_starve` (a starved write head with the bus on the reads and no
  write column turns the bus next cycle), `a_cause3` (a starvation flip had
  the flag), `a_no_read_cap` (the reads never leave on the cap),
  `a_wr_cap_min` (a write cap flip ran at least wr_burst columns).
  `rdprio_cover`: the starvation flip (step 5), a write cap flip at exactly
  wr_burst (step 6), a read drain flip (step 4).
- Mutation, the flat rebuilt per mutant: dropping the starvation branch
  fails `a_starve`; an unguarded cause 3 fails `a_cause3`; a cap on the read
  hold fails `a_no_read_cap`; the write cap one column early fails
  `a_wr_cap_min`.
- `cover`, `dual`, `dual_cover` unchanged and PASS.

## 4. The 100 MHz bitstream

`GRANITE_SYS_100=1 make bitstream`, the SKU (default placement), the 0.2 ns
budget as clock uncertainty: **WNS +0.003 ns, 0 failing endpoints** (build C,
the RTL before: +0.002). The worst path is MC-022's pick select
(`r_self_stale` -> `r2_cls`); none of the 20 worst touch the new logic.
37,507 LUT on the design. The pick core out of context at granite's
parameters: 1,845 -> **1,858 LUT (+13), 443 -> 457 FF (+14)** with
`HAS_RD_PRIO`. Closure is the knife edge MC-022 records, not margin.
