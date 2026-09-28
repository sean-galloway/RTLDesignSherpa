# ISSUE-015: two board host paths program two different read-path tuples

**Status:** open 2026-09-27  **Priority:** P2 -- this is a read-path setting, and
the last time a stale tuple was pinned here it corrupted data while still
reporting healthy bandwidth.
**Owner:** TBD
**Found by:** [[TASK-015]] layer 0, while deciding what `t_rddata_en` should reset to.

## The disagreement

| host path | t_phy_wrlat | t_rddata_en | rddata_delay |
|---|---:|---:|---:|
| `init` -> `pumice_master.SimpleTest` (bring-up, does the read leveling) | 1 | **6** | **7** |
| `pumice_char.ControllerConfig` (the characterisation runner) | 1 | **1** | **2** |

`init write_read char` runs BOTH: `init` programs 1/6/7 and levels bitslip/tap
against it, then `char`'s `ControllerConfig.apply()` re-programs 1/1/2 underneath
the leveling that was measured at the other point.

## Why both appear to work

A joint (t_rddata_en x rddata_delay) board sweep found every clean pair on the
diagonal `rddata_delay = t_rddata_en + 1` -- the a7ddrphy's data-vs-valid offset
is a fixed 1 cycle, so any t_rddata_en works provided the delay tracks it. Both
tuples sit on that diagonal, which is why the 24-cell paging campaign passed
integrity on all 24 cells with the re-program happening mid-run.

## Why it is still worth fixing

1. **The leveling is measured against one point and used at another.** bitslip
   and read tap are chosen during `init` at rden=6/delay=7; the traffic then runs
   at rden=1/delay=2. The eye that was measured is not the eye in use. It works
   today; nothing says by how much margin.
2. **This class of pin has already corrupted data once.** 2026-09-21, overriding
   these to 0/6: all four cells failed integrity while reporting 552.3 MB/s. The
   failure mode is the worst shape available -- the number a reader would quote
   survives and only the integrity flag disagrees (`seq_page_policy.py` carries
   the note).
3. **The reset can only follow one of them.** It now follows `init` (6), which is
   the bring-up authority. That decision is arbitrary between two working points
   and should be a measurement, not a tiebreak.

## Done when

* One place owns the read-path tuple and both host paths read it from there.
* The choice between the diagonal's points is made on measured eye margin at
  75 MHz, not on which file was edited last.
* `csr_reset_parity.py`'s `PHY_TIMING.t_rddata_en` note is updated to cite that
  measurement instead of the tiebreak.

---

## Measurement attempted 2026-09-28 -- and what it takes to do properly

`host_sweep_rddata_delay.py` looked like the instrument: it sweeps
`rddata_delay` 0..15 and reports `beats_mismatched` per setting, so the width of
the clean window is the eye. Run at both candidate points it would settle this.

**It hardcoded the stale tuple.** `t_phy_wrlat=0, t_rddata_en=6` -- the pair that
on 2026-09-21 corrupted data on all four cells of the page-policy A/B while still
reporting healthy bandwidth. The instrument for measuring the read path was
itself carrying a known-bad setting. Now `--wrlat` / `--rden` arguments,
defaulting to what `init` programs.

**It still cannot answer the question as written.** Run at `--rden 6` and
`--rden 1`, both reported 16/16 beats mismatched at every delay 0..15 -- no eye
at either point. That is the tool, not the tuples:

* it never LEVELS. `init` scans bitslip x IDELAY tap to find the capture point;
  this tool programs a fixed geometry and sweeps only the coarse delay, so
  without the leveled bitslip/tap the read path does not capture at any delay.
* it forces `rd_phase=1`, while the board ships `rd_phase=0`.

So a fair comparison needs a per-point eye scan: for each `t_rddata_en`, level
(bitslip x tap) and THEN sweep `rddata_delay`, reporting the width of the clean
window -- three nested loops on hardware, not one. `host_bringup_joint_probe.py`
is the closest existing shape (it does an inner bitslip scan per outer latency
point at a fixed mid tap) and is probably what to extend.

Recorded rather than guessed at: the honest state is that the two tuples are both
known to WORK and their relative margin is still unmeasured. Do not close this on
the strength of "both pass integrity" -- that was already true, and is exactly
what makes the question worth answering.
