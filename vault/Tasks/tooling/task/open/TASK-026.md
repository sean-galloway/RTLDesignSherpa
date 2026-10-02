# TASK-026: formal stale-flat self-detection -- a regenerate-and-diff mode beside `bin/formal_status.py --inventory`

**Priority:** P2 -- a stale committed sv2v flat leaves a proof green against
RTL that no longer exists, and it has already happened undetected twice in
rapids (rapids BUG-011, and the 36-of-48 stale flats from the 2026-09 formal
flat staleness audit).
**Status:** open, filed 2026-10-02 as the fan-out of rapids BUG-011's third
checkbox (tooling is global; the mechanism closes here, not per area -- see
[[feedback_tooling_is_global_fan_out_per_unit]]).
**Owner:** TBD

## The gap

`formal/<area>/<block>/<block>_flat.v` is a COMMITTED sv2v snapshot of the
SystemVerilog source. A source change with no re-flatten leaves the proof
checking the old design, silently and green. rapids BUG-011 found two such
flats (`axi_read_engine_beats`, `axi_write_engine_beats`, stale since the
rapids BUG-009 engine fixes) only because someone looked. The 2026-09-11
staleness audit found 36 of 48 flats stale repo-wide by the same manual
method. Nothing in CI or pre-commit detects the drift.

`bin/formal_status.py` already inventories the suite (`--inventory`); it
reports pass/fail from sby artifacts but never asks whether the flat matches
its sources.

## Done when

- [ ] `bin/formal_status.py` (or a sibling) gains a mode that re-flattens each
      proof's sources to a temp file and diffs against the committed
      `*_flat.v`, reporting stale flats by name. Diff in a temp dir --
      never overwrite the committed flat (see
      [[reference_committed_sv_is_post_formatter]]: committed flats may be
      post-formatter, so the comparison normalizes whitespace/formatting
      rather than demanding byte equality, or the diff is against sv2v run
      with the same flags the proof Makefile uses).
- [ ] The mode runs somewhere unattended (pre-commit on touched flats is the
      cheap version; the filelists CI job is the thorough one -- tooling
      TASK-015's pattern is the precedent).
- [ ] A planted-staleness test proves the mode fails when a flat is behind
      its source (mutation test, per house rule).
- [ ] The mode is then run repo-wide once and the stale flats it surfaces are
      either regenerated or filed per area.

## Notes

- sv2v flags matter: the rapids finding recorded that proof Makefiles differ
  in what they pass, and that `--define=FORMAL` is passed by none of them
  (rapids TASK-022's finding). The re-flatten must use each proof's own
  Makefile invocation, not a repo-global default.
- Related: rapids BUG-011 (the instance that motivated this), the
  formal-flat-staleness memory of 2026-09-11.
