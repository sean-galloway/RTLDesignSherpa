# ISSUE-002: backpressure runs record meter numbers that cannot mean anything
> **Was `TASK-085` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** Medium -- nothing is broken, but the suite JSON stores
`AXIS-out util=0.0% eff=0.00 GB/s` for every backpressure run and nothing marks
those as non-measurements. **Status:** CLOSED 2026-09-23 -- fixed and validated on the board.

Found while diagnosing TASK-082. Under `--suite` with backpressure ON the source
egress meter reports, on all 10 bp-on configs:

```
  prod=0   bp=<the whole window>   starv=0   idle=9
```

That is not a meter fault -- it is arithmetically forced by how the knob works:

- `run_source_selfcheck` arms the checker with `CHK_READY_EN=0` (tready LOW),
- then `go()` arms the meter window AND kicks in the same on-chip pulse,
- then `_poll_backpressure` raises/lowers ready FROM THE HOST over UART.

One CSR write is ~24 bytes at 115200 baud = **2.08 ms = 208,333 aclk cycles**.
The bp-on windows measured 276..2300 cycles (2.8..23 us). So **at most 0.011 of a
single host write fits inside the window** -- it closes 90x to 750x before the
host can raise ready even once. The meter therefore measures a deliberately
stalled egress and freezes; the real transfer happens afterwards. `axis_bus_meter`
is correct (`w_prod = tvalid && tready` etc., mutually exclusive), and the tap is
on the real `m_axis_*` nets.

Backpressure mode is a DATA-INTEGRITY test -- the golden CRC passes and that is
its point (`_poll_backpressure`: "always makes forward progress"). The hazard is
only that its throughput numbers are recorded as if they were measurements.

**Do:**
- [ ] Mark bp-on rows in the JSON and the printed table as integrity-only, or
      omit their `perf` block. A future reader comparing suite files will
      otherwise conclude the egress collapsed under backpressure.
- [ ] If host-paced backpressure is ever supposed to be measurable, it needs an
      on-chip stall generator; over UART it cannot be, by three orders of
      magnitude.

**FIXED 2026-09-23.** Both row builders now emit
`perf_valid: {'sink': True, 'source': not bp}`, and the summary table prints
`n/m` instead of `0.00` for a half whose window did not measure the transfer,
with a footnote saying why. The `perf` buckets are KEPT, not deleted -- they
truthfully describe a stalled egress, and throwing them away would destroy
evidence; they are flagged so nobody reads them as throughput.

Board-validated end to end (8ch, beats 4 and 64, both seeds): all four bp-on
rows render `n/m`, `PEAK MEASURED` is unchanged (5.39 + 5.83 = 11.22 GB/s), and
a real JSON carrying `perf_valid` was written.

Backward compatible by construction: files written before this change have no
`perf_valid` key, and the reader defaults absent -> valid, so every JSON already
on disk (and `docs/assets/make_plots.py`, which does not read `perf` at all)
behaves exactly as before.

Also hardened while here: `_print_suite_summary` subscripted `r['sink']` and
`first[path]` directly, which crashes on a row with a skipped half -- a shape
`_single_row` can emit (`--sink-only` / `--source-only`) while its docstring
claims schema parity with `run_suite`. Guarded, so the claim is now true.

`_peak()` needed no fix: it takes `max()`, which already ignores the 0.0 a bp-on
row contributes. Verified empirically rather than assumed -- sink 5.838 and
source 6.247 with and without those rows. A filter was added anyway so the
intent survives anyone changing `max()` to a mean.
