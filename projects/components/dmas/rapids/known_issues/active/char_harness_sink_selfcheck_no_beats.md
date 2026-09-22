# rapids_char_harness SINK self-check moves zero beats

**Status:** Active / Investigation
**Severity:** High — blocks `verify-sim`, and therefore `make synth` and
`make bitstream`, on every build of `flows-rapids-beats`.

## Symptom

`test_rapids_char_harness_sink` (4 active channels, 8 beats each) times out
with nothing transferred:

```
timeout: snk_system_idle=1 wr_beat_count_total=0 (expected 32)
ch0..ch3: wr_crc_valid=0
ch0: SINK CRC mismatch gen=0x89346A28 wr=0x00000000
sin bus-meter productive=0 (meter not counting)
wr  bus-meter productive=0 (meter not counting)
```

Every channel's write CRC reads `0x00000000`, the generated CRCs do not match
the goldens either, and BOTH bus meters report zero productive cycles. Nothing
moves on the sink path and the DUT nonetheless reports idle.

## Not the resolved write-commit stall

This is NOT [[snk_scheduler_write_commit_stall]] (RESOLVED 2026-07-16). That
one had **correct data** with a trailing commit stall (`snk_system_idle=0`,
CRCs matching, 64 AW / 64 WLAST / 512 W beats, only the B responses short).
Here the opposite holds: `snk_system_idle=1` and zero beats. It is also not
[[drain_size_gt1_source_beat_drop]], which is a SOURCE-path short delivery.

## Pre-existing (established 2026-09-13)

Reproduced identically on a pristine `git worktree` at HEAD, containing none of
that day's rapids work — same failure, same generated CRCs (`ch2 0x942B69BD`,
`ch3 0x06C8E181`) against the same goldens. So it is not caused by the
extended-addressing feature or the USE_ROW_COL_MAJOR_ADDRESSING default flip.

There is no recorded passing sink run at any point: `dv/logs/` holds only a
SOURCE self-check pass from 2026-07-16. The sink self-check may never have been
green since the harness moved.

## Workaround

`BITSTREAM_SKIP_VERIFY=1` bypasses the gate. Both Genesys 2 row/col A/B builds
(2026-09-13) used it and completed normally, so the DUT itself builds and
closes timing — the defect is in the sink self-check path, the harness slave,
or the self-check's configuration.

## MEASURED 2026-09-22 -- the stimulus DOES arrive (supersedes the theory below)

Instrumented the self-check to read `o_gen_beat_count_total` / `gen_busy` /
`gen_done`, which the harness exports and no test read (commit `832973a50`).
At 1 channel x 4 beats:

    SINK gen: beats_emitted=4 busy=0 done=0 (expected 4)

The AXIS generator emitted every beat and returned to IDLE, so `s_axis`
handshook four times and the DUT accepted all the data. **The `sin` meter's
`productive=0` is an artifact, not evidence of missing stimulus**: the meter
window is gated on `obs_dut_busy = ~snk_system_idle` (harness line 1156) and
frozen by `obs_meter_freeze = ~obs_win_active`, so with the sink never leaving
idle the window never opens and BOTH meters stay at zero by construction.

`wr_beat_count_total=0` is real, though -- that counter is gated by
`r_wr_active` (set on an AW handshake) and is NOT windowed. So: data went into
the sink SRAM, and the DMA never issued a single AW to drain it.

Bisected -- the RAPIDS sink RTL is NOT at fault:
- `test_rapids_beats_top_sink` PASSES at HEAD (301s, "sink verified (4 beats)")
  through the same `rapids_beats_top` this harness wraps.
- `test_rapids_core_beats_sink` verifies 4 beats.
- The sink datapath suite passes 54/54, including 32/32 multi-channel stress.
- The harness fails identically at 4ch x 8 beats and at 1ch x 4 beats, so it is
  not multi-channel-specific.

Eliminated by inspection, with evidence: `cfg_alloc_size` (TB programs 16),
`fill_space_free` (resets to full depth), `w_wr_need_base` (gated on
`r_is_ext`; the descriptor is DATA), `EN_WRITE` (sink passes `1'b1`, forwarded
correctly), channel-id routing (`tid` matches both sides), SRAM depth (test
overrides to 512, same as the passing component test), descriptor-RAM wiring
(both halves symmetric, `snk_m_axi_desc_*` fully connected), and the AXIS
generator FSM (holds `tvalid` in RUN; cannot terminate early).

## Next step

The question is now narrow: **why does the sink scheduler never leave idle
after the APB kick?** `snk_system_idle = &scheduler_idle`, the descriptors load
and the by-name kick writes land (visible in the log), yet no AW is issued.
Check whether `snk_desc_arvalid` ever asserts -- i.e. whether the sink
descriptor FETCH starts at all. A `WAVES=1` run reproduces in ~9 minutes at
`TEST_NUM_ACTIVE=1 TEST_NUM_BEATS=4`.

## Second, independent defect: the AXIS generator disagrees with the golden

With 4 beats confirmed emitted, the generator's expected CRC still does not
match the model: `gen=0xC8854A27` vs `golden_crc(0,4)=0x20F5B1C9` (and
`0x89346A28` vs `0x8C023372` at 8 beats). It is not an off-by-one in count or
start -- no `golden_crc(0,n)` for n=1..12 matches, nor a window advanced by one
or two.

Why nothing caught it: the golden's `_KNOWN_GOOD` values are exactly the ones
the SOURCE path verifies, so the model is pinned to `axi4_slave_rd_pattern_gen`
and `axis4_slave_pattern_check`. The only test covering the AXIS *master*
generator, `val/amba/test_axis4_pattern_pair` (3 passed), asserts
`gen_crc == chk_crc` -- but the checker CRCs exactly what the generator sent,
derived from the same LFSR, so that comparison is near-tautological and cannot
detect a sequence that differs from the reference. This self-check is the first
place the two are ever compared.

Expected values for ch0, seed 0xDEADBEEF: beats 0..3 are 0xDEADBEEF,
0x6F56DF77, 0x37AB6FBB, 0x9BD5B7DD. Read `s_axis_tdata` from a waveform
(`tdata = {REP{lfsr_out}}`): if it shows those, the LFSR is right and the CRC
accumulation is the defect; if not, the LFSR is.
