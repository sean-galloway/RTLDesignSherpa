# rapids_char_harness SINK self-check moves zero beats

**Status:** RESOLVED 2026-09-22 (board twin tracked as RAPIDS TASK-081)
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

## ROOT CAUSE FOUND AND FIXED 2026-09-22

`kick_off_channel()` staged the descriptor address and never launched it.
`rapids_beats_top` replaced write-to-kick with staged
`CHx_DESC_ADDR_{LOW,HIGH}` plus a rising-edge-detected `KICK_ENABLE`
(SRC 0x0040 / SNK 0x1040); the TB only wrote the address pair. Confirmed on the
waveform: `snk_desc_arready` came up at t=160000 and `snk_desc_arvalid` NEVER
asserted -- the descriptor fetch was never requested, so the scheduler never
left idle and no AW was ever issued.

The staged addresses were landing on the right registers (`CH0_DESC_ADDR_LOW`
is 0x000 and `HIGH` 0x004, which is what the old hand-computed
`base + ch*8 (+4)` produced) -- the sole defect was the missing trigger.

After adding the `KICK_ENABLE` write, at 1 channel x 4 beats:

    ch0: SINK CRC match 0xC8854A27 (gen==wr==golden, valid)
    SINK gen: beats_emitted=4 busy=0 done=0 (expected 4)
    SINK wr meter: prod=4 bp=0 starv=6 idle=0 util=40.0%

Data flows end to end and the CRC agrees with the corrected golden model.

**Two defects, not one.** The CRC half was independent: the golden model
encoded the pre-`f81454d9a` LFSR taps. Fixed separately; the SOURCE self-check
isolates it cleanly, since that path kicks correctly, moves all its beats
(`rd`/`sout` meters prod=4) and failed on CRC alone.

## RESOLVED: the `sin` bus meter reading zero (second-order effect of the same change)

The one error left is `sin bus-meter productive=0`. This is a windowing
artifact, not a data-path fault: the same clear/freeze window counted `wr`
prod=4, and the data provably moved (CRC matched). The AXIS ingress completes
before the window opens -- the failure mode the TB's own comment anticipates
("the front-loaded ingress would fly by while the window was still closed").
Kicking first was supposed to prevent it and did under the OLD protocol, where
the HIGH write stalled until the engine accepted. With the asynchronous
KICK_ENABLE the harness kept a timing assumption that no longer held. Fixed by
waiting for `snk_system_idle` to deassert before releasing ingress.

    SOURCE: 1 passed        SINK: 1 passed   (1 channel x 4 beats)

`make bitstream` no longer needs `BITSTREAM_SKIP_VERIFY=1`.

## Next step (board side)

The board has the SAME missing-KICK_ENABLE defect in a second implementation --
the on-chip sequencer in `rapids_char_top.sv`. Filed as RAPIDS TASK-081. Note
`verify-sim` cannot catch it: the sim toplevel is `rapids_char_harness`, the
bitstream top is `rapids_char_top`, and the harness filelist does not include
that file.

## Superseded: the question that was narrow before the fix

The question was: **why does the sink scheduler never leave idle
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
