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

## Next step

Compare against the SOURCE self-check, which passes on the same harness: the
source path shares the descriptor/scheduler front end, so the divergence is in
the AXIS ingress -> sink SRAM -> `axi4_slave_wr_crc_check` chain. Check first
whether `s_axis` stimulus is reaching the DUT at all (the `sin` meter reading
zero suggests it is not), which would put the fault ahead of the DMA rather
than inside it.
