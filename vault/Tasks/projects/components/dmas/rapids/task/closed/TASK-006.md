# TASK-006: re-measure the beat-count knee on rapids (July data is stale)
> **Was `TASK-083` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** Medium. **Status:** open 2026-09-22.

`reports/perf/json/genesys_8ch_2026-07-15.json` (8 channels, recorded
2026-07-15T21:35:42) shows a clean knee:

```
  beats 1, 4, 16  -> PASS in both backpressure modes
  beats 64        -> PASS bpoff, FAIL bpon
  beats 256+      -> FAIL in both        (sink_pass and source_pass fail together)
```

**This has NOT been re-measured.** The 2026-09-22 campaign ran beats=8 only --
deliberately below the knee, so that a failure would be attributable to the kick
rather than confounded by this limit. So the knee is a July-era observation, and
whether it survives the staged-address/KICK_ENABLE refactor and the TASK-081 fix
is simply unknown. It is recorded here because it is real measured data that is
currently documented nowhere, not because it is known to be current.

Note the July numbers are NOT tainted by the TASK-081 kick defect: that defect
was introduced by `4ef2dcef0` (2026-09-13 11:34) and fixed by `8fa5af471`
(2026-09-22 15:02), so only board results recorded inside that window are
suspect. July predates it by two months.

**Do:**
- [ ] `make suite BOARD=genesys2 PORT=/dev/ttyUSB0` with
      `--suite-channels 8 --suite-beats 1,4,16,64,256` and compare against the
      July table. (Both `--suite` AND plain `characterize`/`--smoke` write a
      timestamped JSON in the suite schema now -- fixed 2026-09-23, 77dc4de0e --
      so a run no longer evaporates into scrollback the way the 2026-09-22
      numbers did. Note `flows-rapids-beats/reports/` is gitignored: those files
      are durable on disk, NOT in the repo. The tracked, curated records live in
      `rapids_characterization/reports/perf/json/`.)

**RESULT 2026-09-23: the knee is gone. 28/28 configs pass.**

Two board sweeps on the post-TASK-084 bitstream, 8 channels, both backpressure
modes, both seeds:

```
  beats   1   4  16  64  256 | 1024 4096      July 2026-07-15
  now     P   P   P   P   P  |   P    P       P P P (64 bpon F) (256+ F)
```

Every point July failed now passes: 64/bpon (both seeds), and 256, 1024, 4096
(all four combinations each). Sink and source both golden-validated at every
size, up to 32768 beats total at 4096/channel.

What changed in between is substantial -- the staged-address + `KICK_ENABLE`
refactor, the TASK-081 board-kick fix, and TASK-084 -- so this records that the
limit is ABSENT under today's design. It does not attribute the fix to any one
of them; nobody bisected it and this task does not pretend otherwise.

Records: `reports/rapids_char_suite_20260923_032532.json` (1..256) and
`rapids_char_suite_20260923_032753.json` (1024/4096). Both are gitignored --
durable on disk, not in the repo.
