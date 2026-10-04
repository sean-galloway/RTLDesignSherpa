# CDC Drill

A standalone, gamified clock-domain-crossing drill app in the style of
`bin/apps/ddr_drills` and `bin/apps/fifo_depth`.

## What it is

Two modes:

- **Spot the violation** -- read a short scenario (text + ASCII timing diagram)
  and select every illegal CDC element in the exact set.
- **Pick the synchronizer** -- read the data characteristics and choose the
  right structure from four plausible options.

Difficulty tiers (basic / medium / full) can be filtered. Score is tracked per
session. A seed field lets you replay the same sequence for study.

## Files

```
bin/apps/cdc_drill/
  index.html          standalone page (works from file://)
  style.css           single-file CSS, no frameworks
  js/
    rng.js            seeded mulberry32 + deterministic helpers
    content.js        pure scenario generators and question bank
    model.js          pure session/scoring engine
    app.js            DOM glue
  test/
    run_tests.js      zero-dependency TAP-ish node runner
```

## Run

Open `index.html` in any browser (no server required).

## Test

```bash
node bin/apps/cdc_drill/test/run_tests.js
```

Exit code 0 on pass.

## Content contract

- `options[0]` is the correct answer for picker questions; spot questions list
  all correct options before incorrect ones.
- The UI shuffles options; the model never does.
- Every option has a per-option explanation.
- Every question has an overall explanation.
- All strings are ASCII only.
- All randomness is seeded and testable.
