# Slack Explorer

A standalone, file://-friendly drill app for exploring setup/hold slack and
pipelining tradeoffs.

Open `index.html` in a browser, or serve it statically. No build step, no
CDN, no npm.

## Files

- `index.html` -- UI
- `style.css` -- mobile-first styles
- `js/model.js` -- pure slack/pipeline math (no DOM)
- `js/app.js` -- DOM glue
- `test/run_tests.js` -- zero-dependency TAP-ish node runner

## What it teaches

Panel 1 shows how setup and hold slack change as you drag clock skew. The
sign flip is intentional: positive skew helps hold but hurts setup, while
negative skew helps setup but hurts hold.

```
setup slack = T - tCO - tLOGIC - tROUTE + skew - tSU
hold slack  = tCO + tLOGIC + tROUTE - skew - tHD
```

Panel 2 shows the classic latency-vs-throughput tradeoff when pipelining a
fixed amount of combinational logic into K balanced stages. Skew is ignored
in this panel so the relationship is clear:

```
per-stage logic = (tLOGIC + tROUTE) / K
min period      = tCO + per-stage logic + tSU
max frequency   = 1000 / minPeriod   (MHz when delays are in ns)
latency         = K cycles
```

The hint reinforces the common confusion: hold violations are fixed by
adding more delay (buffer, min-delay constraint), not by removing delay.

## Test

```bash
node bin/apps/slack_explorer/test/run_tests.js
```

Exit code 0 when all assertions pass.

## Model API

- `SLACK.validate(p)` -- validate parameters and return `{ok, errors}`.
- `SLACK.setupSlack(p)` -- setup slack in ns.
- `SLACK.holdSlack(p)` -- hold slack in ns.
- `SLACK.computeSlack(p)` -- `{setupSlack, holdSlack, setupPass, holdPass,
  pass, hint}`.
- `SLACK.computePipeline(p, K)` -- `{K, stageLogic, minPeriod, maxFreq,
  latency, closesWithT}` for a given number of stages.
- `SLACK.computePipelineTable(p)` -- array of pipeline results for K = 1..4.
- `SLACK.compute(p)` -- unified result containing both slack and pipeline
  output.
