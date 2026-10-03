# Design: fifo_depth app + root app launcher

**Date:** 2026-10-03
**Status:** approved in brainstorming (faithful port; house stack; launcher at root)
**References:** `docs/fifo_depth_calculator_v2.xlsx` (the port source);
`bin/apps/ddr_drills/` (the house pattern); `.github/workflows/pages-ddr-drills.yml`

## 1. Intent

Two deliverables:

1. **`fifo_depth`** — a browser port of the async FIFO depth calculator
   spreadsheet: worst-case burst sizing with synchronizer margin and
   encoding-aware depth output (Gray vs Johnson pointers), tied to the repo's
   `fifo_async` (rtl/common) and `gaxi_fifo_async` (rtl/amba/gaxi)
   `USE_JOHNSON` parameter rules.
2. **Launcher** — a root-level app picker page so the GitHub Pages site holds
   more than one app without URL collisions.

Success criteria: the web app reproduces the spreadsheet's numbers exactly
(all six example cases as golden regression tests); the node test suite runs
the same bytes the browser ships; deploy is test-gated like ddr_drills;
existing ddr_drills deep links keep working.

## 2. Scope

In scope: the six-input calculator, full result chain, steady-state check,
Gray/Johnson outputs with savings, the sheet's notes, six example cases
(click-to-load), the launcher, and the Pages workflow restructure.

YAGNI (explicitly out): charts/timelines, URL parameter sharing, localStorage
persistence, clock-drift modeling (the sheet removed it deliberately; the app
carries the same policy note), any backend.

## 3. Calculation model (`bin/apps/fifo_depth/js/model.js`)

Pure functions, dual-environment header (node `module.exports` + browser
global), ASCII only. Operation order matches the sheet exactly — this is the
fidelity contract:

```
tW_item   = (1 + wIdle) * 1000 / fA          // ns per write
tW_total  = burst * tW_item                  // ns for the whole burst
tR_item   = (1 + rIdle) * 1000 / fB          // ns per read
itemsRead = floor(tW_total / tR_item)        // conservative direction: floor
rawDepth  = max(1, burst - itemsRead)
total     = rawDepth + nSync                 // 1x synchronizer margin
gray      = 2^ceil(log2(max(total, 2)))      // USE_JOHNSON=0
johnson   = total rounded up to even         // USE_JOHNSON=1
savings   = gray - johnson (slots and %)
steady    = fA/(1+wIdle) <= fB/(1+rIdle)     // false -> banner, results still shown
```

Validation: `fA, fB > 0` (MHz, no upper cap beyond float sanity), `burst >= 1`
integer, `wIdle, rIdle, nSync >= 0` integers. Invalid input returns
`{ok: false, errors: {...}}`; the app renders field-level messages.

IEEE-754 note: `floor` on the items-read division is order-sensitive. The
sheet's order was run in node during design; all six example cases produce
exact integers (case 2 evaluates to 108 exactly, not 107.999...). The golden
tests pin these values so any future "simplification" of the formula order is
caught.

## 4. Golden example cases (regression values)

| Case | fA | fB | Burst | W_Idle | R_Idle | N_Sync | itemsRead | raw | +sync | Gray | Johnson | Steady |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 80 | 50 | 120 | 0 | 0 | 2 | 75 | 45 | 47 | 64 | 48 | NO |
| 2 | 100 | 90 | 120 | 0 | 0 | 2 | 108 | 12 | 14 | 16 | 14 | NO |
| 3 | 50 | 50 | 120 | 1 | 3 | 2 | 60 | 60 | 62 | 64 | 62 | NO |
| 4 | 30 | 50 | 120 | 1 | 3 | 2 | 100 | 20 | 22 | 32 | 22 | NO |
| 5 | 200 | 100 | 256 | 0 | 0 | 3 | 128 | 128 | 131 | 256 | 132 | NO |
| 6 | 80 | 50 | 120 | 0 | 0 | 3 | 75 | 45 | 48 | 64 | 48 | NO |

Savings (Gray - Johnson): 16, 2, 2, 10, 124, 16.

All six cases are steady-state **NO**: every example has the writer faster on
average than the reader. That is the sheet's own truth — it is a burst-sizing
tool, and the check's message is "bursts grow without bound, need flow
control". The app shows results with that banner; it does not suppress them.

## 5. File layout

```
bin/apps/fifo_depth/
  index.html          inputs, results panel, notes, example table
  style.css           house look (ported conventions from ddr_drills)
  js/model.js         calculation engine (pure, dual-environment)
  js/app.js           DOM glue: inputs -> model -> render, click-to-load cases
  test/run_tests.js   zero-dependency node suite
bin/apps/launcher/
  index.html          app picker page
  style.css           house look, minimal (tiles + header)
  js/apps.js          tile data array (id, name, href, blurb) rendered to DOM
```

House stack invariants (same as ddr_drills): no ES modules, no frameworks,
no build step, no network fetches, ASCII only, mobile-first CSS. The suite
`require()`s the same `js/*.js` bytes the browser loads.

## 6. Page designs

**Calculator** (`/fifo/`): header "FIFO Depth Calculator" with an "All apps"
link to `/`; tagline crediting the v2 spreadsheet. Six inputs with sheet
defaults (80 / 50 / 120 / 0 / 0 / 2) and per-field validation. Results, live
on input: calculation chain (write time per item, total write time, read time
per item, items read, raw depth), steady-state verdict line, then required
depth — raw + sync margin = total, Gray depth, Johnson depth, Johnson savings
in slots and percent. When steady-state is NO, a warning banner carries the
sheet's message. Below: the notes section (sync margin 1x, idle-cycle
semantics, first-word latency, drift policy, USE_JOHNSON elaboration rule),
then the example-cases table; clicking a row copies its inputs into the form.

**Launcher** (`/`): header "RTL Design Sherpa — Apps"; a tile per app from
the `apps.js` array — ddr_drills ("Memory-controller training drills"), fifo
("Async FIFO depth calculator") — each tile linking to its path. Adding a
future app is one array entry plus a workflow copy line.

**ddr_drills header** gains the same "All apps" link back to `/`. Its
internal pages are untouched.

## 7. Deploy restructure

`.github/workflows/pages-ddr-drills.yml` (file name unchanged; display name
may be updated to reflect the site):

- `on.push.paths` gains `bin/apps/launcher/**` and `bin/apps/fifo_depth/**`.
- Test job runs both suites:
  `node bin/apps/ddr_drills/test/run_tests.js` and
  `node bin/apps/fifo_depth/test/run_tests.js`.
- Deploy stages a site directory before upload:

```
site/                 <- launcher contents
site/ddr_drills/      <- bin/apps/ddr_drills contents
site/fifo/            <- bin/apps/fifo_depth contents
```

URL map after deploy:

| URL | Serves |
| --- | --- |
| sean-galloway.github.io/RTLDesignSherpa/ | launcher |
| .../ddr_drills/ | drills app (was root) |
| .../fifo/ | FIFO calculator (new) |

Relative-path check: both apps use relative `style.css` / `js/` / `packs/`
references, so subdirectory deployment works without edits. The launcher uses
root-relative links (`ddr_drills/`, `fifo/`) — acceptable since it only ever
lives at root.

Consequence: the bare-root bookmark changes meaning (drills app moves to
`/ddr_drills/`). Accepted by the user. The user's `ddr-drill` memory note
(recording the root URL as the drills app) needs a one-line update after
deploy; the user edits their own memory file.

## 8. Testing

`bin/apps/fifo_depth/test/run_tests.js`, zero-dependency TAP-style like
ddr_drills:

1. **Model suite** — formula chain against hand-computed values; edge cases:
   burst=1 (raw floor), total=2 (Gray minimum), odd/even Johnson rounding,
   idle-cycle semantics (50%/25% duty), nSync=0.
2. **Validation suite** — each input's invalid cases produce field errors;
   boundary values (fA→0, burst=0, negative idles) rejected.
3. **Example-case regression** — all six rows of section 4 reproduced exactly.
4. **Steady-state suite** — YES and NO paths, including both duty-inverted
   cases (3 and 4).

The workflow's test job runs both apps' suites; deploy requires both green.

## 9. Risks and decisions

- **Float fidelity**: pinned by golden tests (section 3 note).
- **Steady-state semantics**: all shipped examples are NO; the banner is the
  sheet's behavior, preserved deliberately.
- **URL break at root**: accepted; only the bare-root bookmark changes.
- **Workflow name**: the file keeps its name to preserve run history; the
  display name is updated to "apps pages" (the coordinator's run-filter
  commands switch to the new name).
- **No drift modeling**: deliberately omitted, per the sheet's own v2 policy;
  the note text ships in the app.
