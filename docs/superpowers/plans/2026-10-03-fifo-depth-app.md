# fifo_depth App + Root Launcher Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the async FIFO depth calculator spreadsheet to a browser app at `/fifo/`, and add a root launcher page that selects between all apps.

**Architecture:** New `bin/apps/fifo_depth/` (pure model + DOM glue, house stack) and `bin/apps/launcher/` (tile picker) alongside untouched `bin/apps/ddr_drills/`. The existing Pages workflow stages a site directory (launcher at root, both apps under subpaths) and runs both test suites before deploy.

**Tech Stack:** Vanilla JS IIFEs with the dual-environment header, zero-dependency node test runner, mobile-first CSS, GitHub Actions Pages deploy.

**Spec:** `docs/superpowers/specs/2026-10-03-fifo-depth-app-design.md`

## Global Constraints

- ASCII only, everywhere (source, tests, HTML copy).
- No ES modules, no frameworks, no build step, no network fetches — same invariants as ddr_drills.
- Dual-environment header idiom, copied from `bin/apps/ddr_drills/js/model.js:11-13` (`var FD = (typeof window !== 'undefined' ? window : globalThis).FD || ...` plus a trailing `if (typeof module !== 'undefined' && module.exports) { module.exports = FD; }` footer).
- Formula operation order MUST match the spec §3 exactly: `tW_item=(1+wIdle)*1000/fA`, `tW_total=burst*tW_item`, `tR_item=(1+rIdle)*1000/fB`, `itemsRead=Math.floor(tW_total/tR_item)`, `rawDepth=Math.max(1,burst-itemsRead)`, `totalDepth=rawDepth+nSync`, `grayDepth=2^ceil(log2(max(totalDepth,2)))`, `johnsonDepth= totalDepth%2===0?totalDepth:totalDepth+1`, `drainable = fA/(1+wIdle) <= fB/(1+rIdle)`.
- Validation bounds: fA/fB > 0 (finite numbers), burst >= 1 integer, wIdle/rIdle/nSync >= 0 integers.
- Golden regression values (spec §4): case1 (80,50,120,0,0,2) -> itemsRead 75, raw 45, total 47, gray 64, johnson 48; case2 (100,90,120,0,0,2) -> 108, 12, 14, 16, 14; case3 (50,50,120,1,3,2) -> 60, 60, 62, 64, 62; case4 (30,50,120,1,3,2) -> 100, 20, 22, 32, 22; case5 (200,100,256,0,0,3) -> 128, 128, 131, 256, 132; case6 (80,50,120,0,0,3) -> 75, 45, 48, 64, 48. All six: steadyState drainable = false.
- **Commit discipline (hard rule in this repo):** other sessions keep staged work in this index. Every commit step uses pathspec commits only: `git add -N <any new files>` then `git commit -m "..." -- <exact files of this task>`. Never `git commit -a`, never a bare `git commit`.
- Commit message convention: `feat(fifo_depth): ...`, `feat(launcher): ...`, `ci(apps): ...`.

## Review Focus

1. **Equal frequencies, zero idles** (fA==fB, burst N): itemsRead == N, rawDepth clamps to 1 via `max(1, ...)` — a user expects the minimum-depth floor, not zero or negative.
2. **burst = 1**: rawDepth 1, totalDepth 1+nSync, grayDepth minimum 2 — the `max(total,2)` guard must not be dropped.
3. **Steady-state YES path**: no golden case exercises drainable=true; a user entering fA < fB must see no warning banner. Pinned in Task 1.
4. **Non-integer MHz** (e.g. 66.667): model must accept fractional frequencies without rounding; itemsRead still exact floor. Pinned in Task 1.
5. **savingsPct when grayDepth == johnsonDepth** (possible when totalDepth is a power of 2): percent must be 0 with no division issue. Pinned in Task 1.

---

### Task 1: Calculation model + golden tests

**Files:**
- Create: `bin/apps/fifo_depth/js/model.js`
- Create: `bin/apps/fifo_depth/test/run_tests.js`

**Interfaces:**
- Produces (used by Task 2's app.js and Task 1's own tests):
  - Global `FD` (dual-environment) with:
    - `FD.validate(p) -> {ok: bool, errors: {fA?: string, fB?: string, burst?: string, wIdle?: string, rIdle?: string, nSync?: string}}` — `p = {fA,fB,burst,wIdle,rIdle,nSync}` (all may be numbers or numeric strings from inputs; validate coerces).
    - `FD.compute(p) -> {ok: true, writeNsPerItem, writeNsTotal, readNsPerItem, itemsRead, rawDepth, totalDepth, grayDepth, johnsonDepth, savingsSlots, savingsPct, steady: {writeRate, readRate, drainable}}` — only called with already-valid input.
    - `FD.EXAMPLES -> [{case:1, fA:80, fB:50, burst:120, wIdle:0, rIdle:0, nSync:2, note:"Baseline: 80 MHz writer into a 50 MHz reader"}, ...]` — all six spec cases with their notes verbatim from the sheet.
  - Test runner: `node bin/apps/fifo_depth/test/run_tests.js` prints TAP-style lines and exits non-zero on failure (same shape as `bin/apps/ddr_drills/test/run_tests.js`).

- [ ] **Step 1: Write the failing test suite**

In `bin/apps/fifo_depth/test/run_tests.js`: a minimal zero-dep harness (copy the assertion style of the ddr_drills runner) plus tests:
- `golden case N` x6: for each `FD.EXAMPLES` entry, `compute` must return the spec §4 values exactly (itemsRead/rawDepth/totalDepth/grayDepth/johnsonDepth from Global Constraints) and `steady.drainable === false`.
- `equal frequencies zero idles`: `compute({fA:50,fB:50,burst:100,wIdle:0,rIdle:0,nSync:2})` -> itemsRead 100, rawDepth 1 (Review Focus 1).
- `burst one`: `compute({fA:80,fB:50,burst:1,wIdle:0,rIdle:0,nSync:0})` -> rawDepth 1, grayDepth 2 (Review Focus 2).
- `steady state yes`: `compute({fA:50,fB:80,burst:120,wIdle:0,rIdle:0,nSync:2})` -> `steady.drainable === true` (Review Focus 3).
- `fractional mhz`: `compute({fA:66.667,fB:50,burst:120,wIdle:0,rIdle:0,nSync:2})` -> `itemsRead === Math.floor(120*(1000/66.667)/(1000/50))` computed with the same expression order (Review Focus 4).
- `savings pct zero`: `compute({fA:50,fB:80,burst:8,wIdle:0,rIdle:0,nSync:0})` -> grayDepth === johnsonDepth and `savingsPct === 0` (Review Focus 5).
- `validation`: `validate({fA:0,fB:-1,burst:0,wIdle:-1,rIdle:1.5,nSync:2})` -> `ok === false` with errors on fA, fB, burst, wIdle, rIdle and none on nSync; numeric strings `"80"` validate ok.

- [ ] **Step 2: Run to verify it fails**

Run: `node bin/apps/fifo_depth/test/run_tests.js`
Expected: FAIL (module not found / FD undefined).

- [ ] **Step 3: Implement `bin/apps/fifo_depth/js/model.js`**

Dual-environment header per Global Constraints. `validate` coerces numeric strings via `Number()`, checks the Global Constraints bounds, returns per-field messages (`'must be > 0'`, `'must be an integer >= 1'`, `'must be an integer >= 0'`). `compute` follows the Global Constraints operation order exactly; `savingsPct = grayDepth === 0 ? 0 : Math.round((savingsSlots/grayDepth)*1000)/1000` (fraction, not percent multiplier — the sheet stores the fraction). `EXAMPLES` holds the six cases with notes copied from the sheet's Example Cases column L.

- [ ] **Step 4: Run to verify it passes**

Run: `node bin/apps/fifo_depth/test/run_tests.js`
Expected: all tests PASS, exit 0.

- [ ] **Step 5: Commit (pathspec-only)**

```bash
git add -N bin/apps/fifo_depth/js/model.js bin/apps/fifo_depth/test/run_tests.js
git commit -m "feat(fifo_depth): calculation model with golden example-case tests" -- bin/apps/fifo_depth/js/model.js bin/apps/fifo_depth/test/run_tests.js
```

### Task 2: Calculator page (index.html, style.css, app.js)

**Files:**
- Create: `bin/apps/fifo_depth/index.html`
- Create: `bin/apps/fifo_depth/style.css`
- Create: `bin/apps/fifo_depth/js/app.js`
- Modify: none

**Interfaces:**
- Consumes: `FD.validate`, `FD.compute`, `FD.EXAMPLES` from Task 1.
- Produces: nothing later tasks consume (page only).

- [ ] **Step 1: Create the page**

`index.html`: house-style header — `<h1>FIFO Depth Calculator</h1>`, tagline "Worst-case async FIFO sizing — a faithful port of fifo_depth_calculator_v2.xlsx", an "All apps" link to `/`. Six labeled inputs with ids `in-fA,in-fB,in-burst,in-widle,in-ridle,in-nsync`, defaults 80/50/120/0/0/2. Empty result containers: `#chain`, `#verdict`, `#depths`, `#banner`, plus `#notes` and `#examples`. Load `js/model.js` then `js/app.js` with relative paths.
`style.css`: port the ddr_drills conventions (mobile-first, forest-green `#228B22` headings, table rules, `.app-header`) — copy patterns from `bin/apps/ddr_drills/style.css`, no classes that need the drills markup.
`js/app.js` (IIFE, dual-env header so `node --check` and future require work): on any input event, run `FD.validate` on the six values; if invalid, render field error text under the offending inputs; if valid, render into `#chain` (write time per item, total write time, read time per item, items read, raw depth), `#verdict` (steady-state line: rates and "YES (drainable)" or the sheet's "NO - bursts grow without bound, need flow control" — the latter also filling `#banner`), `#depths` (raw + sync margin = total, Gray depth, Johnson depth, savings slots and percent). Render `#examples` as a table from `FD.EXAMPLES`; clicking a row copies its values into the inputs and re-renders. `#notes` holds the sheet's notes paraphrased: sync margin 1x, idle-cycle duty semantics, first-word latency, no-drift policy, USE_JOHNSON elaboration rule (Gray = power of 2, Johnson = even; illegal combos fail elaboration in `fifo_async` / `gaxi_fifo_async`).

- [ ] **Step 2: Verify**

Run: `node --check bin/apps/fifo_depth/js/app.js && node --check bin/apps/fifo_depth/js/model.js && node bin/apps/fifo_depth/test/run_tests.js | tail -1`
Expected: no syntax errors; suite still PASS.
Run: `cd bin/apps/fifo_depth && python3 -m http.server 8765 &` then `curl -s localhost:8765/ | grep -c 'FIFO Depth Calculator'` (then kill the server).
Expected: 1.

- [ ] **Step 3: Commit (pathspec-only)**

```bash
git add -N bin/apps/fifo_depth/index.html bin/apps/fifo_depth/style.css bin/apps/fifo_depth/js/app.js
git commit -m "feat(fifo_depth): calculator page with live results and example cases" -- bin/apps/fifo_depth/index.html bin/apps/fifo_depth/style.css bin/apps/fifo_depth/js/app.js
```

### Task 3: Launcher page + drills header link

**Files:**
- Create: `bin/apps/launcher/index.html`
- Create: `bin/apps/launcher/style.css`
- Create: `bin/apps/launcher/js/apps.js`
- Modify: `bin/apps/ddr_drills/index.html` (header block, lines 11-13 area: add an "All apps" anchor to `/` inside `.app-header`)

**Interfaces:**
- Produces: `LAUNCHER_APPS` array rendered by index.html; each entry `{id, name, href, blurb}`.

- [ ] **Step 1: Create the launcher**

`js/apps.js` (dual-env header, global `LAUNCHER_APPS`): the array
`[{id:'ddr_drills', name:'DDR and HBM Drills', href:'ddr_drills/', blurb:'Memory-controller training: quizzes, timing parameters, and AXI walkthroughs for 11 memory technologies'}, {id:'fifo_depth', name:'FIFO Depth Calculator', href:'fifo/', blurb:'Worst-case async FIFO sizing with synchronizer margin and Gray/Johnson depth output'}]`, plus an IIFE that renders one `<a class="tile">` per entry into `#tiles` on DOMContentLoaded.
`index.html`: `<h1>RTL Design Sherpa — Apps</h1>`, `<div id="tiles"></div>`, loads `js/apps.js` (relative).
`style.css`: house look; tiles as large link cards, mobile-first.

- [ ] **Step 2: Add the "All apps" link to the drills header**

In `bin/apps/ddr_drills/index.html` `.app-header` (before the h1), insert `<a class="all-apps" href="/">All apps</a>`. Add a matching rule to `bin/apps/ddr_drills/style.css` (`.all-apps { float: right; ... }` consistent with header styling).

- [ ] **Step 3: Verify**

Run: `node --check bin/apps/launcher/js/apps.js`
Expected: no syntax error.
Run: `grep -c 'All apps' bin/apps/ddr_drills/index.html && node bin/apps/ddr_drills/test/run_tests.js | tail -1`
Expected: count >= 1; drills suite PASS.

- [ ] **Step 4: Commit (pathspec-only)**

```bash
git add -N bin/apps/launcher/index.html bin/apps/launcher/style.css bin/apps/launcher/js/apps.js
git commit -m "feat(launcher): root app picker + All-apps link in drills header" -- bin/apps/launcher/index.html bin/apps/launcher/style.css bin/apps/launcher/js/apps.js bin/apps/ddr_drills/index.html bin/apps/ddr_drills/style.css
```

### Task 4: Pages workflow restructure

**Files:**
- Modify: `.github/workflows/pages-ddr-drills.yml`

**Interfaces:**
- Consumes: all three app directories.
- Produces: deploy layout `/` = launcher, `/ddr_drills/`, `/fifo/` (spec §7).

- [ ] **Step 1: Edit the workflow**

- `name:` change to `apps pages`.
- `on.push.paths`: to `['bin/apps/**', '.github/workflows/pages-ddr-drills.yml']` (covers all three apps and the launcher).
- Test job: run both suites — `node bin/apps/ddr_drills/test/run_tests.js` and `node bin/apps/fifo_depth/test/run_tests.js` (two run steps or one joined with `&&`).
- Deploy job: replace the upload step's `path:` with a staging step:
  `mkdir -p _site && cp -r bin/apps/launcher/* _site/ && mkdir -p _site/ddr_drills _site/fifo && cp -r bin/apps/ddr_drills/* _site/ddr_drills/ && cp -r bin/apps/fifo_depth/* _site/fifo/`
  then `actions/upload-pages-artifact@v3` with `path: _site`. Check `.gitignore`: add `_site/` only if not already covered (common ignores usually are; edit the file only when needed — see Step 3).

- [ ] **Step 2: Verify locally**

Run: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/pages-ddr-drills.yml'))" && rm -rf /tmp/appsite && mkdir -p /tmp/appsite && cp -r bin/apps/launcher/* /tmp/appsite/ && mkdir -p /tmp/appsite/ddr_drills /tmp/appsite/fifo && cp -r bin/apps/ddr_drills/* /tmp/appsite/ddr_drills/ && cp -r bin/apps/fifo_depth/* /tmp/appsite/fifo/ && ls /tmp/appsite /tmp/appsite/ddr_drills /tmp/appsite/fifo | head -30`
Expected: YAML parses; staged tree contains launcher files at top level plus the two app directories with their index.html files.

- [ ] **Step 3: Commit (pathspec-only)**

```bash
git commit -m "ci(apps): stage launcher + both apps for Pages; gate on both suites" -- .github/workflows/pages-ddr-drills.yml
```

(Include `.gitignore` in the pathspec only if Step 1 actually changed it — a pathspec with no changes errors out.)

### Task 5: Integration, push, deploy verification

**Files:** none (verification only)

- [ ] **Step 1: Full local verification**

Run: `node bin/apps/ddr_drills/test/run_tests.js | tail -1 && node bin/apps/fifo_depth/test/run_tests.js | tail -1`
Expected: both PASS.

- [ ] **Step 2: Push**

```bash
git push
```
(If origin/main has moved — another session pushed — `git pull --rebase` first and re-run Step 1.)

- [ ] **Step 3: Verify the deploy**

Run: poll `gh run list --limit 3 --json databaseId,workflowName,status,conclusion --jq '[.[] | select(.workflowName=="apps pages")][0]'` until completed/success.
Then: `curl -s https://sean-galloway.github.io/RTLDesignSherpa/ | grep -c 'RTL Design Sherpa — Apps'`, `curl -s -o /dev/null -w '%{http_code}' https://sean-galloway.github.io/RTLDesignSherpa/fifo/` (expect 200), and `curl -s https://sean-galloway.github.io/RTLDesignSherpa/ddr_drills/ | grep -c 'DDR and HBM Drills'` (expect >= 1).
Expected: launcher at root, calculator at /fifo/, drills at /ddr_drills/.

- [ ] **Step 4: Report**

Summarize URLs and remind the user their `ddr-drill` memory note's live-URL line needs updating (root is now the launcher; drills live at /ddr_drills/).
