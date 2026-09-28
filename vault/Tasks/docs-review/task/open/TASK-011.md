# TASK-011: The five HAS/MAS books: qc rounds, then humanize

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-017** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** open 2026-08-20 (Sean)
**Priority:** P2

The component books queued for correctness first, voice second. This is the
`projects/components` slice of [[DOCREV-013]], decomposed to the five books
that actually exist as HAS/MAS today.

| Book | Words | qc round | humanized |
|---|---|---|---|
| Bridge MAS | — | **STOPPED 2026-09-08 by decision, not convergence**: fresh-dir rounds 1-4 (65 → 54 → 53 → 57 findings; every finding triaged and fixed; four RTL defects, all mutation-checked); Sean: "Switch please" to voice after the flat-count report | **2026-09-08**, humanize round_1, 22 pages, tag-survival 0 fatal, correctness annotations count-exact (`6408d76dd`) |
| Bridge HAS | — | same rounds 1-4 | **2026-09-08**, humanize round_1, 17 pages, same gates (`6408d76dd`) |
| Converters MAS | — | **CONVERGED 2026-08-26**: rounds 1-6 (25→30→19→14→11→7 findings; last four rounds zero RTL defects) | **2026-08-26**, humanize round_1, all 19 pages, tag-survival 0 fatal |
| APB Crossbar MAS | 7,154 (5 md) | **CONVERGED 2026-08-30**: rounds 7-15 (20→22→19→18→17→18→10→12→9; last two rounds no RTL defects) | **2026-08-30**, humanize round_2, 9 pages, tag-survival 0 fatal |
| APB Crossbar HAS | 8,179 (20 md) | rounds 7-15, same batch | **2026-08-30**, humanize round_2, 23 pages, tag-survival 0 fatal |

### Bridge status, measured 2026-09-08 -- arc complete as of `6408d76dd`

Rule 11 applies: complete as of that commit, not forever.

* **Results tree.** The fresh results dir (`~/rtl-doc-review/results`,
  `qc-kimi-k2/round_1..4`, `humanize-kimi-k2/round_1`) restarted numbering at
  round_1; the round_43/44 numbers above it in the history refer to the old
  tree and were never adjudicated. Round_1 of the fresh tree was the first
  bridge qc against a generator-synced book.
* **Trajectory 65 → 54 → 53 → 57** (round_4 had one more unit). A broken
  line-anchored counter reported round_3 as 37 and one unit as clean; the
  recount (rule 14) showed convergence had stalled at rounds 2→3. Round_4's
  findings were lower-severity (stale probe names, a units mismatch) while its
  RTL yield rose (three defects in one round). The recommendation was one more
  RTL-adjacent round; Sean chose to switch to voice. The residual is the
  humanize reviewer's to catch.
* **RTL yield of the four rounds**, each mutation-checked: BRIDGE-011
  response-FIFO overrun → misroute then stall (`c64660f47`);
  `axi4_subtractive_slave` simultaneous AW+AR lost a fault (`37e19daf`);
  `axi5_atomic_filter` duplicate B for a held DECERR (`53b6dedbf`) and B
  before the swallowed burst's WLAST (`f73698397`). Plus 7 vacuous arbitration
  tests made real and latency measured rather than asserted. Bridge 72/72 at
  FULL after the last fix.
* **Humanize round_1** ran across a machine shutdown: units 1-7 landed
  2026-09-08 15:53-18:26, the driver died mid-unit-8, and the round was
  resumed gap-fill (rule 3) the same evening for units 8-10. Units 11-12 were
  deliberately not run and the has_part_04/05 outputs not applied: all four
  were the component PRD.md and CLAUDE.md, pulled in twice by the bundler
  following the index's Related Documents links -- rule 15, fixed in
  `ebfa49d8f`. 39 book pages applied, gates in the commit message.
* **Books rebuilt at rev 1.2** (`Bridge_HAS_v1.2.pdf`, `Bridge_MAS_v1.2.pdf`)
  with a revision-history entry naming the four rounds and the four defects.

### Two problems, not one

**Three books were voice-passed without a correctness round.** Searching the
docs-review area for a bridge or converters qc round returns nothing; the
2026-08-11 humanization ran anyway. That is the failure shape
[kimi-review-rounds](../../../../handbook/authoring/kimi-review-rounds.md#the-order-correctness-until-clean-then-voice)
names outright: a voice pass rewrites every page, so voice-passing a page that
is still wrong "produces a well-written falsehood, and the rewrite makes the
error harder to spot later because it no longer reads like something copied
from stale RTL." Their qc round is therefore owed retroactively, and it is
reading prose that has already been smoothed once.

**The two APB Crossbar books have had neither pass.** Not an oversight in
judgement — a timing miss. The `apbx-xbar` doc tree was created 2026-08-12
(`95f7006f`), one day after the humanization pass ran, and nothing has swept
it since.

### Content added after both passes

Written 2026-08-19/20 (`cf3aa7da`), so it postdates every prior round:

- apbx MAS ch1 — APB5 parity section; the generated-vs-thin parameter split
- apbx MAS ch3 — generator arguments the CLI does not expose
- Converters MAS §3.4 — `axi4_to_apb4_shim` parameter table

The converters case is the one to watch: an un-humanized table now sits inside
an otherwise-humanized file, which is where a voice mismatch will show first.

That same commit corrected parameter tables that had documented
`NUM_MASTERS`/`NUM_SLAVES` — parameters no module has — and defaults that were
simply wrong (`AXI_ADDR_WIDTH` 64 vs the actual 32). Both were found by reading
the RTL, not the docs. Treat that as evidence about the qc round's likely yield
on books nobody has checked against source: aim it at parameter tables,
defaults, and module names first.

**Work:**
- [ ] qc round per book, re-run until a round returns nothing actionable or
      only false positives. One round is not a clean bill of health.
- [ ] Integrate findings, verifying each against RTL before acting — a
      mis-packaged bundle produces confident-but-wrong findings.
- [ ] Only then humanize, using
      `docs/kimi_humanization_style_guide_has_mas.md` (the guide the
      2026-08-11 HAS/MAS pass used), gated on `verify_structure.py`.
- [ ] Re-verify the qc fixes survived the voice pass.
- [ ] Rebuild all five books; confirm LoF/LoT/LoW still populate — caption
      encoding (`: caption`, `Figure N:`) drives them, and a rewrite that
      drops it silently breaks book generation.

**Note:** the apbx books are small enough to send un-split. Sizes above are
markdown word counts, not the built page counts.
