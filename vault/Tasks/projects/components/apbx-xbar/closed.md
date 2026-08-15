<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# apbx-xbar — Closed (completed)

---

## APBX-002 — Formal coverage for the APB4/APB5 version gating
**Status:** closed 2026-08-14 — `formal/apbx_xbar/apbx_xbar_thin_mixed/`,
prove and cover both PASS

A mixed build (m0=APB4, m1=APB5, s0=APB5, s1=APB4) with the sideband
buses as free inputs, proving the gate on both ends exhaustively rather
than by sampling:

- **A** — an APB4 slave is never driven with sideband.
- **B** — an APB4 master never receives completer sideband.
- **C** — an APB5 slave sees `'0` while no APB5 master has selected, so
  an APB4 master cannot contribute either.
- **cover** — the legal pairing (m1 → s0) really does carry nonzero
  sideband, reached in 4 steps. Without it, A–C could pass on a fabric
  that moved nothing.

**Property C is worth reading before writing a similar one.** The first
version stated it against `PSEL` and the solver refuted it in four
steps: grants persist from command acceptance through response
completion, so an APB5 master can still hold the grant — and still
legitimately drive sideband — in a cycle where it has dropped `PSEL`.
The refutation was correct; the property was wrong. Restating it
against `dut.arb_gnt_id` then hit two front-end limits (no dynamic
index into a parameter, no hierarchical reference resolution), so it
ended up as a sticky flag at the boundary, which needs no internal
names and is a stronger statement for it.

Like the sibling apbx_xbar proofs, this is not wired into
`formal/Makefile`'s targets; run it with `sby -f` in its directory.

## APBX-001 — Generalize apbx_xbar to apbx_xbar (APB4 / APB5 / mixed)
**Status:** closed 2026-08-14 — all acceptance criteria met
**Priority:** P2
**Owner:** TBD

Owner request: "update apbx_xbar to apbX_xbar and have it be apb4 or
apb5 and possibly mixed." Lowercase `apbx` in module/file names per
house style; the X reads as the protocol-version wildcard.

**Current shape (surveyed):** parameterized MxS core
`apbx_xbar_thin` (203 lines, vectored discrete APB4 signals, WRR
arbiter thresholds, runtime SLAVE_ENABLE/BASE/LIMIT decode) + a
Python generator (`bin/apbx_xbar_generator.py`, 574 lines +
`generate_xbars.py`) emitting sized variants (1to1/1to4/2to1/2to4)
and `_wrap` wrappers. Consumers outside the component: RLB's own
`apbx_xbar_rlb_1to10.sv` (instantiates the thin core),
`rtl/integ_amba/examples/apbx_xbar_monitored.sv`, env_python's
`APB_XBAR_ROOT`, `bin/filelists.toml` area, filelist registry, docs
assets (mmd/svg) and overview pages, `.claude/settings.json`.

**Design:**

- *Core* `apbx_xbar_thin`: keep the APB4 signal set and routing; add
  per-port version parameters `MST_APB5[M-1:0]` / `SLV_APB5[S-1:0]`
  (default '0 = pure APB4 = today's behavior) and the APB5 superset
  sideband as vectored ports with user-width params (AUW/WUW/RUW/BUW,
  default 1): requester-direction `pauser/pwuser` (master in, slave
  out), completer-direction `pwakeup/pruser/pbuser` (slave in, master
  out). Sideband rides the SAME select/grant muxes as the base
  signals — no new control logic. Version-gating is contribution
  gating: an APB4 master contributes '0 sideband into the fabric; an
  APB4 slave's completer sideband reads as '0; parameters let
  synthesis prune. Mixed operation therefore needs no converters:
  APB5 keeps the APB4 transfer protocol (same lesson as the bridge's
  axi4_to_apb5_shim — see the converters MAS).
- *Generator*: per-port version lists in the config
  (`masters = ["apb4","apb5",...]`), variants named
  `apbx_xbar_MtoS`; wrappers expose ONLY the enabled versions'
  sideband on each port (bridge-style surface discipline), tying the
  rest inside. All-apb4 configs regenerate today's surfaces exactly
  (modulo the module rename) — that is the regression bar.
- *Naming/moves*: component dir -> `projects/components/apbx-xbar`;
  all `apbx_xbar_*` modules/files/filelists/tests ->
  `apbx_xbar_*`; consumers updated (RLB rlb_1to10 instantiation +
  its own module name stays RLB-owned, integ example, env_python
  APB_XBAR_ROOT, filelists.toml area entry + registry, docs assets +
  pages, vault repo-wide INDEX).
- *DV*: rename existing suites; add a MIXED test — apb5 master +
  one apb4 + one apb5 slave: drive PAUSER/PWUSER values, assert they
  arrive at the apb5 slave and are absent (tied) at the apb4 slave;
  drive PWAKEUP/PRUSER/PBUSER at the apb5 slave and assert
  master-side visibility only when the master is apb5. CocoTBFramework
  has APB4 + APB5 BFMs.
- *Docs*: component README/PRD + rtl-amba pages + assets renamed;
  spec-doc standards apply (mermaid diagrams, wavedrom waveforms).

**Progress (2026-08-12):** step 1 (rename, f28581b3) and step 2a
(thin core) LANDED. apbx_xbar_thin carries the APB5 superset sideband
behind per-port `MST_APB5`/`SLV_APB5` masks (fixed [31:0] so -G
overrides pass clean; grant-path index cast 5'(mst_id)); request
sideband rides the slave mux gated by master-version AND
slave-version, completer sideband rides the demux gated per pairing —
verified by test_apbx_xbar_thin_mixed.py (M=2/S=2, master1+slave0
APB5): all four pairings, leak checks both directions against
deliberately tied-high APB4-port pins. Legacy 4-variant suite still
green. Consumer instantiations (formal harness, integ_amba monitored
example) tie the new pins. Bonus closure fix: apbx_xbar_thin.f was
missing its weighted-arbiter dependency. REMAINING: step 2b — the
generated MtoN variants use a cmd/rsp fabric (apb4_slave -> routing ->
apb4_master), and apb5_slave already emits cmd_pauser on its cmd bus:
per-port versions there mean swapping apb5_slave/apb5_master at
versioned ports and widening the cmd/rsp routing; then wrappers,
generator config, regen, docs.

**Progress (2026-08-12, cont.):** step 2b LANDED + dir renamed to
projects/components/apbx-xbar (hyphenated, house style; module names
keep underscores). Generator takes master_versions/slave_versions
('apb4'|'apb5') + name_suffix; apb5 ports swap in apb5_slave /
apb5_master boundary IP (1-bit user widths, parity feature pins tied
off — ENABLE_PARITY=0 — wakeup_request '0 / wakeup_pending open); the
cmd/rsp fabric grows pauser/pwuser (cmd) and pruser/pbuser (rsp) only
on versioned ports, gated per pairing in all three routing shapes
(M>1 arbitration, M==1/N>1 decode, 1-to-1). PWAKEUP toward the master
is regenerated by the master-side apb5_slave; the external
completer's PWAKEUP terminates at the slave-side apb5_master.
apbx_xbar_2to2_mixed generated (in rtl/ with banner) + its filelist +
sim test: all four pairings green with sideband value/leak checks and
structural no-pins-on-apb4-ports asserts. Full 6-test suite green.
Regen caveat RESOLVED (2026-08-12): the generator now emits the
final form — SPDX banner, `include reset_defs.svh, ALWAYS_FF_RST /
RST_ASSERTED macros — and generate_xbars.py writes straight into
rtl/ with the baseline 64KB windows. All five variants regenerated
as the new baseline (only comment/banner-class deltas plus one
leftover raw always_ff upgraded to the macro); regeneration is
idempotent (regen twice = identical tree) and needs zero
post-processing. Remaining: component docs (README, rtl-amba pages,
mermaid/wavedrom per spec-doc-standards).

**Done looks like:** apbx_xbar generates all legacy variants
byte-equivalent except naming with version bits '0; mixed fixture
sims green with sideband value checks; all consumers updated; docs +
filelist registry + audit clean; formal harnesses renamed and still
passing their existing modes.

**Closed 2026-08-14.** Final item was the component documentation
(02ed4c40). Acceptance re-verified at close:

- *Legacy variants byte-equivalent with version bits '0* — regeneration
  is idempotent; `generate_xbars.py` then `git status rtl/` gives no
  output.
- *Mixed fixture sims green with sideband value checks* — full 6-test
  suite passes, including value AND leak checks plus a structural
  no-pins-on-APB4-ports assert.
- *All consumers updated* — no `apb_xbar` references remain anywhere;
  RLB, integ_amba example, filelists.toml, env_python and the filelist
  registry all carry the new name.
- *Docs* — `docs/markdown/rtl-amba/apbx/` (new area; both pages moved
  from `apb4/` as git renames), component README, and cross-links from
  the apb4/apb5 READMEs. Mermaid render-verified, four ASCII waveforms
  converted to WaveDrom per the authoring standards.
- *Filelist registry + audit clean* — `filelist_registry.py --check`
  reports `apbx_xbar 10 modules, 10 covered, 0 uncovered, 0 broken refs`.
- *Formal harnesses renamed and still passing* — updated for the new
  sideband ports (inputs tied, outputs open); `apbx_xbar_thin` prove
  task passes.

Deliberately out of scope, carried forward as APBX-002 and APBX-003.
