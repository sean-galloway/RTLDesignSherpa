<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# apbx-xbar — Open

## APBX-001 — Generalize apbx_xbar to apbx_xbar (APB4 / APB5 / mixed)
**Status:** open 2026-08-12
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
- *Naming/moves*: component dir -> `projects/components/apbx_xbar`;
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

**Done looks like:** apbx_xbar generates all legacy variants
byte-equivalent except naming with version bits '0; mixed fixture
sims green with sideband value checks; all consumers updated; docs +
filelist registry + audit clean; formal harnesses renamed and still
passing their existing modes.
