# TASK-031: delta re-home — noc-ip/delta → fabric-gen-ip/delta (component/spec split)

**Status:** CLOSED 2026-10-12, in the re-home commit. Owner directive ("make it
so number one"): delta the **AXI4-Stream crossbar generator** never belonged in
the NoC lane; it is a live interconnect generator and now sits with its
siblings at `projects/components/fabric-gen-ip/delta/` (apbx-xbar, bridge,
delta). The aspirational DELTA mesh NoC draft (4×4 mesh, VCs, XY routing — no
RTL, never implemented) was split OUT of the component into
`projects/components/noc-ip/delta_spec/`, keeping `noc-ip/` as a reserved
placeholder lane.
**Priority:** P3
**Filed from:** owner review of the delta identity question ("shouldn't delta
be in fabric-gen-ip?") — confirmed against RTL before moving.

What the commit contains:

- `git mv` of the component and of `docs/delta_spec/`; the NoC-flavored
  `CLAUDE.md`, `docs/generate_pdf.sh`, and the two rendered spec PDFs/DOCX
  moved with the spec into `noc-ip/` (they document the NoC, not the
  crossbar). `delta/docs/` dissolved.
- New component `CLAUDE.md` written for the crossbar generator (verified
  facts: tdest decode, per-slave RR, packet-atomic grant, combinational data
  mux, flat-only).
- `noc-ip/CLAUDE.md` rewritten as the NoC draft's agent guide with an
  explicit "not implemented" status and the fabric-gen-ip pointer.
- `noc-ip/README.md` rewritten: lane reserved; delta_spec = unimplemented
  design draft; component lives in fabric-gen-ip.
- ~27 path references updated (root/projects/components READMEs, both
  indexes, component-status-matrix, components/Makefile comment,
  docs/markdown/overview.md, bin/filelists.toml + filelist_registry.py,
  env_python, hive-serv + hpet references, vault mirror INDEX).
- Stale "retired 2026-09-27" status rows corrected to Active/in-progress in
  every index that claimed them.
- Tree-topology claims scrubbed: README feature bullet, PRD REQ-GEN-002,
  PRD §2.2 heading, PRD milestone lines, NFR-PERF-003 — all annotated
  "retired 2026-10-12, flat only" (generator's `--topology tree` prints
  "not yet implemented in framework version").
- PRD §16 (NoC spec PDF generation) replaced with a pointer to
  `noc-ip/generate_pdf.sh`; that script's REPO_ROOT depth and output paths
  fixed for its new home.
- Vault mirror moved to
  `vault/repo-wide-projects/projects/components/fabric-gen-ip/delta/` and its
  INDEX paths fixed.
- History left untouched per convention: dropped/closed vault records that
  mention the old path (coverage TASK-003, tooling BUG-011, docs-review
  ISSUE-001) keep it as recorded.

Not done (deliberately): delta still has no `dv/` suite (the pre-existing
TODO stands); the NoC draft was neither deleted nor promoted — it is design
groundwork the owner may want for a future NoC.
