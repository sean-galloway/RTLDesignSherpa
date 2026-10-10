# mem-ctrl-ip Phase 1 — Move to research/common/product Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Relocate the three memory controllers under `mem-ctrl-research-ip/`, establish the `mem-ctrl-common-ip/` skeleton (docs included), and rewrite every living path reference — with the tree green at the end and zero RTL edits.

**Architecture:** Pure `git mv` + scripted reference rewrite. Phase 1 of spec `docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md`; Phase 2 (layer extraction) is explicitly NOT this plan — it gets its own plan after this lands.

**Tech Stack:** git, bash/sed, ripgrep via `git grep`, verilator lint via the repo Makefile flow, pytest/cocotb via `venv-cocotb2`, `bin/check_task_ids.py`.

**Spec:** `docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md` (§4 Phase 1, §5 boundary rules, §8 success criteria)

## Global Constraints

- **Zero RTL content changes.** Not one byte inside any `.sv` file's logic may change; path rewrites in comments/docs/filelists only. (Spec §5: "No RTL behavior changes in Phase 1.")
- **Old→new path mapping, verbatim:**
  - `projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2` → `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2`
  - `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3` → `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3`
  - `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4` → `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4`
  - `projects/components/mem-ctrl-ip/docs/` → `projects/components/mem-ctrl-ip/mem-ctrl-common-ip/docs/`
- **Module names do not change** (`scoria_*`, `pumice_*`, `andesite_*` stay rock-prefixed; only paths move).
- **Multi-agent trunk:** `git status` before every add; pathspec-limited adds only; foreign staged/modified files never touched; commit with `export PATH="$(pwd)/venv/bin:$PATH"` (hooks need venv python3.12); never `--no-verify`.
- **Dated history is immutable:** `docs/superpowers/specs/*`, `docs/superpowers/plans/*` are dated snapshots — never rewrite paths inside them.
- **Reference-rewrite pattern (prefix-agnostic):** match the repo-relative substring `mem-ctrl-ip/<mc-name>` regardless of `$REPO_ROOT/`, `$REPO/`, `$(pwd)/`, or bare-prefix form; replace with `mem-ctrl-ip/mem-ctrl-research-ip/<mc-name>`.
- **DV environment:** `source venv-cocotb2/bin/activate && export PYTHONPATH="$(pwd)/bin"` (cocotb 2.1.0); pytest-timeout is NOT installed — no `--timeout` flag.

## Review Focus

1. **Generated artifacts with baked paths** — PeakRDL outputs, kmap/gen-generated headers, committed build reports under `reports/` may embed old paths; a missed one breaks builds silently while all greps of source pass.
2. **check_task_ids.py area resolution with deeper nesting** — `vault/Tasks/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/<mc>` must still parse as an area (grouping vs area distinction in `vault/Tasks/INDEX.md`); a misfiled area invisibly drops its items from rollups.
3. **The lint registry in `projects/components/Makefile`** — component entries are path-keyed (`lint-mem-ctrl-ip/<mc>`); a stale entry makes `make lint-all` fail for everyone.
4. **CRLF/UTF-16 files under sed** — Windows-edited scripts (e.g. `bin/*.sh`, uart tooling history) can be corrupted by blind `sed -i`; file-type check precedes batch rewrite.
5. **Symlinks into the moved trees** — a symlinked script outside `mem-ctrl-ip/` pointing at an old inner path survives `git mv` as a dangling link; `find -type l` before and after the move.

---

### Task 1: Scaffold the three-area tree and git mv the controllers

**Files:**
- Create: `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/` (via git mv)
- Create: `projects/components/mem-ctrl-ip/mem-ctrl-common-ip/README.md`, `mem-ctrl-common-ip/rtl/{macro,fub,includes}/.gitkeep`, `mem-ctrl-common-ip/dv/.gitkeep`
- Modify: nothing (pure move)

**Interfaces:**
- Consumes: existing `projects/components/mem-ctrl-ip/{pumice-ddr2-lpddr2,scoria-ddr3-lpddr3,andesite-ddr4-lpddr4,docs}`
- Produces: the exact directory layout of spec §1, minus the six `mc_*` layers (Phase 2); every later task rewrites references assuming this layout

- [ ] **Step 1: Confirm the trunk is quiet for the move set**

Run: `git status --short -- projects/components/mem-ctrl-ip/ projects/fpga-systems/Genesys2/mem-ctrl-ip/ vault/Tasks/`
Expected: no foreign modifications inside the move set (activity in `rtl/amba`, `dma-ip/stream` etc. is fine — disjoint). If the move set is dirty with someone else's work, STOP and report.

- [ ] **Step 2: Create the common skeleton + move the docs**

```bash
cd projects/components/mem-ctrl-ip
mkdir -p mem-ctrl-common-ip/rtl/{macro,fub,includes} mem-ctrl-common-ip/dv
touch mem-ctrl-common-ip/rtl/{macro,fub,includes}/.gitkeep mem-ctrl-common-ip/dv/.gitkeep
git mv docs mem-ctrl-common-ip/docs
```

Write `mem-ctrl-common-ip/README.md` (5-10 lines): what lives here eventually (the six `mc_*` layers per spec §1), that it is intentionally a skeleton until Phase 2, and a link to the spec.

- [ ] **Step 3: git mv the three controllers**

```bash
git mv pumice-ddr2-lpddr2 mem-ctrl-research-ip/pumice-ddr2-lpddr2
git mv scoria-ddr3-lpddr3 mem-ctrl-research-ip/scoria-ddr3-lpddr3
git mv andesite-ddr4-lpddr4 mem-ctrl-research-ip/andesite-ddr4-lpddr4
```

- [ ] **Step 4: Verify layout matches spec §1**

Run: `find projects/components/mem-ctrl-ip -maxdepth 2 -type d | sort`
Expected: `mem-ctrl-research-ip/{pumice-ddr2-lpddr2,scoria-ddr3-lpddr3,andesite-ddr4-lpddr4}`, `mem-ctrl-common-ip/{docs,rtl,dv}`, no leftover `{pumice,scoria,andesite}-*` at the old level; `git status --short` shows pure renames (R) plus the new skeleton files.

- [ ] **Step 5: Commit (skeleton + moves together, nothing else)**

```bash
export PATH="$(pwd)/venv/bin:$PATH"
git add projects/components/mem-ctrl-ip/
git commit -m "refactor(mem-ctrl): move 3 MCs under mem-ctrl-research-ip/, scaffold mem-ctrl-common-ip

Phase 1 of the research/common/product reorg (spec: docs/superpowers/specs/
2026-10-09-mem-ctrl-ip-reorg-design.md). Pure git mv + skeleton; reference
rewrites land in the following commits."
```

---

### Task 2: Rewrite path references inside the moved trees

**Files:**
- Modify: all files under `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/**` and `projects/components/mem-ctrl-ip/mem-ctrl-common-ip/docs/**` containing the old path literals (filelists `.f`, `bin/*.sh`, `dv/**/*.py`, docs `*.md`, `regs/`, Makefiles)

**Interfaces:**
- Consumes: Task 1's layout
- Produces: moved trees with zero old-path literals; `verilator --lint-only -f` filelists that resolve again

- [ ] **Step 1: Inventory + file-type check**

```bash
git grep -l -E 'mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)' -- projects/components/mem-ctrl-ip/ > /tmp/move_refs.txt
wc -l /tmp/move_refs.txt
file $(cat /tmp/move_refs.txt) | grep -Ev 'ASCII|UTF-8|POSIX' || echo "all plain text"
```

Expected: an inventory count (hundreds of files is normal — most are `.f` filelists with `$REPO_ROOT` literals); the `file` check prints nothing but plain-text kinds, or lists the exceptions to handle by hand.

- [ ] **Step 2: Scripted rewrite over the moved trees**

```bash
xargs -a /tmp/move_refs.txt sed -i -E 's#projects/components/mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)#projects/components/mem-ctrl-ip/mem-ctrl-research-ip/\1#g'
```

Note: prefix-agnostic by design — it rewrites the repo-relative substring after any `$REPO_ROOT/`, `$REPO/`, or bare form.

- [ ] **Step 3: Grep gate — zero old literals in moved trees**

```bash
git grep -n -E 'mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)' -- projects/components/mem-ctrl-ip/
```

Expected: empty output. If hits remain, classify each: missed prefix form (extend the sed), or dated-history rule violation (should not exist under mem-ctrl-ip — none of it is docs/superpowers).

- [ ] **Step 4: Compile proof — scoria lint closure resolves**

```bash
export PATH="$(pwd)/venv/bin:$PATH"
make lint-mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3
```

(If the Makefile registry still names the old path and the target doesn't exist yet, run the underlying verilator lint directly per `rtl/filelists/scoria_all.f`'s header comment; the registry fix is Task 3, and this step only proves the rewritten filelists resolve.)

Expected: verilator lint completes (warnings at pre-move levels, no *file-not-found* errors).

- [ ] **Step 5: Commit**

```bash
export PATH="$(pwd)/venv/bin:$PATH"
git add -u projects/components/mem-ctrl-ip/
git commit -m "refactor(mem-ctrl): rewrite path literals inside moved research trees

Scripted sed over filelists/bin/dv/docs/regs; repo-relative substring so
\$REPO_ROOT/\$REPO/bare prefixes all rewrite. Lint closure for scoria
resolves = filelists healthy."
```

---

### Task 3: External references — harness, formal, registries, living docs

**Files:**
- Modify: `projects/components/Makefile` (lint COMPONENT registry), `projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/**` (filelists, `host/*.py`, `bin/`, `Makefile`, `docs/`), `formal/{scoria,pumice,andesite}/**/Makefile` + formal harness path refs, `projects/components/mem-ctrl-ip/README.md`, `docs/DOCUMENTATION_INDEX.md`, `vault/repo-wide-projects/**`
- Do NOT modify: `docs/superpowers/{specs,plans}/*` (dated history)

**Interfaces:**
- Consumes: Tasks 1–2
- Produces: repo-wide, living-tree references all point at the new layout; `make lint-all` registry consistent

- [ ] **Step 1: Inventory external references**

```bash
git grep -l -E 'mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)' -- . ':(exclude)projects/components/mem-ctrl-ip/' ':(exclude)docs/superpowers/' ':(exclude)*reports*' > /tmp/ext_refs.txt
cat /tmp/ext_refs.txt
```

Expected: the classes listed in Files above. Anything under `stats/`, `obj_dir/`, `.ast-cache/` is generated junk — note and exclude (add to the exclude list, do not rewrite).

- [ ] **Step 2: Rewrite**

```bash
xargs -a /tmp/ext_refs.txt sed -i -E 's#projects/components/mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)#projects/components/mem-ctrl-ip/mem-ctrl-research-ip/\1#g'
```

- [ ] **Step 3: Update the lint registry**

Read `projects/components/Makefile`; find the component/lint entries for the three MCs; update each to the `mem-ctrl-research-ip/` path. Run: `make -n lint-all | grep -c 'mem-ctrl'` to confirm the three still appear (dry-run only; full lint-all is Task 5).

- [ ] **Step 4: Rewrite `projects/components/mem-ctrl-ip/README.md`**

New content describes the three-area layout (research/common/product per spec §1), notes product does not exist yet, links the spec. 15-25 lines; follow the repo README voice.

- [ ] **Step 5: Move the vault/repo-wide-projects mirror**

```bash
git mv vault/repo-wide-projects/projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2 vault/repo-wide-projects/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2
git mv vault/repo-wide-projects/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3 vault/repo-wide-projects/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3
git mv vault/repo-wide-projects/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4 vault/repo-wide-projects/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4
```

Fix any relative links inside the three moved INDEX.md files (`../../../` depth increased by one).

- [ ] **Step 6: Repo-wide grep gate**

```bash
git grep -n -E 'mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)' -- . ':(exclude)docs/superpowers/' ':(exclude)*reports*' ':(exclude)stats/' ':(exclude)obj_dir/' ':(exclude).ast-cache/'
```

Expected: empty. Remaining hits allowed ONLY under `docs/superpowers/` (dated history).

- [ ] **Step 7: Commit**

```bash
export PATH="$(pwd)/venv/bin:$PATH"
git add -u && git add projects/components/mem-ctrl-ip/README.md
git commit -m "refactor(mem-ctrl): rewrite external references to research-ip paths

Harness (Genesys2/scoria), formal Makefiles, lint registry, living docs,
repo-wide-projects mirror. Dated docs/superpowers history left untouched."
```

(If `git add -u` picks up foreign agents' modifications to files outside this task — check `git status` first; if so, add the explicit file list from /tmp/ext_refs.txt + README instead.)

---

### Task 4: Vault task areas mirror the new tree

**Files:**
- Move: `vault/Tasks/{pumice-ddr2-lpddr2,scoria-ddr3-lpddr3,andesite-ddr4-lpddr4}` → `vault/Tasks/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/<same>`; `vault/Tasks/memory-controllers/` → `vault/Tasks/projects/components/mem-ctrl-ip/memory-controllers/`
- Modify: `vault/Tasks/INDEX.md` (Areas table rows for the three MCs + memory-controllers row)
- Do NOT modify: item file contents beyond path references (status/history text is immutable record; only path literals inside them get the same sed treatment as Task 2 if any)

**Interfaces:**
- Consumes: Task 1 layout
- Produces: vault areas discoverable at their new paths; `bin/check_task_ids.py` full run green

- [ ] **Step 1: Move the areas**

```bash
mkdir -p vault/Tasks/projects/components/mem-ctrl-ip/mem-ctrl-research-ip
git mv vault/Tasks/pumice-ddr2-lpddr2 vault/Tasks/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2
git mv vault/Tasks/scoria-ddr3-lpddr3 vault/Tasks/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3
git mv vault/Tasks/andesite-ddr4-lpddr4 vault/Tasks/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4
git mv vault/Tasks/memory-controllers vault/Tasks/projects/components/mem-ctrl-ip/memory-controllers
```

- [ ] **Step 2: Path literals inside moved vault files**

```bash
git grep -l -E 'mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)' -- vault/ | xargs -r sed -i -E 's#projects/components/mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)#projects/components/mem-ctrl-ip/mem-ctrl-research-ip/\1#g'
```

- [ ] **Step 3: Update `vault/Tasks/INDEX.md` Areas table**

The three MC rows' links become `[pumice-ddr2-lpddr2](projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2/INDEX.md)` (same for scoria/andesite); the `memory-controllers` row (if present) updates likewise. Add one sentence near the table noting the 2026-10-09 reorg mirroring `mem-ctrl-ip/`.

- [ ] **Step 4: Checker gate**

```bash
export PATH="$(pwd)/venv/bin:$PATH"
python3 bin/check_task_ids.py
```

Expected: full run passes (91+ areas), zero warnings. A failure here is almost always the grouping-vs-area distinction in the INDEX (Review Focus #2) — the checker names the offending path; fix the INDEX row, not the checker.

- [ ] **Step 5: Commit**

```bash
export PATH="$(pwd)/venv/bin:$PATH"
git add vault/Tasks/ && git commit -m "vault(tasks): mirror mem-ctrl-ip reorg — MC areas under mem-ctrl-research-ip

Areas moved; INDEX table relinked; check_task_ids full-run green."
```

---

### Task 5: Full green run — lint, DV suites, final gate

**Files:**
- Modify: nothing expected; this task exists to catch stragglers (fix + fold into its commit if found)

**Interfaces:**
- Consumes: Tasks 1–4
- Produces: Phase 1 declared done; the tree ready for Phase 2 planning

- [ ] **Step 1: Lint all three moved controllers**

```bash
export PATH="$(pwd)/venv/bin:$PATH"
make lint-mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2
make lint-mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3
make lint-mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4
```

Expected: each completes at pre-move warning levels; no missing-file errors.

- [ ] **Step 2: DV suites for the three MCs**

```bash
source venv-cocotb2/bin/activate && export PYTHONPATH="$(pwd)/bin"
# run each MC's dv suite per its dv/README or Makefile convention (pytest)
```

Expected: all suites green at pre-move pass counts. (Verilator is the default simulator; do not set SIM=icarus — see tooling BUG-016.)

- [ ] **Step 3: Final repo-wide grep gate + task tracker**

```bash
git grep -n -E 'mem-ctrl-ip/(pumice-ddr2-lpddr2|scoria-ddr3-lpddr3|andesite-ddr4-lpddr4)' -- . ':(exclude)docs/superpowers/' ':(exclude)*reports*' ':(exclude)stats/' ':(exclude)obj_dir/' ':(exclude).ast-cache/'
export PATH="$(pwd)/venv/bin:$PATH" && python3 bin/check_task_ids.py 2>&1 | tail -3
find projects/components/mem-ctrl-ip -type l -o -type d -name 'mem-ctrl-research-ip' | head
```

Expected: grep empty; checker "passed"; no dangling symlinks in the moved tree.

- [ ] **Step 4: Report + close out**

Report to the owner: files moved, reference counts rewritten (from Task 2/3 inventories), lint/DV results, commit list. Phase 1 is complete; Phase 2 (common-layer extraction) plans next, per spec §4.

---

## Self-Review Notes

- **Spec coverage:** §4 Phase 1 tasks all map (move→T1, refs→T2/T3, vault→T4, green→T5). §6 non-goals enforced via constraints (no RTL edits, no docs/superpowers rewrites). §8 success criteria are T5's gates.
- **Phase 2 deliberately absent:** spec §4 Phase 2 gets its own plan(s) after this lands — extraction with live customers is a different shape of work (TDD per layer, diff-invisible moves) and would bloat this plan past usefulness.
- **Proportion:** five tasks, one phase, each independently committable and verifiable; longest step is a suite run.
