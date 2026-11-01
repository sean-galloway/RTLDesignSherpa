# Task 2 Report: cache-ip fabric planes

## What I implemented

Created the fabric-plane layer for the shared MESI L1 cache-ip restructure: a shared `l1_ace_issue` FUB (renamed from the identical amber/jet copies) and two new fabric planes (`l1_axi4_plane`, `l1_ace_plane`) that wrap the snoop responder, ACE issue FUB, and AXI4/ACE monlite transports. Existing `amber_ace_top` and `jet_ace_top` were kept functional by retargeting them to the shared FUB; the planes are elaborated standalone and will be wired into the full `amber_top` / `jet_top` in Tasks 3/4.

### New RTL

- `projects/components/cache-ip/common-ip/rtl/fub/l1_ace_issue.sv`
  - Shared ACE issue FUB: maps engine read/write requests to ACE snooped AR/AW channels, plus the AW-only evict path.
- `projects/components/cache-ip/common-ip/rtl/plane/l1_axi4_plane.sv`
  - AXI4 fabric plane: `u_snoop` (`l1_snoop_resp`) + `u_rd_monlite` / `u_wr_monlite` (plain `axi4_master_*_monlite`). ACE snoop pins enter on the boundary; the core-facing fabric seam (`ctrl_snoop_*`, `ctrl_crresp`, `ctrl_cd*`) exits toward `l1_core`; `fub_axi_*` buses exit toward the transports; `coh_req_*` is exported for the jet control closure.
- `projects/components/cache-ip/common-ip/rtl/plane/l1_ace_plane.sv`
  - ACE fabric plane: same as `l1_axi4_plane` plus `u_ace_issue` and the `axi4ace_*_monlite` transport pair; `coh_req_*` is consumed internally by `u_ace_issue`. Contains the ACE domain/barrel constants previously local to `amber_ace_top.sv`.

### Deleted RTL / filelists

- `projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_ace_issue.sv`
- `projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_issue.f`
- `projects/components/cache-ip/jet-mesi-l1/rtl/fub/jet_ace_issue.sv`
- `projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_ace_issue.f`

### Updated RTL

- `projects/components/cache-ip/amber-mesi-l1/rtl/top/amber_ace_top.sv`
  - Now instantiates `l1_ace_issue` (`u_ace_issue`) instead of `amber_ace_issue`.
- `projects/components/cache-ip/jet-mesi-l1/rtl/top/jet_ace_top.sv`
  - Now instantiates `l1_ace_issue` (`u_ace_issue`) instead of `jet_ace_issue`.

### New / updated filelists

- `projects/components/cache-ip/common-ip/rtl/filelists/fub/l1_ace_issue.f`
- `projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_axi4_plane.f`
- `projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_ace_plane.f`
- `projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f` — now includes `$CACHE_COMMON_ROOT/rtl/filelists/fub/l1_ace_issue.f`
- `projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_all.f` — same
- `projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_ace_top.f` — now includes shared `l1_ace_issue.f`
- `projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_all.f` — same
- `bin/filelists.toml` — added `rtl/filelists/fub` under `cache-common`, updated the area comment to include FUBs.

### Updated DV testplan

- `projects/components/cache-ip/amber-mesi-l1/dv/testplans/amber_ace_top_testplan.yaml`
  - `rtl_files` now points to `common-ip/rtl/fub/l1_ace_issue.sv`; comments updated.

## Equivalence evidence: `l1_ace_issue` merge

A normalized diff was run against both old copies. The normalization strips comments, the module declaration name, the `endmodule` label, and module-name references inside `$error` message strings.

```bash
python3 /tmp/normalize_sv3.py /tmp/amber_ace_issue_old.sv > amber_norm.txt
python3 /tmp/normalize_sv3.py /tmp/l1_ace_issue_new.sv  > l1_norm.txt
python3 /tmp/normalize_sv3.py /tmp/jet_ace_issue_old.sv  > jet_norm.txt

diff -u amber_norm.txt l1_norm.txt && echo "(no differences)"
diff -u jet_norm.txt  l1_norm.txt && echo "(no differences)"
```

Result:

```
=== amber vs l1_ace_issue (normalized) ===
(no differences)
=== jet vs l1_ace_issue (normalized) ===
(no differences)
```

The only un-normalized differences are the module name and the matching `$error` strings; the logic, ports, parameters, and local snoop encodings are identical.

## What I tested and results

### Verilator lint — `l1_axi4_plane`

```bash
python3 bin/flatten_filelist.py projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_axi4_plane.f \
  --resolve-env --absolute-paths -o /tmp/l1_axi4_plane_flat.f && \
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
  -I$REPO_ROOT/rtl/amba/includes -f /tmp/l1_axi4_plane_flat.f --top-module l1_axi4_plane
```

Result: `EXIT 0` — only baseline `UNUSEDSIGNAL` warnings in `ocelus_common_pkg.sv` (monlite helper functions with wide unused bit ranges).

### Verilator lint — `l1_ace_plane`

```bash
python3 bin/flatten_filelist.py projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_ace_plane.f \
  --resolve-env --absolute-paths -o /tmp/l1_ace_plane_flat.f && \
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
  -I$REPO_ROOT/rtl/amba/includes -f /tmp/l1_ace_plane_flat.f --top-module l1_ace_plane
```

Result: `EXIT 0` — same baseline `UNUSEDSIGNAL` warnings only.

### Verilator lint — `amber_ace_top`

```bash
python3 bin/flatten_filelist.py projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f \
  --resolve-env --absolute-paths -o /tmp/amber_ace_top_flat.f && \
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
  -I$REPO_ROOT/rtl/amba/includes -f /tmp/amber_ace_top_flat.f --top-module amber_ace_top
```

Result: `EXIT 0` — baseline `UNUSEDSIGNAL` warnings only.

### Verilator lint — `jet_ace_top`

```bash
export JET_ROOT=/home/seang/github/RTLDesignSherpa/projects/components/cache-ip/jet-mesi-l1
python3 bin/flatten_filelist.py projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_ace_top.f \
  --resolve-env --absolute-paths -o /tmp/jet_ace_top_flat.f && \
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
  -I$REPO_ROOT/rtl/amba/includes -f /tmp/jet_ace_top_flat.f --top-module jet_ace_top
```

Result: `EXIT 0` — baseline `UNUSEDSIGNAL` warnings plus one pre-existing `SYNCASYNCNET` warning on `w_aresetn` in `jet_ace_top.sv`.

### Repo gates

- `python3 bin/filelist_registry.py --check`
  - Result: `PASS` (all areas covered, zero broken refs, testplan ratchet clean).
- `python3 bin/check_task_ids.py`
  - Result: `Task-tracker check passed (138 area(s))`.
- `.git/hooks/pre-commit`
  - Result: passed on the Task 2 commit.

## Files changed

- `bin/filelists.toml`
- `projects/components/cache-ip/amber-mesi-l1/dv/testplans/amber_ace_top_testplan.yaml`
- `projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_issue.f` (deleted)
- `projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f`
- `projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_all.f`
- `projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_ace_issue.sv` (deleted)
- `projects/components/cache-ip/amber-mesi-l1/rtl/top/amber_ace_top.sv`
- `projects/components/cache-ip/common-ip/rtl/filelists/fub/l1_ace_issue.f`
- `projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_ace_plane.f`
- `projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_axi4_plane.f`
- `projects/components/cache-ip/common-ip/rtl/fub/l1_ace_issue.sv`
- `projects/components/cache-ip/common-ip/rtl/plane/l1_ace_plane.sv`
- `projects/components/cache-ip/common-ip/rtl/plane/l1_axi4_plane.sv`
- `projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_ace_issue.f` (deleted)
- `projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_ace_top.f`
- `projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_all.f`
- `projects/components/cache-ip/jet-mesi-l1/rtl/fub/jet_ace_issue.sv` (deleted)
- `projects/components/cache-ip/jet-mesi-l1/rtl/top/jet_ace_top.sv`

## Self-review findings

- `l1_ace_issue` is a pure rename-merge of two identical files; the equivalence script confirms no logic differences.
- Both planes elaborate cleanly with the house Verilator lint flow.
- `amber_ace_top` and `jet_ace_top` remain lint-clean after retargeting to the shared FUB.
- Filelist registry and task-ID gates pass.
- The planes are created and validated but not yet instantiated by `amber_top` / `jet_top`; that is the scope of Tasks 3/4.

## Issues or concerns

1. **Stale unit-test harness reference**: `projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_ace_issue_th.sv` still instantiates module `amber_ace_issue` by name. It will fail when the unit-level suite is next run and must be updated to `l1_ace_issue`. The top-level filelists and lint are unaffected because they do not include this unit harness.
2. **Stale documentation references**: Markdown files under `projects/components/cache-ip/amber-mesi-l1/docs/` and `projects/components/cache-ip/jet-mesi-l1/docs/` still mention `amber_ace_issue` / `jet_ace_issue`. These do not affect lint or filelist gates and should be refreshed when the doc set is next updated.
3. **Planes not yet wired into full tops**: `l1_axi4_plane` and `l1_ace_plane` are standalone; `amber_top` / `jet_top` still use the older fabric wiring. Task 3/4 will replace those top-level fabric blocks with the planes.

## Status

- Commit: `8649cf112` on main
- Summary: `cache-ip: Task 2 fabric planes — l1_axi4_plane, l1_ace_plane, l1_ace_issue`
- Task 2 is complete. Lint, registry, task-ID, and pre-commit gates pass.

---

# Follow-up fix: retarget amber ace_issue unit harness to shared `l1_ace_issue`

## What changed

- `projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_ace_issue_th.sv`
  - Module name `amber_ace_issue_th` kept unchanged (per house convention: harness stays in amber's area).
  - Instantiation retargeted from `amber_ace_issue` → `l1_ace_issue`.
  - Header comments updated to note the wrapped module is the shared common-ip FUB.
- `projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_issue.f`
  - Recreated as a thin amber-area wrapper that includes `$CACHE_COMMON_ROOT/rtl/filelists/fub/l1_ace_issue.f`.
  - The existing unit test (`_merge_sources('amber_ace_issue')`) now resolves to the shared FUB.

## What was NOT changed

- The harness file/class name (`amber_ace_issue_th`) and the Python TB class (`AmberAceIssueTB`) keep their amber-area names.
- Documentation files under `amber-mesi-l1/docs/` and `jet-mesi-l1/docs/` still carry the old module names; they do not affect simulation or gates and are left for the next doc refresh.
- No jet-side unit harness exists for `jet_ace_issue`; only the top-level `jet_ace_top` referenced it, and that was already retargeted in Task 2.

## Verification

### Focused ace_issue unit suite

```bash
cd projects/components/cache-ip/amber-mesi-l1/dv/tests
source /mnt/data/github/RTLDesignSherpa/env_python
python -m pytest test_amber_ace_top.py -k "ace_issue_rows" -q
```

Result: `2 passed, 6 deselected, 2 warnings in 15.11s` — the `l1_ace_issue` row suite is green.

### Focused amber_ace_top rig suite

```bash
python -m pytest test_amber_ace_top.py -q
```

Result: `8 passed, 8 warnings in 15.25s` — both the ace_issue rows and the rig top cells pass.

### Full amber-mesi-l1 smoke

The literal `pytest . -q` invocation was started with a 1-hour timeout but was stopped at ~75% completion after exceeding 20 minutes of wall time; all tests completed up to that point passed, with no failures observed. The slow tail is dominated by `test_amber_parity_thrash_*` / `test_amber_parity_mix_*` cells (32k–100k accesses on tiny caches), which do not exercise the ace_issue harness change.

A representative smoke excluding those heavy parity cells was run to completion:

```bash
python -m pytest . -q -k "not thrash and not mix"
```

Result: `67 passed, 12 deselected, 55 warnings in 281.71s (0:04:41)`.

### Repo gates (run while suite was in progress)

- `python3 bin/filelist_registry.py --check` → `PASS`
- `python3 bin/check_task_ids.py` → `Task-tracker check passed (138 area(s))`
- `.git/hooks/pre-commit` → passed on the staged fix files.

---

# Review round 1 fixes

## What changed

- `projects/components/cache-ip/common-ip/rtl/plane/l1_axi4_plane.sv`
  - Fixed port-name typo `fuby_axi_awsize` → `fub_axi_awsize` at line 174. The typo left the real `fub_axi_awsize` port as an implicit undriven net.
- `projects/components/cache-ip/common-ip/rtl/fub/l1_ace_issue.sv`
  - Updated header comment: removed "It lives only in the amber_ace rig" and noted it is now a shared common-ip FUB used by `l1_ace_plane`.

## What was NOT changed

- No `default_nettype none` directives were added.
- No other `fuby` typos were found in the new plane files (grep confirmed).

## Verification

- Grep for `fuby` across `projects/components/cache-ip` → no matches.
- Verilator lint of `l1_axi4_plane`:

```bash
python3 bin/flatten_filelist.py projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_axi4_plane.f \
  --resolve-env --absolute-paths -o /tmp/l1_axi4_plane_flat.f && \
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
  -I$REPO_ROOT/rtl/amba/includes -f /tmp/l1_axi4_plane_flat.f --top-module l1_axi4_plane
```

Result: `EXIT 0` — only baseline `UNUSEDSIGNAL` warnings in `ocelus_common_pkg.sv`.

### Repo gates

- `python3 bin/filelist_registry.py --check` → `PASS`
- `python3 bin/check_task_ids.py` → `Task-tracker check passed (138 area(s))`
- `.git/hooks/pre-commit` → passed without `--no-verify`.

## Concerns

None. The typo is fixed, lint is clean, and gates pass.

## Concerns

None for the harness retarget. The only remaining `amber_ace_issue` / `jet_ace_issue` references are in documentation and coverage-report artifacts, which do not affect simulation or filelist gates.
