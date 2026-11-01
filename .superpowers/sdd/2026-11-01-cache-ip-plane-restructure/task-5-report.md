# Task 5 Report — cache-ip plane restructure: seam contract + CHI stub

**Date:** 2026-11-01
**Status:** complete
**Commit:** `9505cf5f30ffb5b3ddc67ebe618b4ba8223946ea`

## One-line summary

Wrote the shared fabric-seam contract doc, added an elaboration-only CHI stub
plane with a filelist + registry entry, closed the amber/jet TASK-002 vault
items, and landed the commit with all gates green.

## Deliverables

| File | What |
|---|---|
| `projects/components/cache-ip/common-ip/docs/l1_fabric_contract.md` | Single source of truth for the core→fabric plane seam: snoop in/out, `fub_axi` fill/drain, `coh_req_*` launch events, `sn_want_o` throttle, MonBus, launch-event mux discipline, MonBus `AGENT_ID`/`UNIT_ID` convention, J7 note, J8/J9/J10 forward reservations, CHI stub elaboration proof command. |
| `projects/components/cache-ip/common-ip/rtl/plane/l1_chi_plane_stub.sv` | Elaboration-only stub: seam-faithful core-facing port list matching `l1_axi4_plane`, CHI channel skeleton (`chi_rxreq_*`, `chi_rxsnp_*`, `chi_txreq_*`, `chi_txrsp_*`, `chi_txdat_*`, `chi_rxdat_*`) tied off. |
| `projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_chi_plane_stub.f` | Filelist for the stub; pulls `l1_pkg.f` and the stub source. |
| `projects/components/cache-ip/common-ip/docs/INDEX.md` | Added the contract doc to the common-ip docs index. |
| `vault/tracking/projects/components/cache-ip/amber-mesi-l1/task/closed/TASK-002.md` | Moved from `open/`; status set to `closed 2026-11-01`; closing note references contract doc + CHI stub and Task 6 as final regression gate. |
| `vault/tracking/projects/components/cache-ip/jet-mesi-l1/task/closed/TASK-002.md` | Moved from `open/`; same closure pattern; notes J7 `jet_monlite` / MSHR stream. |
| Lane/area INDEX updates | `amber-mesi-l1/task/INDEX.md`, `jet-mesi-l1/task/INDEX.md`, `amber-mesi-l1/INDEX.md`, `jet-mesi-l1/INDEX.md` counts and lists updated. |

## Elaboration proof

Command:

```bash
python3 bin/flatten_filelist.py \
    projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_chi_plane_stub.f \
    --resolve-env --absolute-paths -o /tmp/l1_chi_plane_stub_flat.f
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
    -Irtl/amba/includes -f /tmp/l1_chi_plane_stub_flat.f --top-module l1_chi_plane_stub
```

Result: **PASS** (only expected `UNUSEDPARAM` warnings from unused `l1_pkg` locals).

## Gates

| Gate | Result |
|---|---|
| `python3 bin/filelist_registry.py --check` | PASS (all areas covered, 0 broken refs) |
| `python3 bin/check_task_ids.py` | PASS (138 areas) |
| `python3 bin/check_broken_links.py --ratchet` | PASS (no file grew a broken link) |
| `.git/hooks/pre-commit` | PASS |

## Concerns

- The commit closes the vault tasks honestly: the final full amber + jet + common-ip DV and formal regression gate is explicitly noted as the restructure plan's **Task 6**, not claimed as done here.
- No functional RTL was changed; the CHI stub is tie-offs only and is not instantiated by any top.
- The pre-existing untracked/deleted files in the worktree (granite FPGA reports, deleted merlin reports) were left unstaged and are not part of this commit.
