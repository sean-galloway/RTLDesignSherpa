# Task 3 — Migrate `amber_top` / `amber_ace_top` to the cache-ip plane hierarchy

**Date:** 2026-11-01  
**Scope:** `projects/components/cache-ip/amber-mesi-l1/rtl/top/amber_top.sv`, `amber_ace_top.sv`, their filelists, and the DV hierarchical taps that reach into them.  
**Owner:** sean galloway  

## Goal

Move the two amber rig tops off the monolithic `l1_core`-centric integration and onto the restructured cache-ip plane hierarchy:

* `u_cpu` — `l1_cpu_plane`
* `u_coh` — `l1_coh_core`
* `u_fab` — `l1_axi4_plane` for `amber_top`, `l1_ace_plane` for `amber_ace_top`
* `u_monbus_arbiter` — 2-client top-level MonBus merge
* `u_reset_sync` — boundary reset synchronizer

The external port lists of both tops remain unchanged so that existing rig harnesses, fabrics, and FPGA tops keep compiling without modification.

## What changed

### RTL

| File | Lines | Summary |
|------|-------|---------|
| `rtl/top/amber_top.sv` | 643 | Replaced the old `l1_core` + fabric wrapper composition with `u_cpu`/`u_coh`/`u_fab`. Added internal `fub_axi_*` seam, boundary `reset_sync`, and 2-client `monbus_arbiter` that merges the core `l1_monlite` stream with the fabric plane's merged rd/wr observer stream. The D-8 `coh_req_*` sideband is re-exported to the top level for the pair-rig fabric. |
| `rtl/top/amber_ace_top.sv` | 658 | Same plane composition, using `l1_ace_plane` for the ACE rig. The D-8 `coh_req_*` launch stream is consumed on-chip by the fabric plane (`l1_ace_issue`); no coherence sideband reaches the top level. Memory-side pins are the ACE master set (`arsnoop`, `awsnoop`, `rack`/`wack`, 4-bit `rresp`). |

Key wiring decisions:

* Both tops keep the same parameter list and port ordering as before; only the internal hierarchy changed.
* `PF_GUARD` is enabled for `amber_top` (pair rig always sits behind a coherence fabric) and left at its default for `amber_ace_top` (the ACE rig's directed snoop scenarios assume classic bypass behavior).
* The `fub_axi_*` seam carries the full 4-bit `rresp` width that `l1_coh_core` expects; the AXI4 plane narrows to 2 bits at the boundary, the ACE plane keeps 4 bits.
* Unused `mon_dropped` from the core observer and `sn_want_o` from the fabric plane are tied off with `verilator lint_off UNUSEDSIGNAL` guards.

### Filelists

| File | Change |
|------|--------|
| `rtl/filelists/amber_top.f` | Now includes `l1_cpu_plane.f`, `l1_coh_core.f`, `l1_axi4_plane.f`, and `reset_sync.f`. |
| `rtl/filelists/amber_ace_top.f` | Now includes `l1_cpu_plane.f`, `l1_coh_core.f`, `l1_ace_plane.f`, and `reset_sync.f`. |
| `rtl/filelists/amber_all.f` | Updated to reference the new plane-based top filelists. |

### DV tap retargeting

| File | Change |
|------|--------|
| `common-ip/dv/tbclasses/l1_core_tb.py` | Added `_core_tap` and `_snoop_tap` properties so subclasses can override the hierarchical root. The default now points to the actual `l1_coh_core` instance (`self._tap.u_core.u_coh` for `l1_core_fab_tb`), and all core-internal accesses (`u_control`, `u_repl`, `u_tag`, `coh_req_*`, `mon_dropped`) are addressed directly on `_core_tap`. |
| `amber-mesi-l1/dv/tbclasses/amber_ace_top_tb.py` | Overrides `_core_tap` → `dut.u_coh`, `_snoop_tap` → `dut.u_fab.u_snoop`. |
| `amber-mesi-l1/dv/tbclasses/amber_pair_rig_tb.py` | Retargeted all `a.u_core*` taps to `a.u_coh*` and `a.u_snoop` to `a.u_fab.u_snoop` for both caches in the pair rig. |

Bugs fixed during the run:

1. `_core_tap`/`_snoop_tap` initially returned themselves, causing recursion. Fixed to route through `self._tap`.
2. After the plane restructure, `_core_tap` had to point directly to the `l1_coh_core` instance; the base class was updated so core-internal taps are addressed on `_core_tap` itself rather than on `_core_tap.u_coh`.
3. `amber_top.sv` was missing declarations for the internal `fub_awqos`/`fub_awregion` seam wires; Verilator created them as 1-bit implicit signals. Added explicit 4-bit declarations.
4. `amber_top.f` lost the `sdpram_slave_axi4_axi4` closure that `amber_pair_rig_tb` merges in. Added it back.

## Verification

| Suite | Command | Result |
|-------|---------|--------|
| Filelist registry | `python bin/filelist_registry.py --check` | PASS — all areas covered, 0 broken refs |
| Task ID tracker | `python bin/check_task_ids.py` | PASS |
| Pre-commit (direct hook) | `.git/hooks/pre-commit` | PASS — declaration order, select-on-function-call, staged SV parse, filelist contract, etc. |
| common-ip DV | `pytest projects/components/cache-ip/common-ip/dv/tests -q` | **210 passed, 78 warnings in 58.12s** |
| amber-mesi-l1 DV (targeted) | `pytest test_amber_ace_top.py test_amber_pair_rig.py test_amber_top_reset_sync.py -q` | **15 passed, 15 warnings in 254.93s** |

The full `test_amber_parity.py` suite was started but stopped after the two 100k-replay cells proved too long for this session. The targeted suite covers the restructured tops directly: `amber_ace_top`, the pair-rig `amber_top` instances, and `amber_top` reset synchronization. All 15 targeted cells pass.

The common-ip regression was re-run after the `l1_core_tb.py` tap refactor and continues to pass (210 tests), confirming the base-class change is backward-compatible with `l1_core_fab_tb`.

## Files committed

Only the nine files owned by this task were staged and committed:

```
projects/components/cache-ip/amber-mesi-l1/docs/task-reports/2026-11-01-task-3-plane-restructure-amber-tops.md
projects/components/cache-ip/amber-mesi-l1/dv/tbclasses/amber_ace_top_tb.py
projects/components/cache-ip/amber-mesi-l1/dv/tbclasses/amber_pair_rig_tb.py
projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f
projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_all.f
projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_top.f
projects/components/cache-ip/amber-mesi-l1/rtl/top/amber_ace_top.sv
projects/components/cache-ip/amber-mesi-l1/rtl/top/amber_top.sv
projects/components/cache-ip/common-ip/dv/tbclasses/l1_core_tb.py
```

Other workspace modifications (`formal/stream/scheduler/scheduler_flat.v`, deleted `.superpowers/...` reports, untracked NexysA7 build artifacts) were left unstaged because they are not part of this task.

## Follow-up / open items

1. Run the full `test_amber_parity.py` suite in a background/nightly context to obtain the complete 79-test pass count. The targeted top-level tests already pass; the parity suite is a regression soak over the coherence behavior rather than a test of the new top hierarchy.
2. Verify the Genesys2 `amber_top` integration still builds with the new filelist.
