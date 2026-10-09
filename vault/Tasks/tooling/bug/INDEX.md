<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — bugs

**Next ID: BUG-017** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 15 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-015** — the cocotb 2.x flip matrix did not cover the UART-equivalence
  suites: 16 files still used the removed `cocotb.external`/`cocotb.function`
  (fixed in 61ea5dc13); re-run the touched suites under 2.1.0 and extend the
  flip matrix to cover the bridge consumers.



## Closed

- **BUG-016** — the one val/amba runner that didn't pin a simulator fell into cocotb-test's icarus default, and the oss-cad-suite vvp wrapper's glibc-2.35 libm cannot host system libpython3.12 -- CLOSED 2026-10-08: simulator="verilator" pinned in test_axis4_pattern_pair.py (uniform with its siblings); 3/3 params re-passed in 31 s; residual trap + the libm-swap remedy documented in-file
- **BUG-014** — `check_task_ids` globbed the worktree, so as a pre-commit hook it validated a different tree than the one it approved -- CLOSED 2026-09-30: `tracker_tree()` materialises the index being committed; `--tasks-root` added; 6 new teeth tests (11 total), 2 end-to-end reproducers that failed before the fix, mutation-tested 3 ways
- **BUG-013** — `check_port_consumers.py` cannot see unpacked-array ports, so it -- CLOSED 2026-09-29: regex takes unpacked dims; unexplained-pin guard reports shapes the parser misses; end-to-end test in bin/tests
- **BUG-004** — conftests stamp TEST_LEVEL, killing per-cell depth -- CLOSED 2026-09-27: mechanism + checker done, 7 of 8 areas converted; pumice's conversion is pumice BUG-019
- **BUG-005** — concurrent deletion of local_sim_build -- CLOSED 2026-09-27: marker-aware cleaner on every clean target on main; the ddr2_char Makefile is pumice TASK-031
- **BUG-006** — env_python hardcodes /mnt/data/tools
- **BUG-007** — Python version mismatch breaks EVERY Verilator build on this box
- **BUG-008** — `--reruns 3` re-rolls the seed, so a seed-exposed RTL bug retries until it passes
- **BUG-009** — `lint-<component>` is advertised but cannot run for two areas
- **BUG-010** — the filelist gate was blind outside registered areas, to +incdir+, and to its own build output
- **BUG-011** — delta's lint runs, passes, and gates nothing
- **BUG-012** — Scripts book link rot + DOCUMENTATION_INDEX refresh
- **BUG-003** — `RegisterMap.walk()` crashes on an ERROR response, so the MON-window guard silently disabled the board register walk on every `USE_AXI_MONITORS=0` build since 2026-09-24 (walker fixed; host-side skip still open)
- **BUG-001** — checker attribution: multi-module declarations + 46 pages silently unchecked (fixed; threshold was NOT the defect)
- **BUG-002** — `--blindspots` read the index and disk in one subtraction, so a tracked+registered filelist absent from the worktree was reported unregistered (fixed; the rename-commit block it was filed for was CORRECT)

## Deferred

