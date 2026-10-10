# formal/amber — SymbiYosys proofs for the amber MESI L1 control layer

Task 13 (2026-10-09/10). Tiny geometry: SETS=16 / WAYS=2 / LINE_BYTES=64 /
BUS_WIDTH=64. House pattern per `formal/common/gaxi_fifo_sync/`
(`[tasks] prove/cover`, `read_verilog -formal -sv <block>_flat.v` + wrapper,
`prep -top`, `delete t:$print`, `includes/reset_defs.svh` mapping, Makefile
with the tooling-TASK-026 `check-flat` target); flats are sv2v output with
the geometry pinned and parameter declarations removed by
`../specialize_params.py` (yosys `expose` then works on the parameterless
DUT -- this yosys build has no working `bind` at all; see the task report).

| Directory | Proves | Engine | Depth |
|---|---|---|---|
| `amber_control/` | (1) no stale data after an external write — poison invariant on an exact abstract tag store, invalidation/fill/hit write-effects, grant-cycle CRRESP vs an independent HAS Table 3.0 spec copy | boolector | 126 |
| `amber_control/` | (2) no deadlock/livelock under fair arbitration — bounded state residences + whole-request bound 104, model-free wrapper (`formal_amber_control_live.sv`, free tag data) | boolector | 126 |
| `amber_control/` | cover: all seven scenario covers (pf grant, pending-fill CD, pend commit, hits, miss response, poisoned lookup, drain detour) | boolector | 80 |
| `amber_pending_fill_bypass/` | pf state accuracy, beat-mask monotonicity, load/clear/beat priority | z3 (house) | 25 |
| `amber_victim/` | never loaded while busy, handoff payload exact/stable, drain-done ordering | z3 | 20 |
| `amber_snoop_resp/` | AC/CR/CD ordering (CR only after CDLAST), one closed response per AC, CR payload integrity through the skid FIFO | boolector | 80 |

Run: `make prove [prove-live] cover` in each directory (control safety
takes minutes with the `memory_map` encoding; run one sby instance per
task dir at a time -- `make clean` and a second `sby -f` both delete
`*_prove/` dirs mid-run). Gate: `python3 bin/formal_status.py
--check-flats --staged`.

Full assumption/abstraction inventory, soundness derivations (including the
12-cycle fill-window structural minimum), the vacuity hazard the cover task
caught, engine measurements, and Step-4 sim evidence:
`.superpowers/sdd/2026-10-07-amber-rtl-completion/task-13-report.md`.
No RTL changes were made by this task.
