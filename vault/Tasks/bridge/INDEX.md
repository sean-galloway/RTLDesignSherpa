# bridge — task rollup

**Next ID: BRIDGE-020** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 0 | 0 | 9 | 4 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 15 | 0 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 1 | 0 | 0 |

Items live one per file under the lane directories below; this page is the
area overview. See [the convention](../INDEX.md) for the definitions.


Bridge crossbar generator (`projects/components/fabric-gen-ip/bridge/`): the CSV/toml-driven
generator, its generated wrappers/xbars/adapters, and their DV.

| State | Count |
|---|---|
| active | 0 |
| open | 0 |
| closed | 21 |
| dropped | 0 |

## Open

Nothing, since 2026-09-13. BRIDGE-017 (the legacy backlog: perf
characterization, synthesis flow, CDC slave ports, QoS aging, registered
crossbar) and BRIDGE-018 (native-AXI5 fabric: Memory Tagging and chunking
through the structs) both closed; the two known Wishbone gaps are on the
dropped page by the owner's decision (best effort). A new bridge task starts
from a consumer's need, not from this list.

> The pre-migration `projects/components/fabric-gen-ip/bridge/TASKS.md` was folded in on
> 2026-09-10: ledger at the end of closed, leftovers in
> BRIDGE-017 and dropped. The file is retired.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.

---

## Pre-migration ledger: projects/components/fabric-gen-ip/bridge/TASKS.md (retired 2026-09-10)

The component's own task file predated the vault and was folded in here, one
line per item with its disposition. It described the generator as of 2025-11;
everything below that was "Planned" either happened under a BRIDGE-0xx task,
is superseded, or moved to [[BRIDGE-017]] / dropped.

| Legacy | Title | Disposition |
|---|---|---|
| TASK-000A | AXI4 interface wrapper integration | Complete 2025-11-04 |
| TASK-000 | Intelligent width-aware routing (4 phases, per-slave arbitration) | Complete 2025-11-04 |
| TASK-000B | slave_select reversion and multi-master routing fixes | Complete 2026-05-13 |
| TASK-001 | APB converter | Done: `axi4_to_apb4_shim` (+ apb5, BRIDGE-002 A5-3c) |
| TASK-002 | Channel-specific master end-to-end testing | Done: `bridge_1x2_{rd,wr}*` fixtures and generated tests |
| TASK-003 | Width converter integration testing | Done: mixed-width fixtures, `bridge_1x2_rd_axi5w`, converters suite |
| TASK-004 | CSV generator documentation | Done: bridge HAS/MAS (generated, house pipeline) |
| TASK-005 | Performance characterization | Not done -> [[BRIDGE-017]] |
| TASK-006 | Address decode documentation | Done: MAS ch02 address decode |
| TASK-007 | Error handling / response routing documentation | Done: MAS ch02 response routing, BRIDGE-009/010/011 |
| TASK-008 | WaveDrom timing diagrams | Done: MAS/HAS diagrams (mermaid); wavedrom generators in handbook |
| TASK-009 | PlantUML architecture diagrams | Superseded by the mermaid set in the HAS |
| TASK-010 | Synthesis and implementation guide | Not done -> [[BRIDGE-017]] |
| TASK-011 | Generator id_width + prefix handling (bugs A/B/C) | Closed 2026-04-30 |
| TASK-011b | Replace hand-coded arbiters with standard components | Done: BRIDGE-005 request arbiter |
| TASK-012 | AXI burst optimization | Dropped (no defined target) -> dropped.md |
| TASK-013a | Outstanding transaction support | Done: AW/AR tracking FIFOs, BRIDGE-011 not-full gating |
| TASK-013b | Timeout detection | Done: `_mon` variants' AXI monitors report timeouts |
| TASK-014 | APB3 to APB4 bridge | Dropped (no consumer) -> dropped.md |
| TASK-015 | AXI4 <-> AXI4-Lite converter | Done: `axi4_to_axil4_{rd,wr}` (+ axil5) |
| TASK-016 | Async clock domain crossing | Not done -> [[BRIDGE-017]] |
| TASK-017 | QoS with aging counters | Not done -> [[BRIDGE-017]] |
| TASK-018 | CAM-based response routing (optional) | Done: `enable_ooo` slaves use `bridge_cam`; repaired under BRIDGE-015 |
| TASK-019 | Pipeline FIFOs for high-performance crossbars | Not done -> [[BRIDGE-017]] |
| TASK-021 | Testbench and test file automation | Done: `--generate-tests` emits TB class + tests per fixture |

<!-- Moved from vault/Tasks/amba/ 2026-09-14: a bridge task, filed under amba -->
## BRIDGE-NEXYSA7-REGEN — the five NexysA7 char-framework bridges cannot be regenerated in place
**Status:** CLOSED 2026-09-11, overtaken. The five bridges no longer exist in that form: the stream characterization frameworks moved to `projects/fpga-systems/Genesys2/dma-ip/stream/rtl/bridges/` and were respun there, and the pumice `ddr2_char_framework/rtl/bridges/` now keeps its tomls in a `configs/` sibling (the layout this item prescribed) and was regenerated in place on 2026-09-11 (a1e53e5fd, BRIDGE-016 downstream). Nothing left to do.
**Was:** open 2026-07-28 (found by Claude during the USE_JOHNSON sweep)
**Priority:** P3

Five generated bridges under the board-characterization frameworks are stale
with respect to the bridge generator:

    projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_axil
    projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil
    .../bridge_stream_char_axil_mon
    .../bridge_stream_mon_axil
    .../bridge_stream_mon_axil_mon

They carry `Generated by: SlaveAdapterGenerator` and instantiate
`axi4_to_apb4_shim`, but they missed the USE_JOHNSON regeneration that updated
the 13 adapters under `projects/components/fabric-gen-ip/bridge/rtl/generated/`. Harmless
today -- the shim's `USE_JOHNSON` defaults to 0, which is what the FIFO used
before the parameter existed, so the elaborated hardware is identical. It is a
consistency gap, not a functional one.

### Why it is not a one-liner

**The generator cannot write to the directory it reads from.** Each of these
dirs holds its own `<name>.toml` and `<name>_connectivity.csv` NEXT TO the
generated output. `_emit_bridge_variant` clears/copies into the output dir, so
invoking

    bridge_generator.py --ports <dir>/<name>.toml \
                        --connectivity <dir>/<name>_connectivity.csv \
                        --name <name> --output-dir <parent>

deletes the toml and csv partway through and then dies on
`FileNotFoundError ... <name>.toml` in `shutil.copy2`. All five fail the same
way, leaving a half-regenerated tree. (Tried on 2026-07-28; restored with
`git checkout -- projects/NexysA7/`, which recovers cleanly because the configs
are tracked.)

`projects/components/fabric-gen-ip/bridge/` avoids this because `bin/bridge_batch.csv` keeps
configs in `bin/test_configs/` and writes to `../rtl/generated` -- separate
trees.

### The fix

Move each config out of its output dir (a `configs/` sibling, mirroring the
components layout), then add these five to a batch CSV so `make regen` covers
them. Do NOT hand-edit the adapters to add `.USE_JOHNSON(0)` -- that is the
partial-regeneration anti-pattern CRITICAL RULE #0 exists to prevent.

These are board flows; verify on hardware or in the flow's own sim before
trusting the regenerated output.

---

<!-- Moved from vault/Tasks/amba/ 2026-09-14: a bridge task, filed under amba -->
## BRIDGE-MON-STRESS — three _mon monitor stress tests fail on a memory-bounds read
**Status:** closed 2026-08-17 — duplicate; fixed as BRIDGE-003 (5963b2dc)

Same three tests (`mix_b`, `mix_c`, `mix_d`) and the same error —
`Read at address 0xFFC with size 8 exceeds memory bounds (size: 4096)`.
This block had already reached the right conclusion in July: *"the
failure is in the testbench memory model, not in the RTL."*

Root cause, confirmed 2026-08-16: `stress_read_plan` stepped offsets by
the SLAVE word (4 B) while `run_err_bp_phase` computed its expected
value via `tb.slave_mem_read(...)`, which derives `byte_count` from the
MASTER width. A 64-bit master drawing the top offset produced an 8-byte
read at `0xFFC`, four bytes past the cap, and because that call sits
outside the phase's `try/except` the phase died on an uncaught
`ValueError` rather than reporting a mismatch.

It was latent rather than per-test: `mix_a` has the same 64-bit master
and passed only because its random draw never landed on the last word.

The whole 13-test monitor stress suite now passes from a verified
clean. Tracked to completion in `vault/Tasks/bridge/closed.md`
(BRIDGE-003, and BRIDGE-004 for the write-only variants found
alongside).
