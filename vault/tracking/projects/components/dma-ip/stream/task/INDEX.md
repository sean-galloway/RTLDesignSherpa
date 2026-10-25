<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/dma-ip/stream — tasks

**Next ID: TASK-022** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 20 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open


## Active

(none)

## Deferred

(none)


## Closed

- **TASK-019** — CLOSED 2026-10-25: `monbus_axil4_group_1wr` on both STREAM tops and stream-g; `MON_GROUP_ERR_*` window + `MON_ERR_REC_COUNT`; records read from memory in sim (top monbus test) and on the Genesys 2 harness (error window = top 4 KB of comp_sram, `dump_monbus.py`); books MAS 0.104 / HAS 0.101 / board 1.5; rapids twin TASK-039
- **TASK-020** — stream-g: STREAM's schedulers sequenced by gatling firmware (its own image), measured against STREAM on the Genesys 2 the rapids-g way; closed 2026-10-25
- **TASK-021** — stream-g lone-channel chain plateau (32-80 beats): the one-slot poll tested the chain hook only on a pass's first read; fixed in STREAM's own firmware, board 1,890 -> 1,126 cycles at 32 beats; closed 2026-10-25
- **TASK-018** — loadable firmware memory as on rapids-g; delivered by TASK-020 phase 4 (stream-g carries rapids-g's loader unchanged, FW_* at 0x3A0-0x3AC); closed 2026-10-24
- **TASK-017** — CLOSED 2026-10-18: two-deep descriptor skid in every scheduler (rapids TASK-028 parity); formal ap_desc_skid_bound
- **TASK-016** — CLOSED 2026-10-03: all three Genesys2 stream builds rebuilt on
  the fixed sdpram (71d48b6f7), timing-closed, board-verified; perf 40/40
  cycle-identical to the pre-fix sweep (0 measured datapath change — the tax
  amortizes at 1MB/desc); mon/obs tallies re-baselined against the lite-taps
  instrument; every pinned board figure carries a post-fix number or dated note
- **TASK-015** — regs/README.md: the stream_regs example names five ports the generated block does not have -- CLOSED 2026-09-29: regs/README.md rewritten as a link page; the stale sketch is gone
- **TASK-012** — all 38 signal-contract maps armed: 32 IDENTICAL, 3 DIFFERS justified, 0 NOT CHECKED; four rotted maps rewritten to the current RTL (closed 2026-09-28)
- **TASK-013** — placement pass: 2 pages re-homed, 7 stale/generated pages deleted, coverage tool output ignored (closed 2026-09-28)

- **TASK-004** — RFC Stage-E in-core R/W datapath perf monitors; goal met by the shared interface observers, board boxes discharged by the v1.4 campaign (closed 2026-09-28)

- **TASK-003** — scrub the tests for completeness (stream)
- **TASK-002** — gate the monitor regfile on a parameter (present + decoded)
- **TASK-001** — finish the STREAM workbook so its maps prove the decisions
- **TASK-005** — RLB blocks brought under the .rdl regen gate
- **TASK-006** — .rdl regen gate extended from 1 block to 9
- **TASK-007** — .rdl edits are gated against their generated artifacts
- **TASK-008** — perf FIFO is read non-empty, pairing asserted
- **TASK-009** — Signal contracts + K-maps for the significant STREAM signals (prove-by-construction)
- **TASK-010** — Kick STREAM from its own registers — delete the sideband kick ports and the APB kick block
- **TASK-011** — Configurable decompression in `monbus_tally_axil` (LOW priority, future)
