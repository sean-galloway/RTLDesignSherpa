<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dmas/stream — bugs

**Next ID: BUG-015** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 13 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **BUG-000** — reserved template; copy the file, do not file against it.
- **BUG-014** — the descriptor engine fetches any kicked address, in range or not (open 2026-09-27)

## Closed

- **BUG-001** — STREAM formal proofs read a hand-copied gaxi_fifo_sync, not the RTL
- **BUG-002** — `.sv2v_prep` holds TRACKED generated files that `make clean` deletes
- **BUG-003** — stream_core's formal dependency list has rotted behind the monitor rework
- **BUG-004** — datapath_wr_test proof FAILS once it can finally elaborate
- **BUG-005** — sv2v regen: TWO stacked bugs, and `$display` was only the second
- **BUG-006** — TB address->name lookup is a hardcoded chain, not a regmap lookup
- **BUG-007** — perf FIFO read made atomic: pop once BOTH halves are read
- **BUG-008** — build-mon host walks slvmon_apb with the wrong regmap
- **BUG-009** — test_stream_top_basic filed every channel's descriptors under ch0
- **BUG-010** — Fix STREAM extended chained strided (transpose) descriptor corruption
- **BUG-011** — sram_controller_unit's drain accounting refuses to count a write the FIFO accepted
- **BUG-012** — axi_read_engine issues ARs against SRAM space it has already taken (closed 2026-09-27)
- **BUG-013** — axi_write_engine runs two AWs per channel at PIPELINE=0 (closed 2026-09-27)
