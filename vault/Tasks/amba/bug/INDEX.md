<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba — bugs

**Next ID: BUG-039** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 38 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open


## Closed

- **BUG-038** — axis4_slave/master tuser unpack ate low bits with ID or DEST zero-width (UW>0); found via reed-solomon TASK-002 erasure sideband — CLOSED 2026-10-02: per-field slices (axis5 style) in both modules
- **BUG-036** — SOFT_RESET does not fully reset the monitor subsystem -- CLOSED 2026-09-28: not reset state; the in-core group filtered every packet with DAXMON's registers (stream BUG-017, fixed)
- **BUG-037** — ID filter loses an owned write's completion at some seeds -- CLOSED 2026-09-28: root cause was W-before-AW beats dropped by the write monitor (not the filter); trans_mgr now queues early bursts for the next AW
- **BUG-035** — monitor TIMEOUT packets saturate at ~table depth per reset -- CLOSED 2026-09-28: cosim fix 2026-09-15, board confirmed by Sean
- **BUG-002** — `axi4_dma_observer` does not elaborate — CLOSED: module deleted
- **BUG-003** — splitter block_ready duplication — CLOSED (fixed pre-537c7af8, verified against tree 2026-08-23)
- **BUG-004** — CLOSED 2026-08-28 -- stale as filed; the real gap was inside sdpram_core
- **BUG-005** — splitter defect cluster round 2 — CLOSED (537c7af8; verified against tree 2026-08-23)
- **BUG-006** — converter read-path PSLVERR + peakrdl held-req — CLOSED (537c7af8 + revert; verified against tree 2026-08-23)
- **BUG-007** — / TASK-069 / TASK-067 -- CLOSED together (fixed + witnessed, 2026-08-25)
- **BUG-008** — apb4_master response-backpressure deadlock -- CLOSED (fixed + mutation-proven, 2026-08-25)
- **BUG-009** — mon_cg monbus_valid held through gating -- FIXED 2026-08-26, residual CLOSED same day
- **BUG-010** — apb4_master/apb5_master drove a TWO-cycle APB setup phase out of IDLE
- **BUG-011** — write monitors ID-filter W beats against the LIVE AWID
- **BUG-012** — test_axis4_slave dies with SystemExit under heavy parallel load
- **BUG-013** — axis5 _cg pages claim TREADY is held low while gated -- unverified
- **BUG-014** — four instantiation examples in components docs name ports that do not exist
- **BUG-015** — monitor_trans_cam has a combinational loop that only a cocotb-flavoured build can see
- **BUG-016** — lint findings in the monitor that the bridge gate now surfaces
- **BUG-017** — two val/amba tests fail deterministically on specific seeds
- **BUG-018** — three monitors read the event FIFO's registered output in the handshake clock
- **BUG-019** — the Wishbone BFMs do not sample CTI/BTE, and wb4_monitor does not report them
- **BUG-020** — the converters spec PDF is two revisions behind its source
- **BUG-021** — apb4/apb5_master_cg -- the wake property checked one clock too early
- **BUG-022** — formal harnesses that pin a DUT input at a constant
- **BUG-023** — the four axi4 *_mon covers had never been reachable
- **BUG-024** — axi_master_rd_splitter returned read data before accepting the read (AXI A3.3.1)
- **BUG-025** — axi_split_combi's next-boundary arithmetic overflows in the top alignment window
- **BUG-026** — no monitor TB drives cfg_id_filter_enable, so it is X in every test
- **BUG-027** — the write splitter's proof cannot see an extra downstream beat
- **BUG-028** — STABILITY — monbus payload could change during valid && !ready
- **BUG-029** — CLOSED 2026-08-26 (root cause was [[AMBA-BLOCKMARGIN]], fixed + measured)
- **BUG-030** — CLOSED 2026-08-26 (fix landed 2026-08-20 in 16e4c18b; verified + reconciled today)
- **BUG-031** — FLAKY — wavedrom runners handed themselves a random seed
- **BUG-032** — INTERMITTENT — OPEN on a scope decision for six sibling TBs (root-caused, primary fix landed 2026-08-28)
- **BUG-033** — CLOSED 2026-08-27: SKID_DEPTH 2 -> 3 recovers 1 record/cycle
- **BUG-034** — CLOSED 2026-08-26: NUM_CHANNELS=1 channel decode guarded
- **BUG-001** — every integration example in `rtl/amba/CLAUDE.md` named ports the modules do not have; 10 examples + 6 table rows corrected.
