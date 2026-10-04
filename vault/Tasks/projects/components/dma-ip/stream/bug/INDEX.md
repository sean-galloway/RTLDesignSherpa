<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dma-ip/stream — bugs

**Next ID: BUG-020** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 18 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

- **BUG-019** — the obs/mon host campaigns still arm and report the perf/
  debug cones the 2026-09-27 lite-taps rework retired (caps0 bit4/bit5 read 0),
  so obs live-traffic tallies land ~89% in UNEXPECTED and mon_coverage sees
  4/8 tuples; re-baseline the campaigns against OBS_CAPS0. ACTIVE 2026-10-04:
  host side done and committed (obs_addrs caps helpers, arm-what-you-key,
  matrix row SKIP by primary class, build-mon uses BUILD_CONFIG.GEN_MON +
  LITE_RETIRED_TYPES); board re-pin of the results files parked — needs a
  Genesys 2 session


## Closed

- **BUG-018** — both AXI engines wrap a 256-beat burst to 0 beats (8-bit "AxLEN + 1"); the rapids BUG-009 lines, fixed the same way (burst clamped to the buffer) with the rapids engine unit suites ported -- CLOSED 2026-09-29

- **BUG-017** — the in-core monbus group filtered every packet with DAXMON's registers (amba BUG-036) -- CLOSED 2026-09-28 (fix 201babbb5)

- **BUG-016** — the monitor PKT_MASK registers are described as "1 = enable"; the hardware masks on 1 -- CLOSED 2026-09-28 (RDL at 02b5f4629, MAS rows with BUG-017)
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
- **BUG-014** — the descriptor engine fetches any kicked address, in range or not (closed 2026-09-27)
- **BUG-015** — a kick that ends in RD_ERROR wedges the channel's APB path through channel reset (closed 2026-09-27)
