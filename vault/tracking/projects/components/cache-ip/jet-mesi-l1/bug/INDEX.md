<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-mesi-l1 — bugs

**Next ID: BUG-009** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what
correct looks like. If you cannot state the expected behaviour, it is an
ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 8 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

(none)

## Closed

- **BUG-001** ([page](closed/BUG-001.md)) — jet_mshr `set_full_o` compares claims against WAYS cast to MW+1 bits: constant-true at MSHR_COUNT=2, WAYS=4 (every s128w4_m02 FULL cell fails to build). Filed 2026-11-09 from the first FULL run of the pushed RTL; closed 2026-11-09.
- **BUG-002** ([page](closed/BUG-002.md)) — jet_wb_buffer indexes `r_data` with `{slot, beat}` into a VICTIM_DEPTH*FILL_BEATS store: one bit too wide at VICTIM_DEPTH=1 (every *_v1 FULL cell fails to build), wrong at non-pow2 depths. Filed 2026-11-09; closed 2026-11-09.
- **BUG-003** ([page](closed/BUG-003.md)) — jet_pair_fabric loses the buffer-free clear when a trailing absorption's BVALID lands during the peer's F_REPLAY_R (guard not owner-qualified): that direction is never granted again, rig hang (SEED=54355, s128w4 m16v1 fifo). P1. Filed 2026-11-09; closed 2026-11-09.
- **BUG-004** ([page](closed/BUG-004.md)) — jet_pair_fabric safe-peer wait demands an idle peer lookup (`lkup_live`) that a pipelined request stream never grants while the peer's own fill waits on the fabric: both caches park with an AR held, F_AC forever. Found by the pipelined cycle injector (common-ip TASK-002) at depth 8; pinned by pair-rig scenario (i). P1. Filed and closed 2026-11-11 (fix in jet_pair_fabric; jet FULL 149/149, bin 17 swept).
- **BUG-005** ([page](closed/BUG-005.md)) — a write-back victim passed on by a snoop still drains (jet carries jet-prime BUG-002: stale bytes can land after the new owner's write-back). Deferred 2026-11-24 while jet was frozen; fixed 2026-11-25 at the owner's request (jet-prime's fix ported, jet full 149/149); control liveness and safety proofs PASS; closed 2026-11-26; the fabric order hold, unreached by random traffic on jet, is pinned by pair-rig scenario (j).
- **BUG-006** ([page](closed/BUG-006.md)) — jet_pair_fabric's write-port arbiter keeps the LAST match of a scan that ends at the previous winner: the last winner keeps top priority (the comment says fair round-robin). Fairness by timing accident; jet BUG-005 scenario (j) depends on it. P2. Filed 2026-11-26. Fixed 2026-11-26 with rtl/common arbiter_round_robin (req/grant/ACK mode; the absorption kick folded into the write-back's request); jet full 149/149; pinned by pair-rig scenarios (j) and (k) and the grant-eligibility check; closed.
- **BUG-007** ([page](closed/BUG-007.md)) — the Genesys2 jet pair harness decoded 64 B of its 4 KB harness_csr window (addr[5:2]): every offset aliased onto five registers, so the shared host's io sequence read IO_STATUS (0x050) as FABRIC_DBG, saw "IO port present" and wrote CTRL through IO_ADDR (0x040). P3. Filed and closed 2026-11-26: decode addr[11:2]; probe test pins it; board io now skips itself, bin 19 sweeps CRC-identical.

- **BUG-008** ([page](closed/BUG-008.md)) — jet_pair_fabric's safe-peer wait counted the peer's LOOKUP / HIT states as unsafe: a miss waited for as long as the peer hit back to back (board r4k_we0 depth >= 2: one injector ran after the other). P1. Filed and fixed 2026-11-27 (the wait holds only in INIT and the miss states; pinned by `hit_stream_snoop_liveness_test`; jet full 149/149; board bin 21: every dual cell overlaps).

## Deferred

(none)