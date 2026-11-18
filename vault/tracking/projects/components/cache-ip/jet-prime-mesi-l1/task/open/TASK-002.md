# TASK-002: the 2-cycle resident hit -- jet-prime's lookup pipeline against HPDcache's floor

**Priority:** P3
**Status:** open
**Owner:** TBD

Filed 2026-11-17 from TASK-001's step-5 reading. With the miss path rebuilt
(steps 2-5) jet-prime is under HPDcache at every depth on both thrash
configurations; what remains over HPDcache is the resident hit. jet answers a
hit in 3 cycles at the injector and HPDcache in 2 (1 inside the cache plus
its wrapper's reorder ring), so at depths 1 and 2 every resident
configuration (`r4k_*`, `r16k_we64`, `smoke4k_we64`) sits a cycle per
transaction over HPDcache, and on the thrashes half the depth-1
transactions are hits: the 3.5 % depth-1 margin on `r64k_we255` (0.48
cycles per transaction) is this cycle. From depth 4 the hit rows are 1.00
on both and the gap is gone. TASK-001 kept this out of its criterion; JP2
only asks that the hit not regress from 3.

## Where the three cycles are

jet TASK-003 (closed 2026-11-10) counted the v3 resident read hit after
its two FIFO bypasses landed:

| cycle | what happens |
|---|---|
| c0 | CPU handshake; the request skid is transparent while empty, so the lookup sees it this cycle: tag and state read, capture into the classify stage |
| c1 | classify (hit, way); data-array read address presented a stage ahead of the way select (TASK-003 step 1) |
| c2 | data lands, read serve fires, deposit into `jet_rsp_seq`; the head-deposit bypass offers it as `cpu_rsp` in the same cycle |

The capture/classify split is the v3 lookup pipeline (jet ISSUE-001,
2026-11-03): in v2 the classify decided acceptance from the skid's
asynchronous read and the 24-level cone through `u_control` and `u_repl`
failed 100 MHz by 1.8 ns. The split is therefore a timing decision, not a
functional one, and the item is to find the cycle without undoing that
closure.

## Candidate directions (measure before choosing)

1. **Read the set at capture, select the way after classify.** The index is
   known at c0; the data array could read all ways of the set in c0 and the
   c1 classify picks the way from the landed words, so the serve fires in
   c1. Costs: WAY_COUNT read words per cycle out of the data array (port
   width or bank count), the way mux in the c1 cone, and the port-B
   contention rules of the victim capture and the fill beats (MAS ch02/01).
2. **Fold the classify back into the capture cycle for hits only.** A hit
   classify is the tag compare and the state check; the long cone is the
   miss side (MSHR match, allocation, victim claim). A hit-only early
   decision that the full classify confirms a cycle later could serve in
   c1 if the confirmation can cancel a wrong early hit without a side
   effect -- the read serve has one (the response deposit), so this needs
   a kill before the deposit, or a deposit that can be withdrawn.
3. Count first. Rebuild the TASK-003 table on jet-prime's current RTL in
   the pair rig (the step-5 VCD timeline extractor in the TASK-001 log does
   this) and confirm no FIFO cycle has crept back in since the fork.

## Constraints

- 100 MHz on Genesys2 under the 0.2 ns clock-uncertainty budget, on both
  the reference-rig build (REF_CACHE_SEL=3) and the pair-rig build. The
  current worst path is in the fill engine's staging-queue read pointer,
  not the lookup; whatever is added to c0/c1 must not become the new one.
- No common-ip change (`l1_cpu_frontend`, `l1_repl`, the arrays) without
  the owner's say; jet TASK-003 landed its two cycles in `jet_cpu_plane`
  and `jet_rsp_seq` alone.
- Hit rows stay 1.00 from depth 4 (JP2); the response order contract (J4)
  and the MAS ch02/01 capture contract hold.

## Done

- Resident read-hit latency 2 cycles at the injector (`lat_min` on
  `r4k_we0` depth 1), `r4k_*` / `r16k_we64` at depths 1 and 2 at or under
  HPDcache's cycles per transaction, the thrash rows no worse than the
  step-5 bin.
- jet's FULL grid, the pair-rig DV and the control formal (prove,
  prove-live, cover) green on the result; lint clean; a bin on the board
  with WNS >= 0 under the budget, smoke PASS, both sweeps err 0 with the
  single-core CRCs equal to bin 4's.
- Written up as docs/delta/04 and in the reference comparison.

## Progress

(not started)
