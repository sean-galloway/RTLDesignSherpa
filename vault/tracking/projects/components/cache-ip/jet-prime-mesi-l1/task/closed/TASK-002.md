# TASK-002: the 2-cycle resident hit -- jet-prime's lookup pipeline against HPDcache's floor

**Priority:** P3
**Status:** closed 2026-11-19 (filed 2026-11-17; built, measured and closed in one day) -- hit floor 2 on the board, the resident rows at HPDcache's numbers at depth 1 and within 0.05 cycles at depth 2
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

### 2026-11-19 -- built, measured, closed

- **Counted first.** The RTL read confirmed jet TASK-003's table on the
  fork: c0 handshake + tag read + capture, c1 classify with the data
  address leading, c2 the word lands and the deposit bypasses into the
  frontend's staging FIFO, c3 `cpu_rsp`. The cycle to find was c2, and
  `l1_data_array` already reads every way per address with the way
  selected on the output side -- direction 1 of the candidates, at no
  cost in common-ip.
- **Built** (`jet_prime_control` only; delta 04): the arriving request's
  `{set, beat}` leads on port A in its capture cycle (`w_live_lead`,
  keyed off `lkup_valid_i`, yielding to the occupant whenever it may need
  the record path, `w_occ_need`); a read hit answers from the port in
  its classify cycle (`w_direct_fire`: its lead landed, no array write at
  that edge, the completion port free); a write hit acks in its classify
  cycle (`w_direct_ack`, the store echoed) and the record keeps only its
  array write and E-to-M promotion (`r_srv_dep`). The same-line hold and
  `sn_safe_o` cover the ack-to-write window as they covered the record's.
- **Three bins to get there.** Bin 5a (the read side, lead priority to
  the arriving request): floor 2, `r4k_we0` 3.00, but the mixed resident
  rows lost 40 % of their throughput at depth 4 and 16 -- the lead took
  the port from occupants that needed the record path and the one-deep
  record held the classify. Bin 6 (the yield): throughput restored, the
  write-containing rows a cycle over at depth 1 (the write hit). Bin 7
  (the early write ack): done. Both intermediate sweeps kept in
  `ref/results`; the lesson is [[fast-path-must-not-starve-the-fallback]].
- **Result (bin 7, injector 1 idle, s5 -> s6, HPDcache):** hit floor 3 ->
  2 (2). Depth 1: `r4k_we0` 4.00 -> 3.00 (3.00), `r4k_we255` 4.03 -> 3.03
  (3.00), `smoke4k_we64` 4.02 -> 3.02 (3.07), `r16k_we64` 4.16 -> 3.17
  (3.20); depth 2: 2.00 -> 1.50 (1.50), 2.03 -> 1.54 (1.50), 2.00 -> 1.58
  (1.53), 2.08 -> 1.66 (1.64). Thrashes at depth 1: `r64k_we64` 12.76 ->
  12.27 (13.73), `r64k_we255` 13.17 -> 12.68 (13.65), `r128k_we64` 16.94
  -> 16.69 (18.83); from depth 4 every row is s5's within 0.02. Board
  18,241 LUT / 11,896 FF, WNS +0.040 under the budget, the same worst path
  as bins 3-4; smoke PASS; both sweeps err 0; all 55 single-core CRCs
  equal to bin 4's. OOC jetp6 6,033 LUT / 5,402 FF, WNS +0.082.
- **Against the done criterion.** `lat_min` 2: met. Resident rows at
  depth 1: at or under HPDcache except `r4k_we255` at 3.03 against 3.00
  (one write in a hundred acks from the record because its accept cycle
  found the completion port taken); at depth 2 within 0.02-0.05 of
  HPDcache on the write-containing rows for the same reason, equal on the
  pure-read row. Thrash rows: better than bin 4 at depths 1-2, equal from
  4. Verification: lint clean, gate 21/21, FULL 155/155 (9:22), ref-g2
  gate 7/7, control covers 23/23 and 7/7 on the regenerated flat, the
  safety prove relaunched on the final flat (verdict to be appended; the
  step-5 flat's took 26:52); the liveness BMC left as TASK-001 recorded.
  Pair-rig func cell at the CPU boundary: every directly served read hit
  2 cycles. Control TB FULL cell: 107 hits answered in the accept cycle,
  2 from the record. Written up in delta 04 and the reference comparison
  (s6 column). Closed.
