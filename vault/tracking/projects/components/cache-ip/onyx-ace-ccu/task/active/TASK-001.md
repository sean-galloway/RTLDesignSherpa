# TASK-001: onyx v1 -- the ACE coherency unit per the D rulings, measured against the pair fabric it replaces

**Priority:** P2
**Status:** active (filed 2026-11-20, started 2026-11-21)
**Owner:** TBD

Filed 2026-11-20 at the owner's word ("follow the D recommendations"):
the onyx PRD's D1-D6 and D8-D11 are decided (v0.7), each on the
candidate the row had recommended, and this is the build they define.
Every cache-ip L1 lane is empty; onyx is the family plan's next IP, and
basalt (the shared L2) is gated on it.

## What v1 is

The coherency unit in the culsans shape: N (2-4, parameter) ACE
slave-side ports toward caches, one AXI4 master toward memory, one
ACE-Lite IO port (D1). It decodes the transactions the house caches issue
-- ReadNotSharedDirty, ReadUnique, CleanUnique, WriteBack, Evict (D2) --
broadcasts the snoop to every other attached cache (D3), gathers the CR
and CD responses per outstanding transaction from a transaction table
(D4), serializes per address so different lines interleave (D5),
adjudicates the data source (a PassDirty responder or a single designated
forwarder, memory otherwise) with the memory read issued alongside the
snoop and a mode that defers it until the CR (D6), ignores barriers in one
shareability domain (D8), and observes through `*_monlite` taps behind
USE_MONITOR (D9). The cache-side port is the AC/CD/CR-shaped port onyx
owns (D7, 2026-10-05), which jet-prime reaches through a thin adapter.

## Why the pair fabric is the starting point

`jet_prime_pair_fabric` (jet-prime TASK-001 steps 3-5, delta 02) is
already a two-port CCU on the house AXI4 fabric: a transaction table
serializing per line, the memory read issued alongside the snoop, the
verdict latched at the AC accept, completion at the requester's retire
through the `coh_done` sideband, and a 27-property formal safety argument
(`formal/jet-prime/jet_prime_pair_fabric`) that found two memory-AR
defects. onyx generalizes it to N ports on real ACE signaling (ARSNOOP /
AWSNOOP decode, AC/CR/CD channels with the family's CD-before-CR
contract) and adds the adjudication rule and the deferred-read mode. The
first measurement is onyx in the fabric's place on the reference rig at
the fabric's own cycles per transaction (PRD criterion 6, bin 7 the
baseline).

## What already exists (inventory 2026-11-20, at the owner's pointer)

The owner noted the ACE BFM and transport might already be there and
could not vouch for the quality; onyx is their first real application.
Found and measured:

- **BFM**: `CocoTBFramework.components.ace` in RDS-DV (2026-10-05):
  `AXI4ACEMasterRead/Write` (ARSNOOP/AWSNOOP, AxDOMAIN, AxBAR, 4-bit RRESP,
  RACK/WACK auto-pulse with `auto_ack=False`), `AXI4ACESlaveRead`,
  `AXI4ACESnoopMaster` (`issue_snoop`) and `AXI4ACESnoopSlave`
  (per-address cache-state map, MESI responder matrix, replaceable
  handler), `ACEComplianceChecker` (CR/CD order, CRRESP validity per snoop
  type, no snoop to the requester), `ARSnoop`/`AWSnoop`/`SnoopType`/
  `CRRESP` types, factories, `ACE_QUICKSTART.md`. The framework's 135 ACE
  unit tests pass (0.3 s). RDS-DV issue #86 is still open in the tracker
  although the work it describes is in the tree; the D10 row's "build the
  BFM first" is therefore "verify the BFM on onyx", and gaps found are
  RDS-DV items.
- **Transport RTL**: `rtl/amba/ace/` -- `axi4ace_master_rd/wr`,
  `axi4ace_slave_rd/wr`, `axi4ace_snoop_master/slave`, each with a
  `_monlite` wrapper, plus `rtl/amba/ocelus/axi4ace_snoop_monitor_lite`;
  skid-buffer channel movers, not protocol controllers; doc pages under
  `docs/markdown/rtl-amba/ace/`. Tests: six `val/amba/test_axi4ace_*.py`
  with `bin/TBClasses/ace/*` TBs (compliance checker, CRRESP/data
  scoreboard, monitor packet checks): `make clean-all && make
  run-all-func-parallel TESTS="test_axi4ace_*.py"` 24 of 24 cells PASS in
  17 s on 2026-11-20 (the 2026-11-06 logs were green too). The master
  movers' auto-pulsed RACK/WACK is deprecated by N1 (amber follow-up A5).
- **The caches' side**: jet-prime's snoop port is already ACE-shaped
  (`m_axi_ac*` in, `m_axi_cr*`/`m_axi_cd*` out, `AMBER_CRRESP_WIDTH`), so
  the D7 adapter exists for the snoop side; the pair fabric drives it. The
  front side is plain AXI4 plus the `coh_req_{valid,addr,type}` /
  `coh_done_{valid,id}` sideband with `AMBER_ACE_*` types (l1_pkg: RNSD,
  RU, CU, MU, WB, Evict), not ARSNOOP on the AR. onyx's cache-side port
  in v1 therefore takes the fabric's contract (AXI4 + sideband + AC/CR/CD)
  natively, which keeps jet-prime's RTL unchanged and the comparison
  like-for-like; an ARSNOOP front-side flavor is the D7 adapter's second
  half when a true ACE master appears.
- **Quality caveat**: everything above is exercised at transport level
  (movers against BFMs, BFM against BFM). Nothing has driven the snoop
  BFMs against a manager that gathers several caches' responses, so
  expect the gaps there: multiple outstanding snoops per cache, CD
  multi-beat alignment at BUS_WIDTH, the responder matrix against the
  caches' actual CRRESP, RACK deprecation. Each is filed where it lives.

## The work, in order

1. **Verify the ACE BFM on onyx's shapes** (D10): a BFM-against-BFM
   scenario set for the gather (N snoop slaves answering one snoop master,
   out-of-order completion across caches, multi-beat CD, every D2
   transaction's CRRESP matrix against jet-prime's responder), run before
   any onyx RTL; gaps become RDS-DV issues, and #86 closes against the
   result. The rds-dv-axes/bfms rules apply.
2. **The core**: `onyx_ccu` -- front-end decode, the transaction table
   and per-address scoreboard (the fabric's, widened to N ports and ACE
   fields), the snoop fanout and gather, the adjudicator with both D6
   modes, the memory master, WB/Evict drains, ACE-Lite IO port. House
   rules: `ALWAYS_FF_RST` macros, no FSM on the data path, shared
   primitives only, `.f` filelists registered in `bin/filelists.toml`,
   `onyx_` prefix.
3. **The cache adapter**: jet-prime's snoop/coherent side onto the D7
   port (the thin adapter the D7 ruling named), with jet-prime's RTL
   unchanged.
4. **Formal** (D10, criterion 3): the fabric harness pattern on onyx's
   serializer and gather -- the per-address rule, one grant per line,
   the memory AR held once presented, every R/CD beat to its requester,
   no deadlock under fair arbitration at N = 2, 3, 4; mutation-checked;
   BMC at measured depths with derived bounds (TASK-003's lesson in the
   handbook's formal note).
5. **DV** (D10): Pattern-B cocotb at gate/func/full for the core alone
   with BFM caches, then the reference rig -- `REF_CACHE_SEL` for onyx +
   two jet-primes -- with the lockstep golden model the pair rig carries.
6. **Board**: the Genesys2 reference rig at 100 MHz under the 0.2 ns
   budget; the 55-point single and dual sweeps in both D6 modes; the
   cache-ip reference comparison gets an onyx column; the area row with
   and without observers.
7. **Docs**: a HAS/MAS pair for onyx (the family's first manager), the
   PRD's success criteria recorded met or not, the comparison report.

## Done when

- PRD section 5 criteria 1-6: three-block coherence on the parity suite;
  the D2-subset conformance scoreboard clean; the serializer and gather
  proven (safety) and bounded (liveness) at N = 2, 3, 4 with mutations;
  every D9 event class on MonBus in sim and captured on the board;
  LUT/FF/RAM/fmax recorded with and without observers; cycles per
  transaction equal to the pair fabric's in parallel-issue mode, the
  deferred mode's elision rate and latency cost measured.
- Every bring-up mode (D5 in-order, D6 always-read) exists as a parameter
  or CSR and is off in the measured configuration.

## Not in scope

- N2 (AxLock / PoS monitor), N5 (WLU/WU/WC/WE), N6 (DVM), N7 (prefetch
  filtering): OPEN or non-goal rows; each is its own item if promoted.
- Any change to jet-prime's cache RTL beyond the D7 adapter; any change to
  amber or jet (frozen baselines).
- A snoop filter or directory (D3 deferred; basalt's).

## Progress

- 2026-11-20: filed with the D rulings (PRD v0.7).
- 2026-11-20 (later): inventory at the owner's pointer -- the ACE BFM,
  transport RTL and tests exist (see "What already exists"); 24 of 24
  ACE func cells PASS from clean, 135 framework unit tests PASS; step 1
  rewritten from "build the BFM" to "verify it on onyx's shapes".
- 2026-11-21: started; step 1 done. The snoop-gather rig
  (`dv/tb/onyx_snoop_gather_rig_tb.sv`: per port an `axi4ace_snoop_master`
  mover into an `axi4ace_snoop_slave` mover, four port sets, N_CACHES
  live) with `dv/tbclasses/onyx_snoop_gather_tb.py` (N `AXI4ACESnoopMaster`
  BFMs as the fanout, N `AXI4ACESnoopSlave` BFMs as the caches, the golden
  a Python port of `l1_pkg::amber_snoop_crresp`, deterministic per-cache
  line data in LINE_BYTES/DATA_WIDTH beats) and
  `dv/tests/test_onyx_snoop_gather_rig.py` (Pattern B; GATE 1 cell, FUNC 4,
  FULL 18: N 2/3/4 x DW 32/64 x gate/func/full). Scenarios: the BFM's
  default responder matrix against the caches' (24 cells, 0 differ -- the
  l1_pkg claim holds); every (state, type) cell on every port with full
  line data (8 beats at 64-bit, 16 at 32-bit); broadcast gathers over the
  MESI-legal patterns with the single-supplier precondition checked;
  per-port timing profiles pulling completion order apart (the count of
  gathers that completed out of issue order is reported and non-zero in
  every multi-port cell); back-to-back per port on all ports at once; a
  compliance checker per port on every CRRESP. From clean: gate 1/1, func
  4/4, full 18/18, every cell 0 mismatches, 0 compliance violations with
  a non-zero check count. The BFM meets the gather shapes.
  **Finding (RDS-DV):** the cache-side BFM cannot stream snoop data. The
  CD probe under the fast profile measures 8 beats over 21 cycles first to
  last (16 over 45 at 32-bit) where back-to-back would be 7 (15): one beat
  every 3 cycles, because `AXI4ACESnoopSlave._snoop_responder` loops
  `cd_channel.send(beat)` and `GAXIMaster.send` waits for the pipeline to
  drain per call (its own `send_burst` docstring says so). Any onyx
  latency or throughput measured through this BFM carries +2 cycles per
  CD beat that is the BFM's, not onyx's. Fix is one line in RDS-DV
  (`send_burst` for the beats); not made here (the DV repo is the
  owner's, and RDS-DV edits are on hold at their word) -- to file against
  RDS-DV #86 or as its own issue, the owner's call. The pair-rig numbers
  are unaffected (jet-prime's snoop side is RTL, not this BFM).
  Also noted, not a defect: `AXI4ACESnoopMaster` allows one outstanding
  snoop per port by default (`allow_multiple_outstanding` exists but the
  CR/CD receive path is sequential), which is the family's one-at-a-time
  convention and onyx v1's; multiple outstanding per cache stays out of
  v1. Next: step 2, the core.
