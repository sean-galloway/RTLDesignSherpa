# TASK-001: onyx v1 -- the ACE coherency unit per the D rulings, measured against the pair fabric it replaces

**Priority:** P2
**Status:** open (filed 2026-11-20)
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

## The work, in order

1. **The ACE BFM** (D10): the extension of the RDS-DV `axi4` family the
   PRD specifies (field configs with ARSNOOP/AWSNOOP, `axi4ace_*` signal
   patterns, the five D2 transactions as an enum, CRRESP as a bitfield,
   master read/write subclasses, a snoop-slave BFM, a snoop-master BFM
   for the cache side), RDS-DV issue #86. Built and unit-tested before any
   onyx RTL; the rds-dv-axes/bfms rules apply.
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
