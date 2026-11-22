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
- 2026-11-21: step 2 done -- the core. `rtl/top/onyx_ccu.sv` (filelist
  `rtl/filelists/onyx_ccu.f`; the `onyx` area and `ONYX_ROOT` registered in
  `bin/filelists.toml`, `bin/filelist_registry.py`,
  `bin/TBClasses/shared/filelist_utils.py`, `make/formal_flat.mk` and the
  reference rig's Makefile) is `jet_prime_pair_fabric` generalized to
  N_PORTS (2-4, D11) under the D rulings: per-port pending queues and a
  rotating-priority grant (D5 per-line lock, SERIAL_MODE bring-up), a
  transaction table whose slots count the peers yet to accept the AC and
  yet to answer (the tagged gather of D4; the verdict the OR of the CRs'
  DataTransfer, PassDirty from the supplier), broadcast AC queues per
  peer never including the requester (D3), the memory AR issued once
  every peer accepted its AC or -- DEFER_AR -- once every CR is in with
  no DataTransfer (D6, both modes), memory beats held until the gather
  completes and dropped when a peer supplied, per-requester-port snoop
  data buffers with a round-robin CD write per buffer, per-port replay
  engines, the write port round-robin over N write-backs and the
  absorption, retire-sideband release. Cache-side signals are unpacked
  arrays over N_PORTS; the pair fabric's debug tap names are kept. Lint
  clean at N 2, 3, 4 (one false combinational cycle fixed: the gather
  flags moved out of the free-computation block). Not in the core yet:
  the ACE-Lite IO port (D1), monlite taps (D9), ARSNOOP decode.
  **Proof that onyx replaces the fabric:** `dv/tb/onyx_pair_rig_tb.sv` is
  the jet-prime pair-rig harness with onyx_ccu (N_PORTS 2) in the
  fabric's place, instance name and taps kept, so jet-prime's pair-rig TB
  (the 2-cache lockstep model with the fabric rules, the ACE compliance
  scoring, both CPU ports driven) runs unchanged through
  `dv/tests/test_onyx_pair_rig.py` on the jet-prime grid: from clean,
  gate 4/4 pair-rig cells + 1 gather, func 6 + 4, full 26 + 18 -- 44 of
  44, every cell 0 mismatches (gate 4,200-4,659 checks, func 33-34 k,
  full 227-239 k per cell, the knob sweep MSHR {2,16} x VICTIM {1,4} x
  {LRU,FIFO} at both geometries included). The gate reports are
  identical to jet-prime's own fabric cells line for line (checks 4,736,
  grants [35, 31], 17 lines forwarded, 48 pass-throughs, 16 absorptions,
  65 memory reads, 17 beats dropped), so onyx at N=2 is the fabric's
  behavior, not just its contract.
  **Area, manager alone, out of context at 10 ns** (`make ooc
  CACHE=onyx2` / `CACHE=jetp_fabric`, both at 18 slots, SNOOP_INFLIGHT 2,
  clocked on `clk` -- the OOC flow now takes the clock port per target):
  onyx_ccu 4,628 LUT / 1,664 FF / 1,296 LUTRAM, WNS +2.885 ns, 9 levels;
  jet_prime_pair_fabric 4,300 / 1,660 / 1,296, +2.757, 10 levels (the
  rerun reproduces the committed fabric row exactly). The generalization
  costs 328 LUT (7.6 %) at N=2 -- the per-buffer CD arbitration, the
  rotating grants and the per-slot peer counters -- and no flops or
  LUTRAM, with timing unchanged. Next: step 4 (formal: the fabric
  harness pattern on onyx at N=2 and N=3), then step 5's core-alone DV
  with BFM caches, step 6's reference-rig slot (REF_CACHE_SEL 4) and
  board sweeps in both D6 modes, and the IO port / monlite taps as the
  remaining core steps.
- 2026-11-21: steps 4 and 6 done, step 7 begun. **Step 4, formal:**
  `formal/onyx/onyx_ccu` (Makefile, `onyx_ccu.sby`, `formal_onyx_ccu.sv`,
  flat bb83dd7f71 from `onyx_ccu.f` at the fabric's geometry ADDR 8 /
  LINE 16 / BUS 32 / ID 3 / N_PORTS 2 / SLOTS 4 / SNOOP_INFLIGHT 2) is the
  pair fabric's harness carried over with onyx's changes (the accept and
  answer counters read through the DUT's all-accepted and gathered flags;
  the AR waits on all-accepted and no DT; the flag order DT -> all
  accepted, PD -> DT, gathered -> all accepted; `CDREADY` depends on
  `CDVALID`; the array ports packed element 0 at the top, as sv2v does).
  First run: `ap_table_flags` at step 3 and `ap_r_inflight` at step 5 --
  a real weakness and a harness gap together: the memory could present a
  beat nobody asked for in the one cycle after reset before its contract
  armed, and the gather counters read "complete" for an invalid slot, so
  onyx forwarded it (the fabric's explicit verdict bit had shielded the
  same harness). RTL fix: both memory-R routes qualified with a read
  outstanding (`w_mr_live`; a beat for no read is held, as the sim check
  names it); harness fix: reset held for the two steps before the
  contracts arm. Then: `cover` 19/19 reached (by step 7); `prove` (24
  properties, depth 24) PASS 20:30; `prove_book` (3, depth 16) PASS
  14:41; mutations on scratch copies of the flat -- the gather declared
  complete at once (FAIL `ap_table_flags` step 3), the fanout including
  the requester (FAIL `ap_ac_legal` step 3), a second grant to a port
  with its AR untaken (FAIL `ap_grant_one_ar` step 3). Lesson for the
  handbook: three sby tasks of one `.sby` launched concurrently in one
  directory collide on the status database (`no such table:
  task_property_status`) and die in a second with no verdict -- run them
  sequentially or from copies. After the RTL fix: pair rig gate 4/4 again
  (reports unchanged).
  **Step 6, the reference rig:** `ref_harness.sv` carries onyx as
  `REF_CACHE_SEL` 4 (DEFER_AR 0) and 5 (DEFER_AR 1) inside the pair
  block, the two caches shared with SEL 3 and only the manager swapped;
  flows `ref_onyx_bringup` / `ref_onyxd_bringup`; the rig top filelist
  includes `onyx_ccu.f`; lint clean at SEL 3/4/5. Builds at 100 MHz under
  the 0.2 ns budget: SEL 4 WNS +0.006 ns, SEL 5 +0.000 ns (0 failing
  endpoints), the worst path jet-prime's fill-engine staging read pointer
  into the data-array address in both (bin 7's path); SEL 5 18,633 LUT /
  11,881 FF (bin 7 18,241 / 11,896); SEL 4 18,672 / 11,900 (from a rebuild after
  SEL 5's report set overwrote it; the rebuild reproduced WNS +0.006). Board: both programmed, init + smoke PASS,
  single (injector 1 idle) and dual 55-point sweeps in both modes, err 0.
  **SEL 4 equals bin 7 exactly**: every one of the 55 single and 55 dual
  cells reproduces bin 7's cycle count on both injectors, every CRC equal
  -- PRD criterion 6 met, and the strongest statement of "onyx replaces
  the fabric". SEL 5 (deferred read): resident cells equal, `r16k_we64`
  +0.4 to +0.9 %, thrash depth 1 `r64k_we64` 12.27 -> 13.67 (+11.4 %),
  `r64k_we255` 12.68 -> 13.70 (+8.1 %), `r128k_we64` 16.69 -> 18.74
  (+12.2 %), depth 16 +1.8 / +0.2 / +1.5 %; dual the same shape; hit floor
  2, MLP 10.72. The elision rate (memory reads not issued) is not counted
  by the rig; a memory-side AR counter is a D9 tap and the next
  measurement. Results `perf_sweep_onyx_bin1_{single,dual}_20261121T1342*`
  and `perf_sweep_onyxd_bin1_{single,dual}_20261121T1345/47*`;
  `ref_compare.py` has the two columns and a managers-alone table; the
  comparison report carries the reading.
  **Step 7, docs (begun):** the onyx HAS at 0.3 -- chapters 2 to 6
  rewritten to the as-built design (pipeline, decision layer, serializer,
  fanout/gather; the as-built port contracts; parameters; verification;
  characterization), the component README, the PRD at v0.8 with the
  criteria's measured status (1, 2, 6 met; 3 safety at N = 2; 4 not
  built; 5 measured). The ACE interface definition's handshake sentence
  corrected (READY may wait for VALID; the earlier text forbade a
  dependency AXI permits). Remaining in TASK-001: the D1 ACE-Lite IO
  port, the D9 monlite taps (and with them the elision-rate count), the
  N = 3 formal harness, a core-alone BFM-cache rig, a redrawn block
  diagram, and the MAS.
- 2026-11-21 **Step 6b, D9 observation (sim done; board in progress):**
  `onyx_ccu` exposes one-cycle event taps (grant with class / port / slot,
  AC per peer, gather-done per answering port with slot / DT / PD, memory
  AR, read-wasted per answering port, absorb, write-back, lock-wait per
  port); `onyx_pkg` carries the codes 0x20-0x27 (0x21 SNOOP_OUT retired as
  TXN_START x peers); `onyx_monlite` turns them into house MonBus packets
  (agent 0x00A3) and `onyx_counters` keeps six exact 32-bit counts
  (transactions, lines supplied, memory reads, reads wasted, absorptions,
  write-backs; clear pulse + freeze level shared with the rig's tally);
  `onyx_top` composes ccu + observer + counters behind USE_MONITOR.
  Three observer findings on the way, each a count that did not match the
  TB's model: (1) the caches' two-intake engine lost 9 of 66 TXN_START
  packets at queue depth 4 AND at 16 -- the intake, not the depth; it is
  now two-deep per-class holders draining one a cycle round-robin, with
  only a full holder losing, counted; (2) a write the queue refused
  vanished uncounted -- the take is gated on the FIFO's own wr_ready, not
  a shadow count; (3) two peers completing two different slots' gathers
  in one cycle collapsed into one `evt_gather` bit, an event lost that
  nothing counted (once a gate run) -- the gather and read-wasted taps are
  per answering port and the counters add a popcount. The pair-rig TB
  (`OnyxPairRigTB`) now holds the counters to its model exactly
  (transactions == grants, memory reads == ARs, absorptions, reads wasted
  == dropped reads, lines supplied == forwarded lines) and the observer to
  honesty (each class <= its counter, shortfall covered by its own drop
  reports). onyx gate 5/5, func 10/10, full 44/44 from clean; in the full
  cells the observer carries ~13,700 packets with 0 to 8 lost, all
  reported. Reference rig: the pair block carries a 3-client
  `monbus_arbiter` -> `monbus_axil4_group_1wr` -> `monbus_tally_axil` on
  bridge slaves 3/4/5 and the six counters at harness CSR 0x020-0x034;
  host profile `ref-onyx` (bins 11-17 onyx) and `--profile` on the sweep,
  which reads the counters in the tally's frozen window. Lint clean at
  SEL 0/3/4/5. SEL 4 / 5 bitstreams building; sweeps with the profile to
  follow (`perf_sweep_onyx*_bin2_*`). Formal prove + prove_book relaunched
  on the regenerated flat (ports changed; the 27 properties do not read
  the taps). Measured already in sim, DEFER_AR 0: every supplied line is a
  wasted read (supplied == read_wasted, 138/138, 222/222 ...), 3.6 to 6 %
  of the memory reads in the pair rig's full cells.
- 2026-11-22 **Step 6b, board:** SEL 4 and SEL 5 rebuilt with the tally
  chain, observer and counters (bin 2): WNS +0.001 / +0.027 ns at 100 MHz,
  27,872 / 27,143 LUT, 25,877 / 25,854 FF (the chain the jet rig also
  carries: +9,200 LUT, +14,000 FF over bin 1). Programmed, init + smoke
  PASS, single and dual 55-point sweeps in both modes with
  `--profile ref-onyx`: **all 220 cells cycle-identical to bin 1** (the
  observation costs no cycle), err 0. First host run failed on the regmap
  (my six entries had the wrong key shape: `address`/`name`/`size`/`type:
  reg`, not `offset`/`type: register`); fixed, rerun clean. **The D6
  trade, counted:** parallel mode (SEL 4) wastes exactly one read per
  supplied line in every cell but the deepest (reads wasted == lines
  supplied; `r16k_we64` 116 of 381 reads = 30 %, `r64k_we64` 192 of
  20,240 = 0.9 %, `r64k_we255` 637 of 20,303 = 3.1 %, `r128k_we64` 638 of
  30,083 = 2.1 %; at depth 16 a few snoops answer before the AR is taken
  and 11 of 638 reads are never issued); deferred mode (SEL 5) wastes 0 in
  all 110 cells and issues exactly `lines supplied` fewer reads (381 ->
  265, 20,240 -> 20,048, 20,490 -> 19,666, 30,083 -> 29,445). The
  single-injector cells are the control: supplied 0, wasted 0, reads equal
  in both modes. **MonBus on the board:** the pair block's one channel
  (AXI-Lite group writer, three observers) saturates at the thrash cells'
  rates: bin 11 reads 12,613 against 20,240 transactions at depth 1,
  3,891 at depth 16, two drop reports a cell with an 8-bit payload;
  resident and warm-up cells agree with the counters exactly. Filed as
  onyx ISSUE-001 (the bins are lower bounds; the counters are the
  instrument). Formal on the regenerated flat (per-port taps): prove PASS,
  prove_book PASS. HAS ch04/04 and ch06/02 (Table 6.3 observation rows,
  Table 6.5 the counted trade), PRD criterion 4 built and measured,
  README, `ref_compare.py` counter table, comparison report. Results
  `perf_sweep_onyx_bin2_{single,dual}_20261122T1509/1510*` and
  `perf_sweep_onyxd_bin2_{single,dual}_20261122T1513/1515*`.
