# TASK-001: beat HPDcache -- jet-prime's miss path, measured and rebuilt

**Priority:** P2
**Status:** closed 2026-11-18 (active 2026-11-12) -- fork done, step 1 (jet-prime without the pair fabric) measured 11-12, step 2 (multiple outstanding fills) built and measured 11-15, step 3 (pipelined pair fabric) built and measured 11-16, step 4 (the fabric's formal safety argument; two memory-AR defects found and fixed, BUG-001) done 11-17, step 5 (the single-miss path: launch no longer behind the capture, commit tail three cycles) built and measured 11-17 -- under HPDcache at every depth as a pair; control formal on the step-5 RTL: safety prove PASS 11-18 (26:52), covers PASS, the step-3 flat's liveness PASS 11-18 (19:08); the step-5 liveness BMC still running at close (step 115 of 192), its verdict to be appended here
**Owner:** TBD

Filed 2026-11-12 (Sean: "Make a jet-prime and do 1"). The reference
comparison (`projects/components/cache-ip/docs/reference_l1_comparison.md`,
common-ip TASK-003) put jet at 1.0 cycle per resident hit like OpenHW
HPDcache and within 3 % of it on the write-heavy thrash, but 40 % behind on
the 64 KB read-lean thrash at depth 16 (10.7 vs 7.6 cycles per transaction)
and behind the blocking CVA6 cache (9.9). The diagnosis from the sweep
counters: jet keeps seven misses in flight to HPDcache's three yet retires
them at 20 cycles each to HPDcache's 14, because everything after the MSHR is
serial -- one fill engine per cache, one coherence transaction and one memory
read at a time in `jet_pair_fabric` -- and every miss pays the fabric's
grant / snoop / reply round trip even with the peer idle (9 of the 29 cycles
of a single miss, against HPDcache's 20). The memory floor is 8 beats per
64-byte line on the 64-bit bus, about 4.5 cycles per transaction at the
thrash's 50 % miss rate; HPDcache sits at 7.6.

## The fork

jet is frozen as the measured baseline (every jet lane closed, the bin 17
sweeps in the report). jet-prime is jet copied whole at 2be919254 --
`rtl/`, `dv/` (tb, tbclasses, testplans, tests), `formal/jet-prime/` --
with the `jet_prime_` prefix on every module, filelist, harness, test and
formal wrapper, root variable `JET_PRIME_ROOT`, filelist area `jet-prime`,
tests area `jet-prime`. The common-ip slice is reached by `-f` include as
before, never copied. HAS/MAS are NOT copied: jet's books describe
jet-prime until the architecture diverges (step 2), and a second identical
copy is the one nobody edits. Module headers keep their `Documentation:`
pointers into jet's books and carry the fork point on the `Subsystem:` line.

Fork verification: jet-prime gate 19/19 and FULL from clean, formal
prove / prove-live / cover on `jet_prime_control` (results in the progress
log below).

## Plan

1. **Measure jet without the fabric.** jet-prime in the reference rig's
   cache slot (`REF_CACHE_SEL=2`, flow `ref_jetp_bringup`): the same
   injector, memory, bridge, UART and 100 MHz clock as the HPDcache and CVA6
   rows, ACE snoop port tied off, straight onto `sdpram_slave_axi4_axi4`.
   Same geometry, LRU, monitors on, MSHR_COUNT 8 as the jet rig. The row
   against jet's bin 17 row is the fabric's cost to a single core; the row
   against HPDcache is what the cache alone owes.
2. **Multiple outstanding fills inside jet-prime.** The inherited fill
   engine issues one AR and waits for its eight beats; N fills in flight
   need an ID per MSHR entry, R demux by ID, the data-array write port
   arbitrated among returning fills; retire order stays with
   `jet_prime_rsp_seq`.
3. **A pipelined pair fabric.** Per-line serialization (address CAM of
   transactions in flight) instead of one at a time; several memory reads
   outstanding; the AR issued alongside the snoop and its data dropped if
   the peer supplies the line. Grant-after-completion survives for
   same-line conflicts only. The kill rule, the pending-absorption registers
   and both BUG-004-class waits assume one transaction and must be re-argued.
4. **DV and formal to carry 2 and 3.** Pair-rig scenarios with concurrent
   fills to distinct and same lines, the deep-pipelined scenario on both
   cores, formal safety on the fabric's per-line rule; then the standard
   chain (Verilator gates, Genesys2 at 100 MHz, the same sweeps).

Done when jet-prime is under HPDcache's cycles per transaction at every
depth on `r64k_we64` and `r64k_we255`, with the resident-hit row still at
1.0 and jet's FULL grid still green on the fork.

## Progress

### 2026-11-12 -- fork + step 1

- **Fork verified a pure rename.** Normalizing `jet_prime_` back to `jet_`
  and diffing against jet leaves only the `Subsystem:` header lines.
  jet-prime gate 19/19, FULL 149/149 (9:28) from clean; ref-g2 gate 6/6
  (harness AXIL + GAXI read-after-write on hpd / cva6 / jetp); Verilator
  lint of the ref top at `REF_CACHE_SEL=2` clean. Formal
  (`formal/jet-prime/jet_prime_control`): safety prove PASS (4:02), liveness bmc depth 176 PASS (3:16), both covers PASS with every point reached.
- **Step 1 built and measured.** `ref_jetp_bringup` bin 1: 8,339 LUT /
  6,996 FF, WNS +0.360 ns at 100 MHz; smoke init+smoke PASS with ci0
  `rsp_crc` 1814064162 -- the jet rig's own smoke CRC (jet answers stores
  with data where the reference wrappers answer zero), ci1 the null-cache
  CRC. Sweep `ref/results/perf_sweep_jetp_bin1_single_20261112T173844Z.json`,
  55/55 runs, err 0. OOC row identical to jet's (5,892 LUT, +0.356), as it
  must be.
- **Result, cycles per transaction at depth 16 (jet / jet-prime direct /
  HPDcache):** `r64k_we64` 10.65 / 8.13 / 7.64; `r64k_we255` 10.79 / 8.29 /
  10.51; `r128k_we64` 15.74 / 12.00 / 10.90. Depth-1 mean miss latency
  16.4 / 13.9 / 11.4. Hit floor 3 and the 1.00 hit rows unchanged.
- **Split.** The fabric costs a single core 2.5 cycles per transaction at
  every depth on the 64 KB thrash (about 5 cycles per miss, a quarter of
  jet's miss cost). On writes it is the whole gap: without it jet-prime is
  21 % under HPDcache. On reads the remaining 6 % (8.13 vs 7.64) is the
  cache's own: MLP 7.1 at 58 cycles mean latency = seven misses queued
  behind one fill engine retiring at ~15 cycles each, against HPDcache's
  14 with three in flight. So step 2 (concurrent fills) is what takes
  jet-prime under HPDcache on reads; step 3 (the fabric) is what keeps it
  there with a peer attached. Tables and reading:
  `projects/components/cache-ip/docs/reference_l1_comparison.md`.

### 2026-11-15 -- step 2: multiple outstanding fills

- **Built.** `jet_prime_fill` (`rtl/fub/jet_prime_fill.sv`) replaces the
  shared single-outstanding `l1_fill` in `jet_prime_coh_core`: one AXI4
  read ID per MSHR entry plus the no-data upgrade slot, R demuxed by ID
  into a DEPTH-4 staging queue, each beat presented with the entry's
  claimed set/way (the plane's one-deep launch adapter is gone), done with
  the slot's last beat in whatever order the memory returns the bursts.
  `jet_prime_control`: the launch-order completion queue (single read ID)
  became a done queue pushed by the engine's `{idx, cls, pd}` report, and
  the pre-AR snoop rule became per entry (`r_ar_done[MSHR_COUNT]`, set by
  the ID-decoded memory-side AR handshake, cleared at retire). Parameter
  `FILL_INFLIGHT` on the tops (default MSHR_COUNT + 1); the pair rig
  instantiates both caches at 1 because `jet_prime_pair_fabric`'s kill rule
  and 4-deep request queue are argued for a single-outstanding engine per
  direction (step 3 rebuilds the fabric and lifts it). Write-up:
  `docs/delta/01_fill_engine.md` (the first jet-prime chapter that is not
  jet's). No common-ip change.
- **DV.** New `test_jet_prime_fill` (engine vs the AXI4 slave BFM: in-order
  at gate, out-of-order at func, interleaved R at full; cells at full depth
  and at `FILL_INFLIGHT=1`). The control TB's fill stub models the engine
  (several accepted, per-entry AR, bursts in a chosen order), two new
  scenarios (`fill_concurrent_ooo`, `snoop_pre_ar_per_entry`), and a third
  func/full pass runs every scenario under random completion order with
  the done riding the last beat. Core / parity / pair-rig TBs track fills
  by entry and commit in done order. Gate 21/21; FULL 155/155 (8:58; 149 + the six jet_prime_fill cells); ref-g2
  lint at `REF_CACHE_SEL=2` clean.
- **Formal.** The control harness's environment is the new engine (three
  slots, per-slot fairness: AR within 4, done within 24; completion in any
  order); liveness age bound 112 -> 128 (two fills' bursts share one beat
  stream), BMC depth 176 -> 192. Safety prove PASS (boolector, 12:20 wall; step 1 ran about 4 h -- the
  three-slot engine model triples the state the induction carries); liveness BMC to depth 192 PASS (15:41; step 1 depth 176 ran 3:16); both covers PASS, 23/23 safety and 7/7 liveness
  points reached. Formal total 28 h wall for the step; the proof cost is now the long pole of a jet-prime step and is worth
  a look before step 3 adds the fabric model.
- **Board.** `ref_jetp_bringup` bin 2: 8,559 LUT / 7,182 FF (step 1: 8,339 / 6,996), WNS +0.532 ns at 100 MHz; smoke init+smoke
  PASS, ci0 `rsp_crc` 1814064162 (the jet rig's CRC, unchanged from step 1); sweep `ref/results/perf_sweep_jetp_bin2_single_20261115T200018Z.json`, 55/55 runs, err 0. OOC jetp:
  6,047 LUT / 5,394 FF (jet 5,892 / 5,258), 16 RAMB36, 1,888 LUTRAM, WNS +0.118 ns; the worst path runs from the staging queue's read pointer through the slot set lookup into the data-array address -- a watch item (a registered queue output is the fix if it bites) (step 1 row kept as `results/ooc/jetp_step1`).
- **Result, cycles per transaction at depth 16 (jet / jet-prime s1 /
  jet-prime s2 / HPDcache):** `r64k_we64` 10.65 / 8.13 / 5.71 / 7.64;
  `r64k_we255` 10.79 / 8.29 / 8.14 / 10.51; `r128k_we64` 15.74 / 12.00 /
  8.00 / 10.90. Depth 4: 6.89 / 9.10 / 8.91 against HPDcache's 8.22 /
  10.53 / 11.37. Depth 1 unchanged (14.88 vs HPDcache 13.73). MLP on
  `r64k_we64` d16 7.1 -> 10.8 (OUTST_MAX 12, the injector's ceiling);
  hit floor 3 and the 1.00 hit rows unchanged.
- **Reading.** From depth 4 up jet-prime is under HPDcache on every miss
  configuration: 25 % on the read-lean thrash, 23 % on the write-heavy
  one, 27 % at four times the cache -- the done criterion's two
  configurations at depths 4 and 16, on the single-cache rig. Depth 1
  (one miss at a time) keeps its ~1-cycle gap: that is the AR register
  plus the lookup pipeline, not the engine. The read-lean row is now at
  the memory port: 5.71 cycles per transaction at a 50 % miss rate is
  11.4 cycles per line against the 8-beat floor. The write-heavy row moved
  least (8.29 -> 8.14); the likely limiter (not measured here) is the
  dirty-victim path -- one capture at a time with the launch held behind
  it -- and the one write channel, not fills. So the next lever on the
  single-cache rig is probably the capture/launch serialization (measure
  first); the next lever against HPDcache on the PAIR rig is the fabric
  (step 3): adding its measured 2.5 cycles per transaction to 5.71
  estimates the pair-rig jet-prime at ~8.2 on `r64k_we64`, 7 % behind
  HPDcache, until it is pipelined.

### 2026-11-16 -- step 3: the pipelined pair fabric

- **Built.** `jet_prime_pair_fabric` rebuilt around a transaction table
  (`FAB_SLOTS`, the memory read ID is the slot): per-line serialization
  from the request pulse to the requester's RETIRE, grant one per cycle
  with round-robin between directions, the requester's AR taken the cycle
  after the grant (the entry turns post-AR only then), the memory AR
  issued once the peer accepted the AC and its beats dropped (or the AR
  suppressed) on a DataTransfer verdict, snoops per peer in grant order
  with `SNOOP_INFLIGHT` outstanding, CD lines in per-slot buffers (one LUTRAM array per peer;
  the first build's single array written from both peers had two write ports and synthesized as
  9 k flops behind 272:1 muxes -- 35,879 LUT for the fabric alone out of context, caught by the
  bitstream's LUT count),
  replay per direction behind the memory beats, the write port
  round-robin over {wb0, wb1, absorb} with a WB AW held while a slot on
  its line has no verdict yet.  Gone: the kill rule, the drain guard, the
  upgrade-priority grant, the `peer_state` / `lkup_live` inputs.  New
  sideband `coh_done_valid/id` from `jet_prime_top` (control `cu_done_o`
  + the retire; the entry's read ID) is what releases the lock -- the
  responder's `sn_safe` hold covers the done-unretired window except for
  the engine's staging-queue cycles, and a snoop there would be answered
  from the bypass without data for a fill that must stay ordered before
  it.  Write-up: `docs/delta/02_pair_fabric.md`.  The pair rig and the
  ref harness run `FAB_SLOTS = 2 * (MSHR_COUNT + 1)`, both caches at full
  fill depth.  Found on the way: the pending-queue depth is not one per
  direction -- the read transport skids ARs, so a cache runs up to three
  launches ahead of the AR the fabric holds (PEND_DEPTH 4 holds; the
  overflow flag is TB-checked); and two same-cycle push/pop orderings in
  the snoop queues (the pop's shift overwrote the push) that the first
  gate cell hung on.
- **DV.** The pair-rig TB's fabric layer re-keyed on (direction, line):
  every AC scored against the live transaction on its line, CR/CD per peer
  in AC order, the memory read by slot (after the AC, never for an
  upgrade, dropped or suppressed on DT, completed otherwise), grant order
  and the per-line rule at every grant, slot release after the retire;
  scenario (a) checks the forwarded fill's read was dropped or suppressed;
  `DeepPipelinedMisses` added to the testplan.  Gate 21/21; FULL 155/155 (9:01, on the final RTL
  with the buffer split; the FULL before it lost one cell to the TB itself -- the fabric stat check ran before the quiescence wait and the last
  DataTransfer slot freed after it -- so the end-of-run audits now follow the quiescence);
  ref-g2 lint at `REF_CACHE_SEL=2` and `3` clean; ref-g2 gate 7/7 (the new `jetpp` cell
  included).
- **Formal.** `jet_prime_control` gained one output (`cu_done_o`); the
  flat regenerated (the diff is the port and line numbers) and the three
  proofs relaunched on it 2026-11-16 17:20 (safety, liveness depth 192, covers) --
  running at the step-3 commit (step 2's run took 28 h); the verdict is recorded with step 4.  The fabric's own formal safety
  argument (the per-line rule) is step 4.
- **Board.** New `REF_CACHE_SEL=3` (flow `ref_jetpp_bringup`): two
  jet-primes through the fabric, one per injector -- the jet rig's
  structure with jet-prime's RTL. Bin 2 (the buffer split): 17,853 LUT / 11,884 FF, WNS +0.326 ns
  at 100 MHz under the 0.2 ns uncertainty budget (the worst path is the step-2 watch item, the fill
  engine's staging-queue read pointer into the data-array address -- the long pole; the fabric is
  not on it); smoke init+smoke PASS on both injectors, ci0 `rsp_crc` 1814064162 (the jet rig's);
  sweeps `ref/results/perf_sweep_jetpp_bin2_single_20261117T023054Z.json` (injector 1 idle) and
  `perf_sweep_jetpp_bin2_dual_20261117T023233Z.json` (both active), 55/55 runs each, err 0.
  Bin 1 (the first build, 48,946 LUT / 21,439 FF, WNS +0.006) swept bit-identically to bin 2 in
  every cycle count and CRC (`perf_sweep_jetpp_bin1_*`), as a pure restructuring must.
  Fabric alone, out of context at 10 ns, `FAB_SLOTS=18` (`ref/results/ooc/jetp_fabric`): 4,886 LUT
  (3,854 logic + 1,032 as the two line-buffer memories) / 1,655 FF, WNS +2.30 ns, ten levels on the
  worst path (the grant cone: queue count -> candidate -> line CAM -> slot load); the first build's
  fabric was 35,879 LUT / 10,985 FF (the two-write-port buffer array, see Built).
- **Result, cycles per transaction at depth 16 (jet / s2 / s3 / HPDcache):**
  `r64k_we64` 10.65 / 5.71 / 5.78 / 7.64; `r64k_we255` 10.79 / 8.14 / 8.61 / 10.51;
  `r128k_we64` 15.74 / 8.00 / 8.12 / 10.90. Depth 4: 11.40 / 6.89 / 7.05 / 8.22,
  12.01 / 9.10 / 9.52 / 10.53, 16.08 / 8.91 / 9.10 / 11.37. Depth 1: 17.42 / 14.88 / 15.39 /
  13.73, 21.13 / 18.59 / 19.11 / 13.65, 24.02 / 20.27 / 21.02 / 18.83. Both injectors active
  on the same region (ci0/ci1, jet bin 17 -> s3): `r64k_we64` d16 10.74/10.70 -> 5.81/5.83,
  d4 11.48/11.46 -> 7.08/7.11; `r64k_we255` d16 10.90/11.01 -> 8.66/8.65; `r128k_we64` d16
  16.02/15.82 -> 8.11/8.10. Hit floor 3, hit rows 1.00, MLP 10.8 unchanged.
- **Reading.** The fabric's cost to a single core fell from 2.5 cycles per transaction
  (step 1's measurement of jet's fabric) to 0.07 on the read-lean thrash at depth 16 and 0.5 at
  depth 1 -- the grant and the AR take, the two registered stages a miss crosses before its
  memory read goes out. The write-heavy row keeps 0.47 of it (more lines, each snooped, and the
  write-back AW waiting out its line's verdict). With both cores active the numbers are the
  single-core numbers: the fabric is no longer what a peer costs. Against the done criterion:
  under HPDcache at depths 4 and 16 on both `r64k_we64` and `r64k_we255` as a pair (24 % and
  18 % at depth 16), the resident-hit row still 1.00, jet's FULL grid green on the fork; depth 1
  stays 1.7 cycles over -- the s2 cache's single-miss path (AR register + lookup pipe + the
  fabric's two stages), the next lever if depth 1 is to be won.

### 2026-11-17 -- step 4: formal on the fabric

- **Built.** `formal/jet-prime/jet_prime_pair_fabric`: the fabric alone at
  the tiny geometry (8-bit addresses = 16 lines, 16-byte lines on a 32-bit
  bus = four beats, `AXI_ID_WIDTH` 3, `FAB_SLOTS` 4, `SNOOP_INFLIGHT` 2),
  both caches, both snoop responders and the shared memory free inputs
  under their documented contracts (the harness header is the assumption
  inventory). The flat is the fabric's own filelist through
  `make/formal_flat.mk`, specialized parameterless; `read_verilog -mem2reg`
  turns the transaction table's unpacked arrays into per-element wires
  that `expose` reaches (the queue HEADS are exposed, not the queues, so
  no property depends on how yosys linearizes a 2-D array). Twenty-seven
  safety properties (the per-line rule as one valid slot per line and no
  grant to a held line; the lock dropping only after the requester's own
  retire and only with its last beat received and its read drained; one
  AR take per grant with the slot's line and class; the memory AR after
  the AC accept, never for an upgrade or twice, held once presented; every
  R beat to its direction with the requester's own ID, a memory beat never
  for a DataTransfer slot, exactly the beats each AR asked for; AC/CR/CD
  bookkeeping; the write-back hold at selection; the absorption's address
  and ID; no pending-queue overflow; AXI/ACE valid-payload stability on
  the memory AR, both R channels and both ACs), nineteen covers (all
  reached by step 14), ten mutations each failing the property written for
  the mechanism it breaks (`scratchpad` runs; the list in delta 02).
- **Found and fixed (jet-prime BUG-001).** (1) The memory AR was a
  combinational lowest-index pick presented straight on the channel: during
  an `arready` stall a lower slot's AC acceptance re-pointed it at another
  slot with ARVALID high (AXI A3.2.1) -- `ap_mar_stable`, step 6, the
  proof's first second. The pair rig, the ref-rig gate and two bitstreams'
  sweeps had passed it: the memory's two-deep burst queue rarely stalls the
  AR, the slave samples at the handshake, and nothing memory-side checked
  stability. Fix: the presented AR is held until taken (`r_mar_vld/slot`);
  a DataTransfer verdict landing on a presented AR drains its beats instead
  of suppressing it. (2) With the hold, a slot can be deliverable before
  its held read issues, and the release fired in the handshake's own cycle
  with the read outstanding -- `ap_free_complete` / `ap_mo`, step 15, seven
  minutes into the re-prove. Fix: a slot whose AR is presented this cycle
  is not free. Board footprint of (1): bin 3 against bin 2 differs only at
  depths 8 and 16, by at most 0.14 % of the cycles and in bin 3's favour,
  with every CRC equal.
- **DV.** The pair-rig TB checks every cycle that a stalled memory AR
  holds (valid, id, addr) and scores a memory AR after a DataTransfer
  verdict only when it was first presented after it. Gate 21/21; FULL
  155/155 (11:20) from clean on the final RTL; ref-g2 gate 7/7.
- **Formal cost.** BMC, claimed as such. Timing every property alone to
  depth 22 split them three ways: eleven local ones in ~10 s, ten in
  4-12 min, and three end-to-end bookkeeping properties (IDs in flight,
  beats per ID, the CD beat's slot) at ~2.5x per step. So two tasks:
  `prove` (24 properties incl. three helper invariants from a k-induction
  attempt that did not close) at depth 24, `prove_book` (the three) at
  depth 16; covers at 40. Final run on the final RTL (11-17): covers PASS
  (8 s, 19/19 reached), `prove` PASS (38:30 wall), `prove_book` PASS
  (1:00:04 wall). Shrinking addresses (16 -> 8 bit), data (32 ->
  8) and IDs (3 -> 2 bit) did not move the per-step cost; engines
  (boolector, bitwuzla, yices, abc bmc3, abc pdr) did not either. Written
  up in `vault/handbook/dv/formal.md`.
- **Control formal (step-3 flat, relaunched 11-16 17:20).** Safety prove
  PASS (boolector, 11:57 wall). Liveness BMC depth 192 still running at this
  commit (step 151 of 192 at 09:01, 3:44 solver time). Covers queued behind
  it; the verdict goes in the next step's commit.
- **Board.** `ref_jetpp_bringup` bin 3 (the fixed fabric): 17,932 LUT /
  11,889 FF, WNS +0.043 ns at 100 MHz under the 0.2 ns uncertainty budget
  -- the same worst path as bin 2 (the step-2 watch item: the fill
  engine's staging-queue read pointer into the data-array address, 24
  levels), placed at +0.326 there; the budget is what carries the spread.
  Smoke init+smoke PASS on both injectors (ci0 `rsp_crc` 1814064162);
  sweeps `perf_sweep_jetpp_bin3_single_20261117T144843Z.json` and
  `perf_sweep_jetpp_bin3_dual_20261117T145022Z.json`, 55/55 each, err 0.
  Fabric alone OOC at 10 ns, `FAB_SLOTS=18`: 4,923 LUT (3,891 logic +
  1,032 memory) / 1,660 FF, WNS +2.76 ns, ten levels (step 3: 4,886 / 1,655 at +2.30).
- **Result.** Unchanged at two decimals except `r128k_we64` d16 8.12 ->
  8.11 (dual 8.11/8.10 -> 8.10/8.09, `r64k_we64` d16 dual 5.81/5.83 ->
  5.81/5.82); the comparison report regenerated from bin 3.

### 2026-11-17 -- step 5: the single-miss path

- **Why.** The plan's four steps were done, the done criterion ("every
  depth") was not: depth 1 was over on both configurations (`r64k_we64`
  15.39 vs HPDcache 13.73, `r64k_we255` 19.11 vs 13.65). The sweep's
  latency histograms split it (a quarter of the read-lean misses and 96 %
  of the write-heavy ones in [32, 64) cycles; every HPDcache miss in
  [16, 32)), and a cycle-by-cycle trace of the pair-rig gate cell with a
  waveform dump (`docs/delta/03_single_miss_path.md` has the table) put a
  clean miss at 23 cycles and a dirty-victim miss at 33: the launch waited
  behind the whole victim capture, and the tail from the last beat to the
  response was six cycles, three of them the commit's own bookkeeping.
- **Built.** (1) The MAS ch02/01 contract moved from the launch to the
  hazard: `jet_prime_control` exports the capture's `(set, way)`
  (`cap_set_o`/`cap_way_o`), `jet_prime_fill` holds a beat for that way at
  its staging-queue head (`cap_hold_i`/`cap_set_i`/`cap_way_i`; head-of-
  line by design, bounded by the capture); the plane's launch gate is
  gone, the launch goes out in the alloc cycle. (2) The commit tail: a
  completion on an empty done queue is snapshot in its own cycle (never
  in a snoop grant cycle; a merge in that cycle is held), `C_MERGE` leaves
  as the last slot advances, and the first deposit rides with the install
  (a last read slot's word deposited straight off the sync port). No
  common-ip change; the fabric is untouched.
- **Checks that moved with the timing** (each read as a design bug
  first; handbook `dv/checks-encode-events-not-cycles`,
  `design/enforce-the-contract-at-the-hazard`): the tops' launch-gate
  assertions (now "no beat into the captured way"); the core TB's
  launch-time `cap_busy` check (now at the beat) and its armed-downgrade
  slot-state read (now after the retire -- the response is two cycles
  ahead of the claim's release); the control TB's commit watcher (first
  sample is the cycle it starts in) and its deposit attribution (by the
  commit's `w_cmt_cpl` tap, not by tag: a hit granted the just-released
  tag deposited inside the window at FULL -- "one deposit per requester:
  got [8, 9, 0, 1, 8]"); the control formal environment (unconditional
  accept, beats held by entry while `cap_busy`). `jet_prime_fill` gained
  `capture_hold`.
- **DV.** Lint clean at two parameter sets. Gate 21/21; FULL 155/155 (9:17)
  from clean on the final RTL; ref-g2 gate 7/7.
- **Formal.** Control flat regenerated (two new ports; `formal_status
  --check-flats` CURRENT 2/2). Verdicts as they landed: the step-3 flat's
  liveness BMC (depth 192, boolector; step 4's pending verdict) PASS
  2026-11-18 00:28 after 19:08 of solver time; the covers on the step-5
  flat PASS 00:30 / 00:31 (23 of 23 control covers and 7 of 7
  liveness-wrapper covers reached; 2:08 and 0:45); the step-5 safety
  prove (BMC depth 64, boolector) PASS 2026-11-18 13:47 after 26:52 --
  against 11:57 for the same depth on the step-3 flat; the last three
  steps took 3:20, 5:13 and 5:00, so the step-5 environment (the launch
  accepted unconditionally, beats into a captured way excluded by
  assumption) carries more state per unrolled step. The step-5 liveness
  prove (depth 192) launched 00:31 once the step-3 run freed its work
  directory; at 13:47 it was at step 115 of 192 after 13:09, having
  slowed from the step-3 run's pace to about 80 min per step from step
  110 on. The fabric formal is step 4's (fabric unchanged).
- **Board.** `ref_jetpp_bringup` bin 4: 18,126 LUT / 11,890 FF, WNS
  +0.019 ns at 100 MHz under the 0.2 ns uncertainty budget (worst path
  still the fill engine's staging-queue read pointer into the data-array
  write address; bin 3 placed it at +0.043). Smoke init+smoke PASS, ci0
  CRC the jet rig's (1814064162). Sweeps
  `perf_sweep_jetpp_bin4_single_20261117T191112Z.json` and
  `perf_sweep_jetpp_bin4_dual_20261117T191252Z.json`, 55/55 each, err 0;
  every single-core CRC equals bin 3's. Cache alone OOC
  (`ref/results/ooc/jetp5`): 6,010 LUT / 5,399 FF, WNS +0.321 ns (s2's
  cache 6,047 / 5,394 at +0.118).
- **Result, cycles per transaction (s3 -> s5, HPDcache).** `r64k_we64`
  d1 15.39 -> 12.76 (13.73), d2 9.55 -> 7.91 (9.79), d4 7.05 -> 6.10
  (8.22), d8 5.99 -> 5.41 (7.67), d16 5.78 -> 5.29 (7.64); `r64k_we255`
  d1 19.11 -> 13.17 (13.65), d2 11.79 -> 9.31 (11.04), d4 9.52 -> 8.65
  (10.53), d8 8.72 -> 8.53 (10.51), d16 8.61 -> 8.51 (10.51); `r128k_we64`
  d1 21.02 -> 16.94 (18.83), d16 8.11 -> 7.58 (10.90). Depth-1 misses all
  in [16, 32), max 26, mean 20.2 (HPDcache 20.5). Dual-active = single
  (`r64k_we64` d1 12.78 / 12.74, d16 5.32 / 5.34). Hit floor 3, hit rows
  1.00, MLP 10.6.
- **Reading.** The done criterion is met: under HPDcache at every depth
  on `r64k_we64` and `r64k_we255` as a pair, the resident-hit row at 1.0,
  jet's FULL grid green on the fork. The depth-1 margin on the write-heavy
  row is 3.5 % (0.48 cycles per transaction) and is the resident hit's:
  jet answers a hit in 3 cycles to HPDcache's 2, half the transactions at
  depth 1 are hits, so the hit costs 0.5 cycles per transaction there and
  shows as the remaining gap in every resident configuration at depths 1
  and 2. That is the lookup pipeline (jet v3's 100 MHz closure), not the
  miss path, and it is not in this task's criterion.

### 2026-11-18 -- closed

The control formal reruns landed: safety prove PASS, covers PASS on the
step-5 flat, the step-3 flat's liveness PASS. The done criterion (step 5,
4db2f29e5) was met at every depth as a pair, so the task closes. One run
is still out: the step-5 liveness BMC (depth 192), at step 115 of 192 at
the close and slowing (see the step-5 Formal bullet). Its verdict is
appended below when it lands; if it keeps crawling, a tighter liveness
environment for the step-5 control is a separate item, not a reason to
hold this one open. The 2-cycle hit (HPDcache's floor) is TASK-002 (open,
2026-11-17): the v3 lookup pipeline's capture/classify split against
100 MHz.
