# TASK-001: beat HPDcache -- jet-prime's miss path, measured and rebuilt

**Priority:** P2
**Status:** active 2026-11-12 -- fork done, step 1 (jet-prime without the pair fabric) measured 11-12, step 2 (multiple outstanding fills) built and measured 11-15, step 3 (pipelined pair fabric) built and measured 11-16; step 4 (formal on the fabric, the deep scenarios) open
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

Next: step 3 (the per-line pipelined pair fabric) -- lift `FILL_INFLIGHT`
on the pair rig with it.
