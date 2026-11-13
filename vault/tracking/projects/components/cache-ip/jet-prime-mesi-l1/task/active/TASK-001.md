# TASK-001: beat HPDcache -- jet-prime's miss path, measured and rebuilt

**Priority:** P2
**Status:** active 2026-11-12 -- fork done, step 1 (jet-prime without the pair fabric) measured; steps 2-4 open
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

Next: step 2.
