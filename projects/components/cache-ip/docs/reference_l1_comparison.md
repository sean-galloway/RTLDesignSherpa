# amber, jet and two reference L1s on one rig

**Status:** 2026-11-11, complete for the four caches (cache-ip common-ip
TASK-003, closed); 2026-11-12, fifth column -- jet-prime (jet's RTL, forked)
in the reference slot with NO pair fabric (jet-prime TASK-001 step 1);
2026-11-15, sixth column -- jet-prime step 2, `jet_prime_fill` with one AXI4
read ID per MSHR entry, several fills in flight (the step-1 column is kept as
the single-engine control); 2026-11-16, seventh column -- jet-prime step 3,
the jet-prime PAIR through the pipelined `jet_prime_pair_fabric`
(`REF_CACHE_SEL=3`, injector 1 idle): the first coherent, fabric-attached
column; 2026-11-17, eighth column -- jet-prime step 5, the single-miss
path (the fill launch no longer waits behind the victim capture, the
commit answers three cycles after the last beat), the same pair rig;
2026-11-19, ninth column -- jet-prime TASK-002, the 2-cycle resident hit
(the arriving request's data address leads in its capture cycle, a read
hit answers from the port and a write hit acks in its classify cycle),
the same pair rig: the column to read against jet's and HPDcache's;
2026-11-21, tenth and eleventh columns -- onyx (onyx TASK-001): the same
jet-prime pair behind `onyx_ccu` in the pair fabric's place, with the
memory read alongside the snoop (`REF_CACHE_SEL=4`) and deferred until the
gather (`REF_CACHE_SEL=5`), plus a table of the two managers alone;
2026-11-22, the onyx counters table -- the D6 trade counted on the board
(reads issued, lines supplied, reads wasted) from the bin 2 builds with
the pair block's tally chain. Re-run `ref/bin/ref_compare.py` after any
new sweep.
**Rig:** Genesys 2 (Kintex-7 325T-2), 100 MHz, the cache-ip pair harness
with the pipelined cycle injector (common-ip TASK-002), the house 512 KB
AXI4 block-RAM memory, one UART host stack.

## What is being compared

Four L1 data caches of the same geometry -- 32 KB, 4 ways, 64-byte lines,
64-bit CPU word, 64-bit AXI4 memory port, ID width 8 -- each behind the
same injector on the same part at the same clock:

| cache | source | kind | coherent |
|---|---|---|---|
| amber | `projects/components/cache-ip/amber-mesi-l1` | blocking MESI L1, one miss at a time, one-deep request skid | yes (snoop side idle in these runs) |
| jet | `projects/components/cache-ip/jet-mesi-l1` | lockup-free MESI L1, 8 MSHRs, in-order response sequencer | yes (snoop side idle in these runs) |
| HPDcache | `vendor/cv-hpdcache` (OpenHW / CEA, commit 40d2897) behind `ref_hpdcache_top` | non-blocking L1, 8 MSHR ways, 8-entry write buffer, write-back, fast loads | no |
| CVA6 WB | `vendor/cva6-dcache` (OpenHW, commit 742dc82, `std_nbdcache`) behind `ref_cva6_dcache_top` | blocking write-back L1 (the one HPDcache is measured against in CVA6S+) | no |
| jet-prime s1 | `projects/components/cache-ip/jet-prime-mesi-l1` at 3f0a7bb4d (jet forked at 2be919254, identical RTL) in the reference slot, `REF_CACHE_SEL=2` | jet with no pair fabric: straight onto memory, ACE snoop port tied off, same LRU / monitors / MSHR_COUNT 8 as the jet rig; one fill engine | yes, but nothing to be coherent with |
| jet-prime s2 | the same slot, jet-prime after TASK-001 step 2 (`jet_prime_fill`, [delta 01](../jet-prime-mesi-l1/docs/delta/01_fill_engine.md)) | as s1 with one AXI4 read ID per MSHR entry: up to 9 fills in flight on the memory port, completing in any order | yes, but nothing to be coherent with |
| jet-prime s3 | the same rig as a PAIR: two jet-primes after step 3 through the pipelined `jet_prime_pair_fabric` ([delta 02](../jet-prime-mesi-l1/docs/delta/02_pair_fabric.md)), one per injector, `REF_CACHE_SEL=3` (bin 3: the step-4 fabric with the memory-AR fixes) | the jet rig's structure with jet-prime's RTL: s2's cache behind a fabric that serializes per line, issues the memory read alongside the snoop and keeps several reads outstanding | yes -- a real peer, snooped on every miss (idle in the single-core column, active in the both-injectors numbers below) |
| jet-prime s5 | the same pair rig, jet-prime after step 5 ([delta 03](../jet-prime-mesi-l1/docs/delta/03_single_miss_path.md)), `REF_CACHE_SEL=3` (bin 4) | s3's pair with the single-miss path shortened: the fill launch goes out in the alloc cycle and the engine holds beats for the way a victim capture is reading; the commit snapshots in the done cycle, leaves the merge as its last slot advances and deposits with the install | yes -- as s3 |
| jet-prime s6 | the same pair rig, jet-prime after TASK-002 ([delta 04](../jet-prime-mesi-l1/docs/delta/04_two_cycle_hit.md)), `REF_CACHE_SEL=3` (bin 7) | s5's pair with the resident hit at HPDcache's floor: the arriving request's data address leads on the array in its capture cycle (the array reads every way; the way is selected after the tag compare) and a read hit answers from the port in its classify cycle; a write hit acks there too, its array write following from the serve record | yes |
| onyx | the same pair rig with `onyx_ccu` (N_PORTS 2) in `jet_prime_pair_fabric`'s place, `REF_CACHE_SEL=4` (onyx bin 1; [onyx HAS](../onyx-ace-ccu/docs/onyx_has/onyx_has_index.md)) | s6's two caches behind the coherency unit: broadcast snoop, tagged gather, per-line serialization, the memory read issued once every peer accepted its AC and dropped when a peer supplies the line | yes -- as s6 |
| onyx-d | the same build with `DEFER_AR=1`, `REF_CACHE_SEL=5` (onyx-d bin 1) | onyx with the memory read issued only once every CR is in and no peer supplied the line: every memory read a necessary one, every miss served from memory paying the gather first | yes -- as s6 |

Why these two: HPDcache is the closest open design to jet's point (a
lockup-free L1 with an MSHR file, published on this very board in the
CVA6S+ work), and the CVA6 write-back cache is the blocking L1 that work
measured HPDcache against, which makes it amber's peer. Neither has a snoop
side, so the comparison is single-core: injector 1 runs zero transactions
(`--ci1-idle`) on every rig, and the snoop-side results stay jet vs amber
(the J7 report).

## Method

- Stimulus: `jet_perf_sweep.py --ci1-idle --outstanding 1 2 4 8 16`
  (amber: `amber_perf_sweep.py`), 20,000 transactions per config, the same
  seeds, the same address masks and write mixes on every rig. The issued
  sequence is a function of the seed alone (TASK-002), so every cache sees
  the same addresses, strobes and data in the same order.
- Depth = requests the injector keeps in flight (CTRL[23:16]). Depth 1 is
  a blocking CPU; depth 16 is the injector's maximum.
- Cycles per transaction = RUN_CYCLES / 20,000 on injector 0. Latency =
  accept to response, from the injector's timestamp ring. MLP =
  OUTST_SUM / RUN_CYCLES (mean requests in flight at the cache).
- Area and Fmax: each cache module synthesized, placed and routed out of
  context at a 10 ns clock (`make ooc CACHE=...` in
  `projects/fpga-systems/Genesys2/cache-ip/ref/build-bringup`), so the
  injectors, bridge, UART and memory of the rigs do not blur the row.

## Where the comparison is not like-for-like

- **Wrapper stages.** HPDcache and CVA6 answer through adapters that are
  not part of the published designs: HPDcache's responses pass a one-cycle
  reorder ring (it answers out of order; the rig needs accept order), so its
  hit floor of 2 is 1 inside the cache. CVA6's wrapper presents loads on one
  port with the tag a cycle behind the index and stores on another port
  only while no load is in flight -- the serialization CVA6's own load and
  store units impose, approximated. amber's and jet's hit floors include
  their own GAXI skid.
- **Store responses.** amber and jet return data on a write response;
  HPDcache leaves it unspecified and CVA6 has no write response, so both
  wrappers return zero. The read CRC therefore differs between rigs by
  construction and is not compared.
- **Read data.** The injector's read addresses never coincide with its
  write addresses (address and write-enable derive from the same LFSR
  bits), so every read returns the memory's initial content. Data
  integrity of the reference wrappers is verified separately
  (`test_ref_cache_rw`: strobed writes over twice the cache, every word
  read back), not by the sweep.
- **Memory path.** All four share the house AXI4 memory with one read in
  flight at the pair fabric on jet/amber; HPDcache and CVA6 talk to the same
  memory directly (no fabric). Miss-side numbers include that difference.
- **Monitors.** amber, jet and jet-prime carry their MonBus observers
  (USE_MONITOR=1, the rig configuration); the references have none. The
  out-of-context rows are taken as the rigs build them, and a second area
  table gives the same three with the observers tied off (USE_MONITOR=0,
  `make ooc CACHE=<cache>_nomon`), which is the like-for-like LUT count.
- **Write policy.** HPDcache is run write-back (its WT mode off); CVA6's
  std cache is write-back by design; amber and jet are write-back MESI.
- **Coherence.** Only amber and jet pay for a snoop side (tag ports,
  response sequencing, the fabric handshake). It is idle here but it is in
  the area and in the pipeline.

## Results

<!-- generated by projects/fpga-systems/Genesys2/cache-ip/ref/bin/ref_compare.py -->
Sources (newest single-core sweep per rig; injector 1 idle):

- amber: `perf_sweep_bin11_single_20261111T225150Z.json`
- jet: `perf_sweep_bin17_single_20261111T224949Z.json`
- HPDcache: `perf_sweep_bin2_single_20261111T225823Z.json`
- CVA6 WB: `perf_sweep_cva6_bin2_single_20261111T233015Z.json`
- jet-prime s1: `perf_sweep_jetp_bin1_single_20261112T173844Z.json`
- jet-prime s2: `perf_sweep_jetp_bin2_single_20261115T200018Z.json`
- jet-prime s3: `perf_sweep_jetpp_bin3_single_20261117T144843Z.json`
- jet-prime s5: `perf_sweep_jetpp_bin4_single_20261117T191112Z.json`
- jet-prime s6: `perf_sweep_jetpp_bin7_single_20261119T132547Z.json`
- onyx: `perf_sweep_onyx_bin2_single_20261122T150901Z.json`
- onyx-d: `perf_sweep_onyxd_bin2_single_20261122T151318Z.json`

Error flags / unfinished runs across all sources: 0

### Cycles per transaction (injector 0, 20,000 transactions)

| config | depth | amber | jet | HPDcache | CVA6 WB | jet-prime s1 | jet-prime s2 | jet-prime s3 | jet-prime s5 | jet-prime s6 | onyx | onyx-d |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| r4k_we0 | 1 | 5.00 | 4.00 | 3.00 | 3.00 | 4.00 | 4.00 | 4.00 | 4.00 | 3.00 | 3.00 | 3.00 |
| r4k_we0 | 4 | 3.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 |
| r4k_we0 | 16 | 3.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 |
| r4k_we255 | 1 | 5.03 | 4.03 | 3.00 | 3.99 | 4.03 | 4.03 | 4.03 | 4.03 | 3.03 | 3.03 | 3.03 |
| r4k_we255 | 4 | 3.03 | 1.05 | 1.01 | 2.99 | 1.04 | 1.04 | 1.05 | 1.04 | 1.04 | 1.04 | 1.04 |
| r4k_we255 | 16 | 3.03 | 1.04 | 1.01 | 2.99 | 1.04 | 1.04 | 1.04 | 1.04 | 1.04 | 1.04 | 1.04 |
| smoke4k_we64 | 1 | 5.08 | 4.08 | 3.07 | 3.29 | 4.06 | 4.06 | 4.06 | 4.02 | 3.02 | 3.02 | 3.02 |
| smoke4k_we64 | 4 | 3.00 | 1.01 | 1.12 | 1.62 | 1.01 | 1.01 | 1.01 | 1.01 | 1.01 | 1.01 | 1.01 |
| smoke4k_we64 | 16 | 3.00 | 1.01 | 1.12 | 1.62 | 1.01 | 1.01 | 1.01 | 1.01 | 1.01 | 1.01 | 1.01 |
| r16k_we64 | 1 | 5.24 | 4.23 | 3.20 | 3.36 | 4.18 | 4.18 | 4.19 | 4.16 | 3.17 | 3.17 | 3.20 |
| r16k_we64 | 4 | 3.18 | 1.13 | 1.22 | 1.71 | 1.11 | 1.09 | 1.10 | 1.08 | 1.08 | 1.08 | 1.08 |
| r16k_we64 | 16 | 3.18 | 1.11 | 1.20 | 1.72 | 1.08 | 1.06 | 1.06 | 1.05 | 1.05 | 1.05 | 1.05 |
| r64k_we64 | 1 | 20.89 | 17.42 | 13.73 | 10.79 | 14.88 | 14.88 | 15.39 | 12.76 | 12.27 | 12.27 | 13.67 |
| r64k_we64 | 4 | 18.86 | 11.40 | 8.22 | 9.85 | 8.90 | 6.89 | 7.05 | 6.10 | 6.08 | 6.08 | 6.38 |
| r64k_we64 | 16 | 18.86 | 10.65 | 7.64 | 9.88 | 8.13 | 5.71 | 5.78 | 5.29 | 5.27 | 5.27 | 5.37 |
| r64k_we255 | 1 | 30.50 | 21.13 | 13.65 | 14.68 | 18.59 | 18.59 | 19.11 | 13.17 | 12.68 | 12.68 | 13.70 |
| r64k_we255 | 4 | 28.50 | 12.01 | 10.53 | 14.22 | 9.54 | 9.10 | 9.52 | 8.65 | 8.65 | 8.65 | 8.76 |
| r64k_we255 | 16 | 28.50 | 10.79 | 10.51 | 14.25 | 8.29 | 8.14 | 8.61 | 8.51 | 8.51 | 8.51 | 8.52 |
| r128k_we64 | 1 | 29.01 | 24.02 | 18.83 | 15.23 | 20.27 | 20.27 | 21.02 | 16.94 | 16.69 | 16.69 | 18.74 |
| r128k_we64 | 4 | 27.01 | 16.08 | 11.37 | 14.61 | 12.35 | 8.91 | 9.10 | 8.09 | 8.08 | 8.08 | 8.33 |
| r128k_we64 | 16 | 27.01 | 15.74 | 10.90 | 14.60 | 12.00 | 8.00 | 8.11 | 7.58 | 7.57 | 7.57 | 7.68 |

### Mean latency, accept to response (cycles)

| config | depth | amber | jet | HPDcache | CVA6 WB | jet-prime s1 | jet-prime s2 | jet-prime s3 | jet-prime s5 | jet-prime s6 | onyx | onyx-d |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| r4k_we0 | 1 | 4.00 | 3.00 | 2.00 | 2.00 | 3.00 | 3.00 | 3.00 | 3.00 | 2.00 | 2.00 | 2.00 |
| r4k_we0 | 4 | 4.00 | 3.00 | 2.00 | 2.00 | 3.00 | 3.00 | 3.00 | 3.00 | 2.00 | 2.00 | 2.00 |
| r4k_we0 | 16 | 4.00 | 3.00 | 2.00 | 2.00 | 3.00 | 3.00 | 3.00 | 3.00 | 2.00 | 2.00 | 2.00 |
| r4k_we255 | 1 | 4.03 | 3.03 | 2.00 | 1.01 | 3.03 | 3.03 | 3.03 | 3.03 | 2.03 | 2.03 | 2.03 |
| r4k_we255 | 4 | 4.03 | 3.19 | 2.00 | 1.01 | 3.17 | 3.17 | 3.18 | 3.17 | 3.16 | 3.16 | 3.16 |
| r4k_we255 | 16 | 4.03 | 4.38 | 2.00 | 1.01 | 4.35 | 4.35 | 4.37 | 4.35 | 3.77 | 3.77 | 3.77 |
| smoke4k_we64 | 1 | 4.08 | 3.08 | 2.06 | 1.78 | 3.06 | 3.06 | 3.06 | 3.02 | 2.02 | 2.02 | 2.02 |
| smoke4k_we64 | 4 | 4.00 | 3.03 | 2.00 | 1.75 | 3.03 | 3.03 | 3.03 | 3.03 | 3.02 | 3.02 | 3.02 |
| smoke4k_we64 | 16 | 4.00 | 4.01 | 2.00 | 1.75 | 4.01 | 4.01 | 4.01 | 4.01 | 4.00 | 4.00 | 4.00 |
| r16k_we64 | 1 | 4.24 | 3.23 | 2.18 | 1.85 | 3.18 | 3.18 | 3.19 | 3.16 | 2.17 | 2.17 | 2.20 |
| r16k_we64 | 4 | 4.18 | 3.54 | 2.25 | 1.82 | 3.42 | 3.37 | 3.38 | 3.30 | 3.30 | 3.30 | 3.34 |
| r16k_we64 | 16 | 4.18 | 6.17 | 2.44 | 1.82 | 5.89 | 5.81 | 5.83 | 5.65 | 5.65 | 5.65 | 5.71 |
| r64k_we64 | 1 | 19.89 | 16.42 | 11.41 | 6.99 | 13.88 | 13.88 | 14.39 | 11.76 | 11.27 | 11.27 | 12.67 |
| r64k_we64 | 4 | 19.86 | 44.61 | 18.11 | 7.51 | 34.60 | 26.54 | 27.18 | 23.38 | 23.33 | 23.33 | 24.50 |
| r64k_we64 | 16 | 19.86 | 75.16 | 22.49 | 7.55 | 57.89 | 61.65 | 62.42 | 56.04 | 55.91 | 55.91 | 57.52 |
| r64k_we255 | 1 | 29.50 | 20.13 | 11.34 | 1.10 | 17.59 | 17.59 | 18.11 | 12.17 | 11.68 | 11.68 | 12.70 |
| r64k_we255 | 4 | 29.50 | 47.04 | 16.69 | 1.09 | 37.16 | 35.40 | 37.06 | 33.57 | 33.57 | 33.57 | 34.01 |
| r64k_we255 | 16 | 29.50 | 75.39 | 17.52 | 1.10 | 58.11 | 52.30 | 54.71 | 44.95 | 45.25 | 45.25 | 46.69 |
| r128k_we64 | 1 | 28.01 | 23.02 | 15.89 | 10.02 | 19.27 | 19.27 | 20.02 | 15.94 | 15.69 | 15.69 | 17.74 |
| r128k_we64 | 4 | 28.01 | 63.33 | 23.29 | 10.89 | 48.41 | 34.65 | 35.40 | 31.35 | 31.30 | 31.30 | 32.30 |
| r128k_we64 | 16 | 28.01 | 91.97 | 26.74 | 10.91 | 70.76 | 86.06 | 87.01 | 80.04 | 79.97 | 79.97 | 81.36 |

### Resident-hit floor and achieved parallelism

| rig | hit floor (lat_min, r4k_we0 d1) | MLP r64k_we64 d16 | OUTST_MAX r64k_we64 d16 |
|---|---|---|---|
| amber | 4 | 1.05 | 2 |
| jet | 3 | 7.06 | 12 |
| HPDcache | 2 | 2.94 | 12 |
| CVA6 WB | 2 | 0.76 | 2 |
| jet-prime s1 | 3 | 7.12 | 12 |
| jet-prime s2 | 3 | 10.79 | 12 |
| jet-prime s3 | 3 | 10.81 | 12 |
| jet-prime s5 | 3 | 10.59 | 12 |
| jet-prime s6 | 2 | 10.60 | 12 |
| onyx | 2 | 10.60 | 12 |
| onyx-d | 2 | 10.72 | 12 |

### Cache alone, out of context (xc7k325t-2, 10 ns clock, synth + place + route)

| cache | LUT | FF | RAMB36 | RAMB18 | LUTRAM | WNS at 10 ns | worst path levels |
|---|---|---|---|---|---|---|---|
| amber | 3709 | 2944 | 16 | 0 | 1169 | +0.123 | 19 |
| jet | 5697 | 4834 | 16 | 0 | 2023 | +0.245 | 17 |
| HPDcache | 3510 | 4944 | 8 | 4 | 0 | +1.372 | 10 |
| CVA6 WB | 5669 | 1661 | 32 | 20 | 0 | +0.990 | 14 |
| jet-prime s1 | 5892 | 5258 | 16 | 0 | 1879 | +0.356 | 16 |
| jet-prime s2 | 6047 | 5394 | 16 | 0 | 1888 | +0.118 | 16 |
| jet-prime s3 | 6047 | 5394 | 16 | 0 | 1888 | +0.118 | 16 |
| jet-prime s5 | 6010 | 5399 | 16 | 0 | 1998 | +0.321 | 19 |
| jet-prime s6 | 5926 | 4977 | 16 | 0 | 2142 | +0.159 | 25 |
| onyx | 5926 | 4977 | 16 | 0 | 2142 | +0.159 | 25 |
| onyx-d | 5926 | 4977 | 16 | 0 | 2142 | +0.159 | 25 |

### The same, monitors off (USE_MONITOR=0; HPDcache and CVA6 have none to turn off)

| cache | LUT | FF | RAMB36 | RAMB18 | LUTRAM | WNS at 10 ns | worst path levels | LUT with monitors |
|---|---|---|---|---|---|---|---|---|
| amber | 2370 | 1706 | 16 | 0 | 980 | +0.859 | 22 | 3709 |
| jet | 3711 | 2886 | 16 | 0 | 1468 | +0.326 | 16 | 5697 |
| jet-prime s6 | 3908 | 3031 | 16 | 0 | 1587 | +0.157 | 21 | 5926 |

### The managers alone, out of context (xc7k325t-2, 10 ns clock; 18 slots, SNOOP_INFLIGHT 2)

| manager | LUT | FF | LUTRAM | WNS at 10 ns | worst path levels |
|---|---|---|---|---|---|
| jet_prime_pair_fabric | 4300 | 1660 | 1296 | +2.757 | 10 |
| onyx_ccu (N_PORTS 2) | 4628 | 1664 | 1296 | +2.885 | 9 |
### onyx counters, both injectors (the D6 trade: reads issued, lines supplied, reads wasted)

- onyx: `perf_sweep_onyx_bin2_dual_20261122T151054Z.json`
- onyx-d: `perf_sweep_onyxd_bin2_dual_20261122T151512Z.json`

| config | depth | mode | transactions | memory reads | lines supplied | reads wasted | wasted / issued | absorptions | write-backs |
|---|---|---|---|---|---|---|---|---|---|
| r4k_we0 | 1 | onyx | 16 | 16 | 16 | 16 | 1.000 | 16 | 16 |
| r4k_we0 | 1 | onyx-d | 16 | 0 | 16 | 0 | 0.000 | 16 | 16 |
| r4k_we0 | 4 | onyx | 16 | 16 | 16 | 16 | 1.000 | 16 | 16 |
| r4k_we0 | 4 | onyx-d | 16 | 0 | 16 | 0 | 0.000 | 16 | 16 |
| r4k_we0 | 16 | onyx | 16 | 16 | 16 | 16 | 1.000 | 16 | 16 |
| r4k_we0 | 16 | onyx-d | 16 | 0 | 16 | 0 | 0.000 | 16 | 16 |
| r4k_we255 | 1 | onyx | 128 | 64 | 64 | 64 | 1.000 | 64 | 0 |
| r4k_we255 | 1 | onyx-d | 128 | 0 | 64 | 0 | 0.000 | 64 | 0 |
| r4k_we255 | 4 | onyx | 128 | 64 | 64 | 64 | 1.000 | 64 | 16 |
| r4k_we255 | 4 | onyx-d | 128 | 0 | 64 | 0 | 0.000 | 64 | 16 |
| r4k_we255 | 16 | onyx | 128 | 64 | 64 | 64 | 1.000 | 64 | 16 |
| r4k_we255 | 16 | onyx-d | 128 | 0 | 64 | 0 | 0.000 | 64 | 16 |
| smoke4k_we64 | 1 | onyx | 64 | 64 | 16 | 16 | 0.250 | 16 | 0 |
| smoke4k_we64 | 1 | onyx-d | 64 | 48 | 16 | 0 | 0.000 | 16 | 0 |
| smoke4k_we64 | 4 | onyx | 32 | 32 | 32 | 32 | 1.000 | 32 | 32 |
| smoke4k_we64 | 4 | onyx-d | 32 | 0 | 32 | 0 | 0.000 | 32 | 32 |
| smoke4k_we64 | 16 | onyx | 32 | 32 | 32 | 32 | 1.000 | 32 | 32 |
| smoke4k_we64 | 16 | onyx-d | 32 | 0 | 32 | 0 | 0.000 | 32 | 32 |
| r16k_we64 | 1 | onyx | 381 | 381 | 116 | 116 | 0.304 | 116 | 46 |
| r16k_we64 | 1 | onyx-d | 381 | 265 | 116 | 0 | 0.000 | 116 | 46 |
| r16k_we64 | 4 | onyx | 383 | 383 | 116 | 116 | 0.303 | 116 | 77 |
| r16k_we64 | 4 | onyx-d | 383 | 267 | 116 | 0 | 0.000 | 116 | 77 |
| r16k_we64 | 16 | onyx | 383 | 383 | 116 | 116 | 0.303 | 116 | 77 |
| r16k_we64 | 16 | onyx-d | 383 | 267 | 116 | 0 | 0.000 | 116 | 77 |
| r64k_we64 | 1 | onyx | 20240 | 20240 | 192 | 192 | 0.009 | 192 | 4778 |
| r64k_we64 | 1 | onyx-d | 20240 | 20048 | 192 | 0 | 0.000 | 192 | 4778 |
| r64k_we64 | 4 | onyx | 20240 | 20240 | 192 | 192 | 0.009 | 192 | 4810 |
| r64k_we64 | 4 | onyx-d | 20240 | 20048 | 192 | 0 | 0.000 | 192 | 4810 |
| r64k_we64 | 16 | onyx | 20240 | 20239 | 192 | 191 | 0.009 | 192 | 4810 |
| r64k_we64 | 16 | onyx-d | 20240 | 20048 | 192 | 0 | 0.000 | 192 | 4810 |
| r64k_we255 | 1 | onyx | 20490 | 20303 | 637 | 637 | 0.031 | 637 | 19367 |
| r64k_we255 | 1 | onyx-d | 20490 | 19666 | 637 | 0 | 0.000 | 637 | 19367 |
| r64k_we255 | 4 | onyx | 20490 | 20303 | 637 | 637 | 0.031 | 637 | 19367 |
| r64k_we255 | 4 | onyx-d | 20490 | 19666 | 637 | 0 | 0.000 | 637 | 19367 |
| r64k_we255 | 16 | onyx | 20490 | 20303 | 637 | 637 | 0.031 | 637 | 19367 |
| r64k_we255 | 16 | onyx-d | 20490 | 19666 | 637 | 0 | 0.000 | 637 | 19367 |
| r128k_we64 | 1 | onyx | 30083 | 30083 | 638 | 638 | 0.021 | 638 | 7258 |
| r128k_we64 | 1 | onyx-d | 30083 | 29445 | 638 | 0 | 0.000 | 638 | 7258 |
| r128k_we64 | 4 | onyx | 30083 | 30083 | 638 | 638 | 0.021 | 638 | 7258 |
| r128k_we64 | 4 | onyx-d | 30083 | 29445 | 638 | 0 | 0.000 | 638 | 7258 |
| r128k_we64 | 16 | onyx | 30083 | 30072 | 638 | 627 | 0.021 | 638 | 7258 |
| r128k_we64 | 16 | onyx-d | 30083 | 29445 | 638 | 0 | 0.000 | 638 | 7258 |

<!-- end generated -->

## Reading

**Compare cycles per transaction across rigs; compare latency only within a
rig.** The injector counts latency from the cycle it hands a request over to
the cycle the response comes back. amber, jet and HPDcache take a request
into a skid or ring the moment they are ready and queue it inside, so their
latency includes that queueing; the CVA6 wrapper's acceptance IS the cache's
grant, which for a store is its completion and for a load its array access,
so CVA6's latency column is almost pure service time (1.1 cycles on the
write-heavy thrash) and the waiting shows up in `STALL_CYCLES` and in cycles
per transaction instead. Cycles per transaction is the one number every rig
measures the same way.

- **Hit path.** All four stream resident hits once the injector keeps enough
  in flight: one hit per cycle for jet, HPDcache and the CVA6 cache from depth
  4 on a read-only working set (`r4k_we0`: 1.00 cycles per transaction each).
  amber settles at 3.0: its one-deep skid admits a second request and then
  blocks. The resident-hit floor at the injector is 4 cycles for amber, 3 for
  jet, 2 for both references (1 inside HPDcache plus the ring stage; the CVA6
  load hit is index then tag, two cycles, with the grant on the first).
  Mixed hits (25 % stores, `smoke4k_we64`, depth 4) separate them: jet 1.01,
  HPDcache 1.12, CVA6 1.62 -- the CVA6 cache's store is a second array pass
  on a single-ported SRAM and the wrapper drains the load pipe before each
  one, so every store costs it two to three cycles.
- **Miss path, read-lean (`r64k_we64`, 25 % stores).** At depth 1 the order
  is CVA6 10.8, HPDcache 13.7, jet 17.4, amber 20.9 cycles per transaction.
  At depth 16: HPDcache 7.6 (MLP 2.9), CVA6 9.9 (blocking: MLP 0.8, two in
  flight at most), jet 10.7 (MLP 7.1, twelve in flight), amber 18.9. HPDcache
  gains 45 % from depth, jet 39 %, the CVA6 cache 8 %, amber 10 %. jet keeps
  the most in flight yet lands behind both references: its fills go through
  the pair fabric's grant, snoop and reply cycle even with the peer idle
  (the references write to memory directly), and its mean latency at depth
  16 is 75 cycles against HPDcache's 22 -- queue depth it pays for with
  latency where HPDcache holds `ready` low. The fabric cost is the rig's,
  not the cache's; measuring jet without the fabric is the next experiment.
- **Miss path, write-heavy (`r64k_we255`, all stores, depth 16).** HPDcache
  10.5, jet 10.8, CVA6 14.3, amber 28.5. Write-back traffic separates the
  blocking caches from the non-blocking ones by a factor of two to three;
  the two non-blocking ones are within 3 % of each other here.
- **128 KB (four times the cache), depth 16:** HPDcache 10.9, CVA6 14.6,
  jet 15.7, amber 27.0.
- **jet without the fabric (jet-prime direct, 2026-11-12).** Same RTL as
  jet, same injector, same memory, no `jet_pair_fabric` between them. At
  depth 16: `r64k_we64` 8.13 (jet 10.65, HPDcache 7.64), `r64k_we255` 8.29
  (jet 10.79, HPDcache 10.51), `r128k_we64` 12.00 (jet 15.74, HPDcache
  10.90); at depth 1 the single miss costs 13.9 mean cycles against jet's
  16.4 and HPDcache's 11.4. Read it two ways. The fabric costs a single
  core 2.5 cycles per transaction at every depth on the 64 KB thrash --
  about 5 cycles per miss, a quarter of jet's miss cost -- and on the
  write-heavy thrash it is the whole gap: without it jet is 21 % under
  HPDcache (the fabric's one-write-burst-at-a-time port is what held jet
  to a tie). What remains against HPDcache on the read-lean thrash is 6 %
  (8.13 vs 7.64), and it is the cache's own: MLP 7.1 with a mean latency
  of 58 cycles says seven misses still queue behind one fill engine that
  retires them at about 15 cycles each (eight beats plus overhead), where
  HPDcache retires at 14 with three in flight. Hit floor (3) and hit rows
  (1.00 from depth 4) are unchanged, as they must be for identical RTL.
  The step-2 target is now quantified: concurrent fills, not the fabric,
  take jet-prime under HPDcache on reads; the fabric work (step 3) is what
  keeps it there with a peer attached.
- **jet-prime with concurrent fills (s2, 2026-11-15).** The same slot and
  rig as s1; the only RTL change is the fill path (`jet_prime_fill`, one
  read ID per MSHR entry, the done queue in `jet_prime_control`). At depth
  16: `r64k_we64` 5.71 (s1 8.13, HPDcache 7.64), `r64k_we255` 8.14 (s1
  8.29, HPDcache 10.51), `r128k_we64` 8.00 (s1 12.00, HPDcache 10.90); at
  depth 4: 6.89 / 9.10 / 8.91 against HPDcache's 8.22 / 10.53 / 11.37.
  Depth 1 is unchanged (14.88 per miss-heavy transaction, HPDcache 13.73):
  one miss at a time is the same path it always was, and the single-miss
  latency gap to HPDcache (about one cycle, the AR register plus the
  lookup pipeline) is still there. From depth 4 up jet-prime is under
  HPDcache on every miss configuration: 25 % on the read-lean thrash, 23 %
  on the write-heavy one, 27 % at four times the cache. The mechanism is
  the one the s1 column predicted: MLP on `r64k_we64` at depth 16 went from
  7.1 to 10.8 with the same 12-outstanding ceiling (the injector's), and
  the mean miss latency fell at depth 4 (34.6 to 26.5) while rising at
  depth 16 (57.9 to 61.7) because the deeper queue now fills faster than
  it drains -- the memory port, not the cache, is the limit there: 5.71
  cycles per transaction at a 50 % miss rate is 11.4 cycles per line
  fetch against the 8-beat floor. The write-heavy row moved least (8.29
  to 8.14); the likely limiter, not measured here, is the dirty-victim
  path (one victim capture at a time, with the launch held behind it) and
  the single write channel rather than the fill engine. Hit floor (3) and hit rows (1.00 from
  depth 4) are unchanged. Area, cache alone at 10 ns: 6,047 LUT / 5,394 FF
  (jet 5,892 / 5,258: +155 LUT, +136 FF for the slot records, the wider
  staging queue and the done queue), the same 16 RAMB36 and 1,888 LUTRAM,
  WNS +0.118 ns with the worst path from the staging queue's read pointer
  through the slot's set lookup into the data array's address -- the
  tightest of the five OOC rows and a watch item (the full bitstream
  closes at +0.532 ns).
- **jet-prime as a pair (s3, 2026-11-16).** The s2 cache, twice, through
  the pipelined fabric -- the jet rig's structure -- with injector 1 idle
  as in every other column. At depth 16: `r64k_we64` 5.78 (s2 5.71, jet
  10.65, HPDcache 7.64), `r64k_we255` 8.61 (s2 8.14, jet 10.79, HPDcache
  10.51), `r128k_we64` 8.12 (s2 8.00, jet 15.74, HPDcache 10.90); at depth
  4: 7.05 / 9.52 / 9.10 against HPDcache's 8.22 / 10.53 / 11.37; at depth
  1: 15.39 / 19.11 / 21.02 (s2 14.88 / 18.59 / 20.27). So the fabric that
  cost jet 2.5 cycles per transaction on `r64k_we64` costs jet-prime 0.07
  at depth 16 and half a cycle at depth 1 -- the grant and the AR take,
  the two registered stages a miss crosses before its memory read; the
  snoop round trip to the idle peer runs alongside the read and shows
  only in the write-heavy row (0.47 at depth 16: more lines, each snooped,
  the write-back AW waiting out its line's verdict). With a peer attached
  jet-prime is under HPDcache on every miss configuration from depth 4
  (24 % on the read-lean thrash, 18 % on the write-heavy one, 25 % at four
  times the cache) and at depth 1 it is 1.7 cycles over, as the s2 cache
  is. With BOTH injectors active on the same 4 KB region (the pair's own
  numbers, not in the table: `perf_sweep_jetpp_bin3_dual_*.json` against
  jet's `perf_sweep_bin17_2026*.json`), `r64k_we64` at depth 16 is
  5.81 / 5.82 cycles per transaction on the two injectors against jet's
  10.74 / 10.70, depth 4 7.08 / 7.11 against 11.48 / 11.46, `r64k_we255`
  8.66 / 8.65 against 10.90 / 11.01, `r128k_we64` 8.10 / 8.09 against
  16.02 / 15.82 -- the same figures as with the peer idle, so the fabric
  is no longer what a second core costs. Hit floor (3), the 1.00 hit rows
  and MLP 10.8 unchanged; smoke CRC on injector 0 is the jet rig's
  (1814064162). The cache-only OOC row is s2's (same cache). Full
  bitstream (bin 3, the step-4 fabric with the memory-AR hold) 17,932 LUT
  / 11,889 FF at WNS +0.043 ns under the 0.2 ns uncertainty budget; the
  worst path is the s2 watch item (the fill engine's staging-queue read
  pointer into the data-array address, 24 levels), the long pole of the
  pair build -- bin 2 (the step-3 fabric) placed the same path at +0.326,
  so the spread is placement, and the budget is what holds it. Bin 3
  against bin 2: every CRC of both sweeps equal, every cycle count equal
  at depths 1, 2 and 4, and at depths 8 and 16 within 0.14 % (fewer cycles
  on bin 3: the held AR issues where the step-3 fabric re-picked) -- the
  footprint of the defect the fabric formal found, which needs the
  memory's two-deep burst queue to stall the AR. Bin 1, the first build
  with the two-write-port buffer array (48,946 LUT, WNS +0.006), swept
  bit-identically to bin 2. Fabric alone, out of context at 10 ns with `FAB_SLOTS=18` (`ref/results/ooc/jetp_fabric`): 4,923 LUT (3,891 logic, 1,032 as the
  two line-buffer memories) / 1,660 FF, WNS +2.76 ns, ten levels on the worst path (the grant
  cone: queue count, candidate, line CAM, slot load); the step-3 fabric was 4,886 / 1,655 at +2.30,
  so the AR hold and the release term cost 37 LUT and 5 flops. The first build's single buffer array
  had two write ports and synthesized as 9 k flops behind 272:1 muxes -- 35,879 LUT -- caught
  by the bitstream's LUT count; one array per peer is the fix.
- **jet-prime at every depth (s5, 2026-11-17).** The s3 pair with the
  single-miss path rebuilt: a depth-1 trace of the pair rig had put a
  clean miss at 23 cycles and a dirty-victim miss at 33 (the fill launch
  waited behind the whole victim capture; the tail from the last beat to
  the response was six cycles, three of them the commit's own). The launch
  now goes out in the alloc cycle (the engine holds beats for the way a
  capture is reading -- the contract at the hazard, not the launch) and
  the commit tail is three cycles. On the board every depth-1 miss now
  sits in the [16, 32) bucket with a maximum of 26 (bin 3: a quarter of
  the read-lean misses and 96 % of the write-heavy ones in [32, 64)), mean
  miss latency 20.2 cycles against HPDcache's 20.5. Cycles per transaction
  (s3 -> s5, HPDcache): `r64k_we64` depth 1 15.39 -> 12.76 (13.73), depth
  2 9.55 -> 7.91 (9.79), depth 4 7.05 -> 6.10 (8.22), depth 16 5.78 -> 5.29
  (7.64); `r64k_we255` depth 1 19.11 -> 13.17 (13.65), depth 2 11.79 ->
  9.31 (11.04), depth 16 8.61 -> 8.51 (10.51); `r128k_we64` depth 1 21.02
  -> 16.94 (18.83), depth 16 8.11 -> 7.58 (10.90). jet-prime is under
  HPDcache at every depth 1, 2, 4, 8 and 16 on both thrash
  configurations and at four times the cache -- TASK-001's done
  criterion; the margin at depth 1 on the write-heavy row is 3.5 %, on
  the read-lean row 7 %. The resident rows keep jet's 3-cycle hit (HPDcache
  2), so at depths 1 and 2 `r4k_*` / `r16k_we64` / `smoke4k_we64` stay a
  cycle per transaction over HPDcache as before; from depth 4 they are
  1.0x. Hit floor 3, the 1.00 hit rows, MLP 10.6 at depth 16 (OUTST_MAX
  12). Both injectors active on the same region (`perf_sweep_jetpp_bin4_dual_*.json`):
  `r64k_we64` depth 1 12.78 / 12.74, depth 16 5.32 / 5.34; `r64k_we255`
  depth 1 13.25 / 13.32; `r128k_we64` depth 1 17.20 / 16.98 -- the
  single-core numbers, as with s3. Every CRC of the 55 single-core runs
  equals bin 3's (the data path is untouched; only the timing moved).
  Smoke CRC on injector 0 is the jet rig's (1814064162). Full bitstream
  (bin 4) 18,126 LUT / 11,890 FF, WNS +0.019 ns under the 0.2 ns
  uncertainty budget; the worst path is still the fill engine's
  staging-queue read pointer into the data-array write address (bin 3:
  +0.043 on the same path; the spread is placement, the budget holds it).
  Cache alone out of context at 10 ns (`ref/results/ooc/jetp5`): 6,010
  LUT / 5,399 FF, 16 RAMB36, 1,998 LUTRAM, WNS +0.321 ns, 19 levels on the
  same staging-queue-to-array path (s2's cache: 6,047 / 5,394 at +0.118) --
  the beat hold and the shorter commit cost no area.
- **jet-prime's resident hit (s6, 2026-11-19).** The s5 pair with the hit
  path shortened by a cycle: the data array reads every way per address
  and selects the way on its output side, so the arriving request's
  `{set, beat}` is presented in its capture cycle and a read hit answers
  from the port in its classify cycle; a write hit's response (the store
  echoed) leaves in the classify cycle as well, with the array write and
  the E-to-M promotion still done from the serve record under the same
  same-line and snoop-safe holds. The capture/classify split of jet v3
  (the 100 MHz closure) is untouched. Hit floor 3 -> 2, HPDcache's.
  Cycles per transaction at depth 1 (s5 -> s6, HPDcache): `r4k_we0` 4.00
  -> 3.00 (3.00), `r4k_we255` 4.03 -> 3.03 (3.00), `smoke4k_we64` 4.02 ->
  3.02 (3.07), `r16k_we64` 4.16 -> 3.17 (3.20); at depth 2 `r4k_we0` 2.00
  -> 1.50 (1.50), `r4k_we255` 2.03 -> 1.54 (1.50), `smoke4k_we64` 2.00 ->
  1.58 (1.53), `r16k_we64` 2.08 -> 1.66 (1.64): the resident rows are at
  HPDcache's numbers at depth 1 and within 0.05 cycles at depth 2 (the
  residual is a write whose accept cycle finds the completion port
  taken). The thrashes at depth 1: `r64k_we64` 12.76 -> 12.27 (13.73,
  10.7 % under), `r64k_we255` 13.17 -> 12.68 (13.65, 7.1 %), `r128k_we64`
  16.94 -> 16.69 (18.83, 11.3 %); from depth 4 every row is s5's within
  0.02. Two intermediate bins taught the shape of the change: bin 5a
  (the read side, with the arriving request's lead pre-empting an
  occupant that could not serve directly) kept the floor at 2 and the
  pure-read row at 3.00 but lost 40 % of the throughput of the mixed
  resident rows at depth 4 and 16 (`smoke4k_we64` 1.01 -> 1.76), fixed by
  letting the lead yield whenever the occupant may need the record path;
  bin 6 (read side only) left the write-containing rows a cycle over at
  depth 1. Both sweeps are kept in `ref/results` as the measurements that
  found those, not as columns. Board: `ref_jetpp_bringup` bin 7 18,241
  LUT / 11,896 FF, WNS +0.040 ns under the 0.2 ns uncertainty budget,
  the same worst path as bins 3-4 (the fill engine's staging read pointer
  into the data BRAM address); smoke PASS, both 55-run sweeps err 0, all
  55 single-core CRCs equal to bin 4's; dual-active `r64k_we64` depth 1
  12.28 / 12.25, depth 16 5.30 / 5.32. Cache alone out of context at
  10 ns (`ref/results/ooc/jetp6`): 6,033 LUT / 5,402 FF, WNS +0.082 (s5
  6,010 / 5,399 at +0.321, the same path).
- **onyx in the fabric's place (2026-11-21).** The s6 pair with `onyx_ccu`
  (N_PORTS 2, 18 slots, SNOOP_INFLIGHT 2) replacing `jet_prime_pair_fabric`,
  same caches, memory, injectors and knobs. With the memory read alongside
  the snoop (`REF_CACHE_SEL=4`, the fabric's own timing rule) every one of
  the 55 single-injector cells and the 55 dual cells, both injectors,
  reproduces bin 7's cycle count exactly -- not within noise, identical --
  and every CRC equals bin 7's: onyx at two ports is the fabric's behavior.
  Hit floor 2, MLP 10.60 on `r64k_we64` at depth 16, as s6. With the read
  deferred until the gather (`REF_CACHE_SEL=5`) the resident rows are
  unchanged (every hit-only cell equal; `r16k_we64` +0.4 to +0.9 % from its
  few misses) and the thrash rows pay the gather on the critical path:
  depth 1 `r64k_we64` 12.27 -> 13.67 (+11.4 %), `r64k_we255` 12.68 -> 13.70
  (+8.1 %), `r128k_we64` 16.69 -> 18.74 (+12.2 %); the cost shrinks with
  depth to +1.8 / +0.2 / +1.5 % at 16, where the gather overlaps other
  misses. CRCs equal bin 7's there too. The saving the deferred mode buys
  is memory reads not issued, and the bin 2 builds count it (onyx's exact
  counters through the harness CSR, the last table): with the read
  alongside the snoop every line a peer supplies is a read the memory
  answered for nothing -- reads wasted equals lines supplied in every cell
  but the deepest, 116 of 381 reads (30 %) on the shared resident set
  `r16k_we64`, 192 of 20,240 (0.9 %) on `r64k_we64`, 637 of 20,303 (3.1 %)
  on `r64k_we255`, 638 of 30,083 (2.1 %) on `r128k_we64`; with the read
  deferred, reads wasted is 0 in all 110 cells and memory reads fall by
  exactly lines supplied (381 -> 265, 20,240 -> 20,048, 20,490 -> 19,666,
  30,083 -> 29,445). The single-injector cells are the control (no peer
  holds anything: supplied 0, wasted 0, reads equal in both modes). The
  trade, then: the deferred mode elides every wasted read -- the sharing
  rate of the workload, 1 to 30 % of the memory reads here -- for +8 to
  +12 % per transaction at depth 1 in thrash and under 2 % at depth 16.
  The bin 2 builds reproduce bin 1's cycle count in all 220 cells (the
  observation costs no cycle) and add the chain the jet rig carries:
  27,872 / 27,143 LUT, 25,877 / 25,854 FF, WNS +0.001 / +0.027 ns. The
  MonBus tally bins for onyx's classes are lower bounds on the board when
  every class is open (the house MonBus is a low-bandwidth event channel
  by design, and four of onyx's classes fire once a transaction, so the
  channel saturates in thrash); the counters are the measurement. The
  observer carries the ocelus mask layers (`ONYX_MON_CTRL` 0x038, reset
  to LOCK_WAIT only; `jet_perf_sweep.py --onyx-mon-classes`), and the
  bin 3 build (27,668 LUT, 25,090 FF, WNS -0.001 ns, the same path)
  measures them: `MEM_READ` opened alone equals its counter in 39 of 55
  dual cells and in every cell at depth 1 and 2 (`r64k_we64` depth 1:
  20,240 = 20,240 where the all-open bin read 12,603), short only in the
  thrash cells at depth 4 to 16 where the caches' two unmasked observers
  still share the channel, each with a drop report; the deferred build
  reads the same way, 45 of 55 (onyx ISSUE-001, closed). The content
  filter (bin 4: an address window, `--onyx-mon-window LOW HIGH`; 27,328 /
  27,237 LUT, WNS +0.003 / +0.013 ns) is what makes the class
  low-bandwidth at any depth: `MEM_READ` through a window on the first
  8 KB reads exactly in the 30 cells whose region lies inside it, the
  window's share in the thrash cells (0.123 of `r64k_we64`'s reads against
  a 0.125 share), and not one of the 110 windowed cells drops a packet. Timing at 100 MHz under the 0.2 ns budget: SEL 4 WNS
  +0.006 ns, SEL 5 +0.000 ns, both met, the worst path jet-prime's fill
  engine staging read pointer into the data-array address in both -- onyx
  is not on the critical path. Manager alone out of context (the fourth
  table): onyx 4,628 LUT / 1,664 FF / 1,296 LUTRAM at +2.885 ns against
  the fabric's 4,300 / 1,660 / 1,296 at +2.757, the generalization to N
  ports 328 LUT (7.6 %) and nothing else.
- **Area, cache alone at 10 ns.** HPDcache is the smallest in LUTs (3,510)
  and the fastest (WNS +1.37 ns, ten logic levels on its worst path) and
  keeps its arrays in 8 RAMB36 + 4 RAMB18. jet is 5,892 LUT / 5,258 FF /
  16 RAMB36 plus 1,879 LUTRAM (tags, LRU, MSHR file, the response ring, and
  its MonBus observers) at +0.36 ns; amber 3,709 LUT / 2,944 FF / 16 RAMB36
  plus 1,169 LUTRAM at +0.12 ns. The CVA6 cache is 5,669 LUT but 32 RAMB36 +
  20 RAMB18: its `sram` wrapper cuts every 512-bit line into eight 64-bit
  block RAMs per way at 128 words deep, so each RAMB36 holds 8 Kb of its 36.
  That is the published structure at this geometry on this part, not a
  wrapper artifact; amber's and jet's arrays are organized for the part
  (common-ip TASK-001). The two coherent caches carry a snoop side and
  observers the references do not.
- **Area with the observers off** (the second area table, 2026-11-19). The
  MonBus observers and their arbiter are about a third of every house
  cache's LUTs (35-37 %) and close to half of jet's and jet-prime's flops: jet-prime 6,033 -> 3,908 LUT and 5,402 -> 3,031 FF with
  USE_MONITOR=0, jet 5,892 -> 3,711 / 5,258 -> 2,886, amber 3,709 -> 2,370 /
  2,944 -> 1,706; the block RAM count does not move, and the observer
  queues were 411 LUTRAM on jet and jet-prime, 189 on amber. Read like-for-like against HPDcache's
  3,510 LUT / 4,944 FF: jet-prime is 11 % more LUTs and 39 % fewer flops,
  jet 6 % more LUTs, amber a third fewer. The fork's own cost, jet to
  jet-prime with the observers off, is 197 LUT / 145 FF / 119 LUTRAM for
  multiple fills, the held beats and the 2-cycle hit. Timing with the
  observers off: jet-prime +0.157 ns on the same worst path (the fill
  engine's staging read pointer into the data-array address, 21 levels),
  jet +0.326, amber +0.859 -- the observers' output queue was amber's worst
  path with them on. The remaining LUTRAM (jet-prime 1,587) is the tag
  array, LRU, MSHR file and response ring as distributed memory, which is
  the structural difference from HPDcache's block-RAM tags and MSHR.

What this says about jet and amber: against the non-blocking reference,
jet's hit path is equal and its miss path is 30-40 % behind at depth 16;
the jet-prime s1 column splits that into the fabric's 2.5 cycles per
transaction (measured, not suspected) and the cache's own 0.5 on reads,
and shows the fabric alone holding jet to a tie on writes; the s2 column
shows that with concurrent fills the cache alone is 23-27 % under
HPDcache from depth 4 on every miss configuration; the s3 column puts the
pipelined fabric back and keeps 18-25 % of it, with both cores active or
one; the s5 column takes the single miss itself from 23-33 cycles to
20 and puts jet-prime on the pair rig under HPDcache at every depth on
every miss configuration (depth 1: 7 % on the read-lean thrash, 3.5 % on
the write-heavy one, 10 % at four times the cache); the s6 column takes
the resident hit to HPDcache's 2-cycle floor, which puts the resident
rows at HPDcache's numbers at depths 1 and 2 and widens the depth-1
thrash margins to 10.7 %, 7.1 % and 11.3 %. Nothing in the table is now
over HPDcache by more than 0.05 cycles per transaction. Against the
blocking reference, amber is 1.7x slower on hits (its skid-then-block port)
and 2x on misses (CVA6's miss handler overlaps the write-back with the
refill; amber drains then fills). Both gaps have a named mechanism to go
after; jet's is jet-prime TASK-001.

## Reproduction

```bash
# board sweeps, one rig at a time (board_lock.sh); --ci1-idle = single core
cd projects/fpga-systems/Genesys2/cache-ip/ref/build-bringup
make bitstream smoke REF_CACHE_SEL=0            # HPDcache rig
make bitstream smoke REF_CACHE_SEL=1            # CVA6 write-back rig
make bitstream smoke REF_CACHE_SEL=2            # jet-prime, no fabric (s2 at HEAD; s1 at 3f0a7bb4d)
make bitstream REF_CACHE_SEL=3 ; make program REF_CACHE_SEL=3 ; make run SEQUENCES="init smoke" REF_CACHE_SEL=3   # the jet-prime pair through the pipelined fabric (s6 at HEAD; s5 at 4db2f29e5; s3 at 7fb330377)
python3 ../../jet/host/jet_perf_sweep.py --board genesys2 --ci1-idle --outstanding 1 2 4 8 16 --out ../results/<name>.json
make ooc CACHE=hpd ; make ooc CACHE=cva6 ; make ooc CACHE=jet ; make ooc CACHE=jetp ; make ooc CACHE=jetp5 ; make ooc CACHE=jetp6 ; make ooc CACHE=amber
make ooc CACHE=jet_nomon ; make ooc CACHE=jetp6_nomon ; make ooc CACHE=amber_nomon   # the same with the observers off
make bitstream REF_CACHE_SEL=4 ; make program REF_CACHE_SEL=4 ; make run SEQUENCES="init smoke" REF_CACHE_SEL=4   # onyx in the fabric's place (SEL 5: DEFER_AR)
make ooc CACHE=jetp_fabric ; make ooc CACHE=onyx2            # the two managers alone
python3 ../../jet/host/jet_perf_sweep.py --board genesys2 --profile ref-onyx --outstanding 1 2 4 8 16 --out ../results/perf_sweep_onyx_bin2_dual_<stamp>.json   # SEL 4/5 with the tally chain: bins 11-17 onyx, the six counters per cell
python3 ../bin/ref_compare.py                   # the tables above
```

Simulation gates: `make clean-all && make run-all-gate-parallel` in
`projects/fpga-systems/Genesys2/cache-ip/ref/dv/tests` (harness AXIL tests
and the read-after-write check, all four selections).
