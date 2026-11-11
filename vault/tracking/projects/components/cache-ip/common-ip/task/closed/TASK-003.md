# TASK-003: reference L1 caches on the pair rig -- HPDcache (non-blocking peer of jet) and the CVA6 write-back dcache (blocking peer of amber)

**Date:** 2026-11-11
**Priority:** P2
**Status:** CLOSED 2026-11-11 -- both references behind the injector in Verilator (gate 4/4) and on the Genesys2 (HPDcache rig bin 2, CVA6 rig bin 2, smoke PASS, single-core sweeps err 0 at depths 1-16), out-of-context rows for all four, report written.
**Owner:** cache-ip

## Why

amber and jet are complete to their PRDs and measured against each other,
never against anything outside the repo. Published numbers for other L1s
come from different cores, memory systems, parts and clocks, so they only
support order-of-magnitude claims. The fair comparison is a reference cache
behind the same pipelined injector (TASK-002), the same memory model and
the same Kintex-7 at the same clock. Owner, 2026-11-11: "Pick the best
model possible to act as a reference; two if needed."

## What

Selection (2026-11-11), both SystemVerilog, both from the OpenHW CVA6 tree,
both already published on a Genesys2 (Kintex-7 325T):

1. **HPDcache** (CEA / OpenHW `cv-hpdcache`, Solderpad 2.1): non-blocking,
   MSHR-based, out-of-order for non-overlapping addresses, write buffer,
   multi-requester. The closest open design to jet's point (lockup-free L1
   with an MSHR file). Reported +43.5% IPC / +74.1% bandwidth over the CVA6
   blocking cache in CVA6S+ (arXiv 2505.03762), on the same board we use.
2. **CVA6 write-back dcache** (`std_nbdcache` in `cva6/core/cache_subsystem`):
   the blocking L1 HPDcache was measured against, a peer for amber.

Neither is coherent (no ACE snoop side), so the comparison is single-core:
hit latency, hit throughput, miss penalty, MLP, fill bandwidth, LUT/FF/BRAM
per KB and Fmax on the same part. Snoop-side metrics stay jet vs amber.

Work: vendor the two sources under `vendor/` pinned to a commit; a GAXI
cpu_req/cpu_rsp -> native request adapter per cache; memory side onto the
rig's existing AXI memory model; a third rig variant (`ref_pair_harness` or
a single-cache harness) that reuses the injector, tally and UART stack;
sweep the same configs at the same depths; one comparison table.

## Done when

- Both references build in Verilator behind the injector and pass the
  smoke sequence (acc == rsp == count, err 0).
- Genesys2 bitstream per reference at 100 MHz (or the highest closing clock,
  recorded), sweep err 0.
- A comparison report (`projects/components/cache-ip/docs/`) with the
  metric table for amber, jet, HPDcache, CVA6 WB at depths 1..16, and the
  area/Fmax row, stating every place the comparison is not like-for-like.

## Notes from the sources (2026-11-11, clones at scratchpad `ref/`)

- `cv-hpdcache` 40d2897 (2026-11-04), Apache-2.0 WITH SHL-2.1. Top
  `rtl/src/hpdcache.sv`: per-requester `core_req_valid_i/ready_o/req_i`
  arrays plus `core_req_tag_i` / `core_req_pma_i` a cycle after the request
  (virtual-index two-cycle addressing; `phys_indexed` collapses it to one),
  `core_rsp_valid_o/rsp_o` with `sid`/`tid`; memory side is its own
  read/write request + response channels (`hpdcache_mem_req_t`, `_req_w_t`,
  `_resp_r_t`, `_resp_w_t`), AXI-shaped (len/size/id/last) -- CVA6 maps them
  with `cva6_hpdcache_subsystem_axi_arbiter.sv`. Controller is a 3-stage
  pipe, one request per cycle; a load hit answers from stage 1, data RAM
  read latency one cycle. **Responses to non-overlapping addresses may
  return out of order** (tid-tagged), so the GAXI `cpu_rsp` adapter needs a
  reorder buffer keyed by tid to present accept-order responses; the
  injector's latency ring and rsp CRC assume accept order.
- `cva6` 742dc82 (2026-10-23): `core/cache_subsystem/std_nbdcache.sv`
  (Solderpad 0.51) -- `NumPorts` request ports of `dcache_req_i_t/o_t`,
  AXI refill + bypass ports (`axi_req_t/axi_rsp_t`), needs `config_pkg`,
  `ariane_pkg`, `std_cache_pkg` from `core/include`.

## Progress

### 2026-11-11 -- both references behind the injector, in Verilator and on the board

Rig: `projects/fpga-systems/Genesys2/cache-ip/ref/` = the jet pair harness
with ONE reference cache in the slot (`REF_CACHE_SEL` 0 HPDcache, 1 CVA6
write-back dcache), `ref_null_cache` behind injector 1 (the jet host stack
runs unchanged: same bridge, regmaps, smoke, sweeps), `ref_axil_stub` on the
three tally apertures. Vendored subsets: `vendor/cv-hpdcache` (40d2897) and
`vendor/cva6-dcache` (742dc82), each with a PROVENANCE.md and a filelist
under `vendor/filelists/`.

Wrappers (`ref/rtl/`): `ref_hpdcache_top` -- one requester, physically
indexed, loads and stores with need_rsp, a 16-slot tid ring that releases
responses in accept order (HPDcache answers out of order), the upstream
mem-to-AXI adapters; store responses carry zero data (upstream leaves it
unspecified and the rig's read CRC covers every response).
`ref_cva6_dcache_top` -- loads on port 0 with the tag presented a cycle
behind the index (the controller's WAIT_TAG re-grant streams hits one per
cycle), stores on port 1 only while no load is in flight (CVA6 drives the
two from separate units and the controller double-grants a store presented
behind a load hit), accept = grant for both; `ref_cva6_cfg_pkg` sets the
pair rig's geometry (32 KB, 4 ways, 64 B, 64-bit AXI, ID 8).

Vivado lessons, all three fixed in the rig, none in the vendored files:
HPDcache's behavioural SRAM macros type each entry as a two-dimensional
packed array and Vivado builds them from registers ("RAM from
Record/Structs", 283,782 FF, placer refused: bin 1) -- flat-vector
`hpdcache_sram_1rw` / `hpdcache_sram_wbyteenable_1rw` in `ref/rtl/`
(8 RAMB36 + 4 RAMB18). CVA6's `tc_sram_wrapper` has `parameter type` ports
and Vivado 2025.1 synthesizes it to an EMPTY module without a message (37
black boxes, bin 1) -- house `tc_sram` + `tc_sram_wrapper` with plain
vectors. HPDcache also requires byte enables at or above the address
offset within the word, so the wrapper word-aligns the offset (amber and
jet ignore addr[2:0]).

Verification: `ref/dv/tests` gate 4/4 from clean -- the harness AXIL test
per selection (aperture, smoke with counts and a repeatable read-only CRC,
latency instrumentation, pipelined depths 1/8/255) and `test_ref_cache_rw`,
a GAXI read-after-write check per selection (2,048 strobed random writes
over twice the cache, every word read back against a model, three
postures). That check exists because the injector's reads never land on a
word it wrote (addr and we derive from the same LFSR bits), so its read
CRC only ever sees never-written memory -- which is also why a reference
run's read CRC equals the zero stream of the null cache on a freshly
programmed board, and why jet's and amber's differ (their write responses
carry data).

Board (100 MHz, 0.2 ns budget): HPDcache rig bin 2 8,450 LUT / 9,595 FF /
136 BRAM, WNS +1.030, smoke PASS, ci1-idle sweep err 0 at depths 1-16.
Single-core (`--ci1-idle`, injector 1 runs zero transactions) sweeps also
taken on jet bin 17 and amber bin 11 so the three are like-for-like. CVA6
rig: bin 1 failed on the black boxes above; bin 2 building. Out-of-context
cache-only rows (`make ooc CACHE=...`, 10 ns): HPDcache 3,510 LUT /
4,944 FF / 8 RAMB36 + 4 RAMB18, WNS +1.372; jet, amber, cva6 running.

First like-for-like numbers (ci0, 20,000 transactions, board):

| metric | amber | jet | HPDcache |
|---|---|---|---|
| resident hit floor (cycles, injector accept to response) | 4 | 3 | 2 (1 inside the cache + the wrapper's ring stage) |
| hits, depth 1, cycles/txn | 5.0 | 4.0 | 3.0 |
| hits, depth 4, cycles/txn | 3.0 (skid, then blocking) | 1.01 | 1.00 (reads) / 1.12 (25 % stores) |
| 64 KB thrash, depth 1 | 20.9 | 17.4 | 13.7 |
| 64 KB thrash, depth 16 | 18.9 | 10.7 (MLP 7) | 7.6 (MLP 3; it holds ready low instead of queuing) |
| 128 KB thrash, depth 16 | 27.0 | 15.7 | 10.9 |

Comparison report with the CVA6 column and the area rows follows
(`projects/components/cache-ip/docs/reference_l1_comparison.md`).

### 2026-11-11 CLOSED

CVA6 write-back rig bin 2 (house `tc_sram` + `tc_sram_wrapper`): 10,696 LUT
/ 6,481 FF, WNS +0.958 at 100 MHz under the 0.2 ns budget, smoke PASS,
ci1-idle sweep err 0 at depths 1-16
(`ref/results/perf_sweep_cva6_bin2_single_20261111T233015Z.json`).

Out-of-context rows at 10 ns (`make ooc CACHE=...`, summaries under
`ref/results/ooc/`; the first three were re-materialized from the queue log
after the cva6 bitstream's `make clean` wiped `fpga/reports`, and the target
now writes under `results/`):

| cache | LUT | FF | RAMB36 | RAMB18 | LUTRAM | WNS |
|---|---|---|---|---|---|---|
| amber | 3,709 | 2,944 | 16 | 0 | 1,169 | +0.123 |
| jet | 5,892 | 5,258 | 16 | 0 | 1,879 | +0.356 |
| HPDcache | 3,510 | 4,944 | 8 | 4 | 0 | +1.372 |
| CVA6 WB | 5,669 | 1,661 | 32 | 20 | 0 | +0.990 |

Headline (cycles per transaction, injector 0, single core): resident hits
stream at 1.0 per cycle on jet, HPDcache and CVA6 from depth 4, amber 3.0;
64 KB read-lean thrash at depth 16 HPDcache 7.6, CVA6 9.9, jet 10.7, amber
18.9; write-heavy thrash HPDcache 10.5, jet 10.8, CVA6 14.3, amber 28.5. The
report (`projects/components/cache-ip/docs/reference_l1_comparison.md`)
carries the full tables, the accounting caveat (CVA6's accept is its grant,
so compare cycles per transaction across rigs, latency only within one) and
every place the comparison is not like-for-like. Two follow-ups it names:
jet's miss path pays the pair fabric round trip even with the peer idle
(measure jet without the fabric), and amber's skid-then-block port.

Done-when, checked: Verilator build + smoke for both references (gate 4/4
including the GAXI read-after-write check); Genesys2 bitstream per reference
at 100 MHz with sweep err 0; the comparison report with the metric table at
depths 1/4/16 and the area/Fmax row, caveats stated.
