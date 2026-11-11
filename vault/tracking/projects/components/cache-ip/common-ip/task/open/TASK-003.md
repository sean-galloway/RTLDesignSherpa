# TASK-003: reference L1 caches on the pair rig -- HPDcache (non-blocking peer of jet) and the CVA6 write-back dcache (blocking peer of amber)

**Date:** 2026-11-11
**Priority:** P2
**Status:** OPEN (after TASK-002)
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
