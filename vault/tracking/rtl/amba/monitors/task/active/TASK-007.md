# TASK-007: assess the monitor family for the FPGA-review treatment (jet_monlite, the monlite wrappers, the Ocelus monitors)

**Priority:** P3
**Status:** ACTIVE 2026-11-21 -- owner selected this as the next FPGA-optimization area.
**Owner:** TBD
**Filed:** 2026-11-10, owner direction while closing jet ISSUE-002.

## Why

The 2026-11 FPGA microarchitecture reviews of the memory controllers
(memory-controllers MC-004/005, granite -2,042 LUT) and of cache-ip
(common-ip TASK-001, jet TASK-003) found the same few things over and over:
arrays that an async reset dissolved into flops, combinational reads of
arrays that should have been RAM-shaped and registered, per-entry logic that
a shape change made free, and attributes that never reached the tool. Every
measured rig carries monitors -- `jet_monlite`, `l1_monlite` and the
`axi4_*_monlite` wrappers on the cache-ip rigs, and the lite monitors plus
MonBus aggregation/drain on STREAM/RAPIDS. The full Ocelus `axi_monitor_*`
family survives as the reference/test oracle, not as a current project
consumer (TASK-037). The owner, deciding jet ISSUE-002 (2026-11-10): leave the
drop limit as the error bar, but find out whether the monitors themselves
would benefit from FPGA optimisation.

## What

An assessment first, fixes only where the measurement says so:

- Measure what the monitors cost on current bitstreams:
  `area-measure-by-hierarchy` on the routed cache-ip rigs (`jet_monlite` /
  `jet_prime_monlite`, `l1_monlite`, the rd/wr monlites and MonBus arbiters)
  and on STREAM `build-mon` (`USE_AXI_MONITORS=1`) or an enabled RAPIDS build.
  The STREAM `reports/ooc/stream_core*` rows have `USE_AXI_MONITORS=0` and are
  not an enabled-monitor baseline. Record LUT / FF / LUTRAM / BRAM and whether
  any monitor path is on the critical list.
- Read each monitor module against the review checklist: storage arrays
  behind an async reset, combinational array reads, `ram_style` attributes,
  reset fan-out, one-hot vs encoded state, and per-entry compare trees. The
  full monitor's CAM/age network is measured for comparison only; do not
  reopen its TASK-037 redesign without a real consumer needing its unique
  features and missing timing.
- For each candidate, a same-configuration before/after A/B build, with a
  golden-copy equivalence proof for a nonlocal or combinational rewrite (the
  MC-004/005 method). Use the shared main tree and named-path commits required
  by the repo, not a new worktree; nothing changes without a baseline pair.
- Write the findings into the module docs and the relevant handbook note; file
  a bug or task per real finding. If the measurement says the monitors are
  already cheap, say so with the numbers and close.

Scope: `rtl/amba/ocelus/*` (the lite cores, MonBus infrastructure, and the full
base/trans_mgr/CAM/reporters for measurement), the `*_monlite` wrappers in
axi4/axil4/axis4/cxs/chi, `chi_monitor_lite`, and cache-ip's `l1_monlite`,
`jet_monlite` and `jet_prime_monlite`. Onyx's currently active work is excluded
from the first pass. TASK-005's global timebase and TASK-006's group routing
are separate feature work, not behavior this optimization may change. The
observer rule holds throughout ([[observers-do-not-drive]]): no change may
perturb the measured path, and the present-vs-absent pins in cache-ip DV stay
green.

## Done when

- A cost table per monitor module on at least one cache-ip and one
  STREAM/RAPIDS bitstream, with the critical-path check.
- Each candidate either A/B-measured and fixed (own bug/task, closed) or
  recorded as not worth it with its number.
- jet ISSUE-002's error bar is unchanged by any of it (drop bin still named,
  commit width untouched unless this task's measurement reopens it).

## Storage and reset census (2026-11-21)

No `ram_style` / `ramstyle` attribute occurs in `rtl/amba/ocelus/*.sv`. This is
an inventory of state-holding arrays and packed per-entry table state; the
combinational `c_*` candidate arrays and MonBus interconnect arrays are not RAM
candidates. "Reset-free candidate" still requires a directed stale-data test,
a qualified-read review, and a Vivado inference check before it is kept.

| Module | Arrays / per-entry state | Shape and disposition |
|---|---|---|
| `jet_monlite`, `jet_prime_monlite` | `r_alloc_cyc[MSHR_COUNT]` | One dynamic write at allocation, reset loop today; reads only on merge/retire events. First reset-free distributed-RAM candidate. |
| `l1_monlite` | no persistent arrays; `r_drain_line_q`, `r_fill_line_q`, pending packet/timestamp are scalars | Candidate arrays are combinational. Remove payload reset only where the valid/event qualifier is proven; control stays reset. |
| `axi_monitor_lite` | packed `r_id`, `r_addr`, `r_ts0`, `r_next`, `r_wq`, `r_wq_seq`; mutable `r_beats`, `r_us0`, `r_early_*`; valid/head/tail/pointers separate | First group has allocation/link/push writes and validity-qualified consumers: reset-free unpacked-array candidates. `r_beats`/`r_us0` also update on progress and early state has several cases: keep as flops unless a separate single-write rewrite is proven. |
| `axi4ace_snoop_monitor_lite` | packed `r_addr`, `r_snoop`, `r_ts0`; mutable `r_beats`, `r_us0` | Address/snoop/allocation stamp are allocation-only candidates; beat count and last-progress stamp also update at the head and stay flops in the first pass. |
| `chi_monitor_lite` | request `r_txnid`, `r_dbid`, `r_opcode`, `r_pkts`, `r_dat_rem`, `r_wdat_rem`, `r_us_stamp`, `r_cyc_stamp`; snoop `r_s_txnid`, `r_s_rem`, `r_s_us`, `r_s_cyc` | All are reset today. Allocation-only `r_txnid`, `r_opcode`, `r_pkts`, `r_us_stamp`, `r_cyc_stamp`, `r_s_txnid`, `r_s_us`, `r_s_cyc` are candidates. DBID and remaining-debt arrays update in response/data phases and stay flops. Protocol keying/debt behavior is not negotiable. |
| `axis_monitor_lite`, `cxs_monitor_lite` | no per-entry arrays | Scalar event/episode state only. Any work must come from a measured event/output cone, not a RAM conversion. |
| `apb4_monitor`, `apb5_monitor` | `r_trans_table[MAX_TRANSACTIONS]` | Whole struct resets; command fields are written at allocation while state/response/event fields update later. Split only write-once payload fields from validity/control; do not put the whole struct in RAM. |
| `wb4_monitor` | `track_t r_q[MAX_TRANSACTIONS]` | Command payload writes at push, `rsp_timed_out` later writes at the head. Payload split is a candidate; head/tail/count stay reset. |
| `monbus_cam`, `monbus_cam_pipe` | `r_valid`, `r_key`, `r_data`, `r_ts` | Move-to-front shift writes many constant positions and dynamically selected span. Not RAM-shaped. Key/data/timestamp reset removal is possible only after all match/dump/eviction reads are shown validity-qualified. |
| `monbus_group_core`, `monbus_burst_writer` | `r_os_len[4]`, `r_ws_len[4]` | One dynamic write at AW issue and pointer-indexed read; reset today. Reset-free distributed-RAM candidates with read/write-pointer qualification. |
| `monbus_group_core_1wr` | `r_err_len_q[4]` | One dynamic write at error-AW and pointer-indexed read; same candidate class. |
| `axi_monitor_timeout` | three timer arrays | Per-entry timers update over time; leave as flops. The full monitor is reference-only for this task. |
| `axi_monitor_reporter*` | local transaction table, latency and previous-state arrays | Full-monitor reporter state; no deployed consumer and no rewrite under TASK-037. |
| `axi_monitor_trans_mgr`, `monitor_trans_cam` | CAM IDs/payload, dense ages, W-order/early queues | Full-monitor reference structures. Ages and shift queues are not RAM candidates; measure cost but do not rearchitect without a consumer. |
| `arbiter_monbus_common` | per-client counters/timers | Repeatedly updated accounting state, not write-once RAM. Review only if hierarchy/timing names it. |
| `axi_monitor_addr_check`, `apb_monitor_addr_check` | packed match/shadow configuration arrays | Small configuration state; no conversion without a measured cost/timing reason. |

## Current system baselines (2026-11-21, RTL base 18a4969dc)

The cache OOC runs use the same RTL at 10 ns on the Kintex-7 325T -2; each
`*_nomon` row sets `USE_MONITOR=0`. The summary's optimized LUT count is used
for the pair delta; the hierarchical report's pre-cross-hierarchy-combining
count is used only for the named module rows.

| Cache | Monitor LUT / FF / LUTRAM delta | Named monitor hierarchy (LUT / FF) | Worst monitored path |
|---|---:|---|---|
| jet-prime `jetp6` | 2,125 / 2,371 / 411 | `jet_prime_monlite` 674 / 596; `l1_monlite` 415 / 194; AXI rd/wr 275 / 356 and 252 / 336; arbiters 548 / 1004 and 231 / 413 | 6,033 vs 3,908 total LUT; +0.082 ns, cache fill -> data RAM, not a monitor |
| jet | 2,181 / 2,372 / 411 | `jet_monlite` 715 / 596; `l1_monlite` 410 / 194; AXI rd/wr 246 / 332 and 253 / 336; arbiters 547 / 1004 and 231 / 413 | 5,892 vs 3,711 total LUT; +0.356 ns, cache control -> data RAM, not a monitor |
| amber | 1,339 / 1,238 / 189 | `l1_monlite` 176 / 194; AXI rd/wr 245 / 332 and 253 / 336; arbiters 359 / 665 and 231 / 413 | 3,709 vs 2,370 total LUT; +0.123 ns, control -> monitor output FIFO; monitor path is critical but meets |

The jet/jet-prime `r_alloc_cyc` arrays do not appear in the distributed-RAM
mapping report, matching the async-reset loop seen in the census. That is the
first cache edit candidate.

STREAM `build-mon` was synthesized at its configured 60 MHz with
`USE_AXI_MONITORS=1`: 85,286 LUT / 80,178 FF / 7,204 LUTRAM, setup WNS
+6.898 ns. Its current synthesis worst setup path is 9.591 ns, 26 logic levels,
from `u_dma_observer/g_egress_axil.u_group/u_core/r_aw_cov_beats` to
`r_wr_addr`. This is the inline writer in `monbus_group_core`, not an AXI lite
monitor. The standalone `monbus_burst_writer` already carries a pipelined AW
cap that the inline copy lacks; porting or sharing that proven shape is the
first MonBus timing candidate. The existing `timing_worst.txt` in this build
area is dated 2026-11-11 and was not regenerated by `make synth`; only the
2026-11-21 `timing_summary_synth.txt` is used for this baseline.

### Fresh Kintex-7 OOC rows (6.667 ns)

These are routed out-of-context rows from the expanded sweep. WNS below is
register-to-register; several new protocol wrappers miss only under the OOC
primary-I/O budget and are not misreported as internal timing failures.

| Module | LUT / FF | WNS reg-to-reg | Read |
|---|---:|---:|---|
| `axi4_master_rd_mon` / `_monlite` | 7,164 / 5,552 vs 1,371 / 1,416 | +0.664 / +1.969 ns | Full remains large; lite is the deployed answer. |
| `axi4_master_wr_mon` / `_monlite` | 8,345 / 6,156 vs 1,602 / 1,554 | **-1.124** / +1.957 ns | Full write CAM remains a timing problem; no current consumer. |
| `axis4_master_monlite` | 1,164 / 630 | +1.489 ns | Improved from the September 1,550 / 935 row after the shared FIFO work. |
| `apb4_monitor` / `apb5_monitor` | 518 / 653 and 538 / 676 | +0.812 / +0.553 ns | Small; payload reset removal is area-only. |
| `wb4_monitor` | 541 / 909 | +0.789 ns | Small; payload split is area-only. |
| `chi_rnf_port_monlite` / `chi_hnf_port_monlite` | 4,532 / 3,480 and 4,432 / 3,308 | +0.326 / +0.274 ns | Largest lite-family blocks; storage candidates deserve an A/B, but internal timing already meets. |
| `cxs_master_monlite` / `cxs_slave_monlite` | 2,024 / 1,647 and 1,195 / 550 | +2.131 / +1.650 ns | No array conversion; no timing edit indicated. |
| `axi4ace_snoop_monitor_lite` | 613 / 797 | +1.367 ns | Allocation-payload reset removal is area-only. |
| `monbus_arbiter` | 1,032 / 1,970 | +2.843 ns | Down from 1,821 LUT after MC-004; no repeat skid rewrite. |
| `monbus_axil4_axil4_group` / `monbus_axi4_axi4_group` | 1,679 / 1,030 and 1,909 / 1,272 | **-2.089 / -2.355 ns** | Inline writer is now a timing target. |
| `monbus_group_core` | 1,377 / 552 | **-2.130 ns** | Same inline writer cone. |
| `monbus_burst_writer` | 592 / 379 | +0.757 ns | The pipelined standalone shape meets; use it as the reference for the inline copy. |

### Fresh Artix-7 OOC rows (10 ns)

The complete expanded sweep produced 96 unique fresh module/part rows (48 per
part), with no failed or skipped runs. Selected Artix results:

| Module | LUT / FF | WNS reg-to-reg | Consequence |
|---|---:|---:|---|
| AXI4 full read / lite read | 7,499 / 5,552 vs 1,375 / 1,416 | **-0.629** / +1.732 ns | Same full-versus-lite decision as Kintex. |
| AXI4 full write / lite write | 8,360 / 6,156 vs 1,601 / 1,554 | **-3.779** / +2.030 ns | Do not reopen the full write CAM without a consumer. |
| AXIS / CXS master / CXS slave | 1,164 / 630; 2,024 / 1,647; 1,196 / 550 | +1.112 / +1.860 / +1.109 ns | No timing edit indicated. |
| APB4 / APB5 / Wishbone | 520 / 653; 545 / 676; 541 / 909 | **-0.133 / -0.278** / +0.105 ns | Small but APB timing now deserves a path review before any area-only change. |
| CHI RNF / HNF | 4,647 / 3,480 and 4,558 / 3,308 | **-0.365 / -0.606 ns** | Both miss 100 MHz internally; event/output queue timing joins the storage work. |
| ACE snoop core | 623 / 797 | **-0.425 ns** | Misses 100 MHz internally; review the event cone as well as reset payload. |
| MonBus arbiter | 1,033 / 1,970 | +3.575 ns | Already benefits from the shared skid conversion. |
| MonBus group core / standalone writer | 1,381 / 552 vs 601 / 379 | **-6.750** / +0.174 ns | Strongest fix candidate; port the writer's proven pipeline. |
| `monbus_cam` | 3,197 / 4,422 | **-2.616 ns** | Match -> index -> shift-to -> storage CE chain; evaluate the existing pipelined CAM before changing the base algorithm. |

The full selected two-part table and reproduction commands are in
`docs/markdown/rtl-amba/monitor/monitor_characterization.md`.

## Cache monitor conversion (done 2026-11-21)

Both `jet_monlite` and `jet_prime_monlite` now keep `r_alloc_cyc` in a
reset-free, single-write process with unconditional distributed-RAM attributes.
Allocation overwrites the indexed entry; only merge/retire events read it. A
new `SlotReuse` scenario in each TB checks that a recycled slot's merge/retire
latency uses the newest allocation, including under MonBus backpressure. The
original RTL passed 6/6 in each suite; forcing the timestamp to zero produced
three tap-side failures, including the new scenario. The converted RTL is 6/6
in each. Area gates: jet-prime 21/21, jet 19/19, cache-common 173/173.

| OOC configuration | Before LUT / FF / LUTRAM | After LUT / FF / LUTRAM | Delta and timing |
|---|---:|---:|---|
| jet-prime monitored | 6,033 / 5,402 / 1,998 | 5,926 / 4,977 / 2,142 | **-107 LUT, -425 FF, +144 LUTRAM**; WNS +0.082 -> +0.025 ns, same cache fill/data path class |
| jet monitored | 5,892 / 5,258 / 1,879 | 5,697 / 4,834 / 2,023 | **-195 LUT, -424 FF, +144 LUTRAM**; WNS +0.356 -> +0.245 ns, same cache control/data path class |
| amber monitored | 3,709 / 2,944 / 1,169 | 3,709 / 2,944 / 1,169 | unchanged; no amber RTL was touched |
| all three `*_nomon` | 3,908 / 3,711 / 2,370 LUT | identical | controls unchanged |

Vivado maps each live `r_alloc_cyc` as an 8 x 53 table into 18 RAM32M
primitives under the user attribute. The small WNS differences are placement
variation, not a claimed timing win; neither monitor becomes the critical
path. `l1_monlite` is deliberately unchanged: it has no persistent array, its
scalar payload is small, and amber's measured critical path ends in its output
FIFO rather than the resettable payload. Onyx remains for its active owner.
