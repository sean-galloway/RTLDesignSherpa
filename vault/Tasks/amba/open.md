<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# AMBA tasks — open (not started)

## TASK-098: monitor-lite -- three quarters of the AXI monitor for a fifth of the gates
**Status:** open 2026-09-25 (Sean: "review `rtl/amba/monitor` with the eye of
making a new version of some or all to get 75% of the functionality with ~20%
of the gates; the solution space runs from a simpler `axi_monitor_trans_mgr`
to a new `monitor-lite` directory built for gate count and timing")
**Priority:** P2
**Owner:** TBD
**Related:** [[TASK-072]] (trim the existing family; area not speed),
[[TASK-014]] (per-monitor area, never measured until now), [[TASK-083]],
[[TASK-084]].

This entry is the review. It measures what a monitor costs today and where,
says what "75%" should mean by what the consumers actually use, and proposes
the lite design. Nothing here is built yet.

### 1. What one monitor costs, measured

Out-of-context synthesis, Vivado 2025.1, Artix-7 100T -1 at 10 ns, through
`projects/components/bridge/fpga/` (`make synth BRIDGE=bridge_1x2_rd` and
`bridge_1x2_rd_mon`). The `_mon` bridge is the same 1x2 read fabric with an
`axi4_*_rd_mon` wrapper on each of its three ports, every monitor at the
generator's default preset: `MAX_TRANSACTIONS=16`, `ID_WIDTH=4`,
`ENABLE_ERROR_LOGIC=1`, `ENABLE_COMPL_LOGIC=1`, timeout/threshold/perf/debug
cones OFF, `N_ADDR_RANGES=0`. Post-route, hierarchical (2026-09-25,
`fpga/reports/bridge_1x2_rd_mon__xc7a100tcsg324-1/`):

| Instance | LUTs | FFs |
|---|---:|---:|
| `bridge_1x2_rd` (no monitors, whole bridge) | 826 | 767 |
| `bridge_1x2_rd_mon` (whole bridge) | 12,625 | 7,433 |
| one `axi4_slave_rd` (the thing being watched) | 291 | 224 |
| **one `axi_monitor_base` (read, error+compl)** | **3,249** | **1,628** |
| . `axi_monitor_trans_mgr` | 2,609 | 885 |
| .. `monitor_trans_cam` (16 slots) | 239 | 800 |
| .. trans_mgr minus CAM (per-slot next-state cones, age ranks, pick_oldest, pop-count) | ~2,370 | ~85 |
| . `axi_monitor_reporter` | 640 | 743 |
| .. `intr_fifo` (85 b x 8, LUTRAM) | 467 | 10 |
| .. reporter minus FIFO (its own copy of the table, `r_trans_table_local[N]`, + formatter) | ~173 | ~733 |
| . base + timer + filtered wrapper own logic | ~0 | ~0 (perf-window counters pruned: outputs unconnected) |
| shared per bridge: `monbus_arbiter` (3 clients, skids) | 564 | 864 |
| shared per bridge: `monbus_axil4_axil4_group` | 1,382 | 949 |

Three monitors on an 826-LUT bridge cost 11,800 LUTs: **each read monitor is
eleven times the port it watches**, and the fixture that met 10 ns without
them misses it with them (-0.16 ns, 10 levels).

`bridge_mix_a_mon` (two 32-bit AXI4 rw masters into an APB, an AXI-Lite and
an AXI4 slave, every port monitored both directions -- ten monitors plus the
arbiter and group), same flow, same part: **42,539 LUTs / 25,426 FFs against
6,456 / 5,697 unmonitored**, so the monitor set is 36,083 LUTs, 5.6x the
bridge, and the fixture misses 10 ns by 1.35 ns. Per instance from its
hierarchy (the trans_mgr is 85-90% of each):

| Monitor instance | LUTs | FFs | of which trans_mgr |
|---|---:|---:|---:|
| `axi4_slave_wr_mon` (write, master port side; WID-less W ordering) | 3,853 | 1,929 | 3,385 |
| `axi4_master_wr_mon` (write, slave port side) | 3,464-3,496 | 1,484-1,518 | 3,093-3,134 |
| `axi4_slave_rd_mon` (read, master port side) | 3,029 | 1,625 | 2,567 |
| `axi4_master_rd_mon` (read, slave port side) | 2,815-3,023 | 1,180-1,609 | 2,457-2,503 |

The write monitor is the dearest by 600-800 LUTs: that is the age-rank and
`pick_oldest` machinery recovering AXI4's WID-less W order every beat, the
structure `USE_WDATA_ORDER_Q` already replaces with an N x log2(N) FIFO.

Two things the numbers say that reading the RTL does not:

- **The dead struct fields are already free.** `bus_transaction_t` is ~285
  bits and the CAM holds 16 of them, yet the CAM is 800 flops: 50 live bits
  per slot. Vivado prunes the write-only timers, the unread timestamps
  (threshold cone off), the channel field. [[TASK-072]] item 1 (delete the
  96-bit timers) is right for the RTL's honesty and for ASIC, but on the
  FPGA it recovers nothing that is not already gone. The reporter's private
  copy of the table is the same story: 733 live flops, not 4,560.
- **The cost is combinational, and it is per slot.** 2,370 of the
  monitor's 3,249 LUTs are the trans_mgr's per-slot cones: the three-phase
  next-state machine per entry, the same-ID oldest-first attribution
  (`r_age` ranks plus `pick_oldest`, O(N^2) even at one bank), the
  three-port hit suppression and the command-entry reserve. That is ~150
  LUTs per slot. A lighter *table* does not reach 20%; a lighter *entry
  lifecycle* does.

### 2. What "75% of the functionality" should mean

What the consumers enable and test, from the tree (agent survey 2026-09-25):

| Consumer | Cones built | Packets asserted on |
|---|---|---|
| bridge generator (default `mon_preset = error_only`; `functional` = error+timeout+compl) | error, compl | Error, Completion (`monitor_stress_common.py`) |
| STREAM datapath monitors | perf only (`*_MON_ENABLE_PERF_LOGIC=1`, all else 0) | perf window counters via CSR |
| observers (Genesys2 build-obs) | perf taps; `MAX_TRANSACTIONS=64` | AddrMatch, Completion, Debug, Perf, Threshold on silicon; Timeout still owed (7/7 gate at 6/7) |

Keep (the 75%): error packets for response errors, orphan responses and
beat-count violations with the transaction's ID and address; completion
packets with latency; timeout packets naming the stuck phase; the
active-count threshold; the 128-bit `monitor_packet_t` + 64-bit timestamp
output and UNIT/AGENT ids so the arbiter, group, tally and host tooling are
untouched; the wrapper's cfg surface (unused inputs ignored, not removed).

Drop (the 25%): the perf class (the always-on `axi_bus_meter` and the
observers' perf taps are the perf path now), debug state-change packets, the
address-range checker and report-time address filter, the ID-range filter,
the latency threshold, three independent per-phase timeouts (one "no
progress" threshold, the phase reported in the event code), the
`block_ready` admission stall (replaced by drop-and-count), and unbounded
data-before-address (one early W burst buffered by count, not a table of
them).

### 3. Why the existing design is heavy, in one paragraph

It tracks every transaction as a full record and re-derives everything about
it every cycle: three CAM lookup ports so AW, W and B can each find their
entry independently; an oldest-first attribution among same-ID entries done
with dense age ranks that every survivor recomputes when any entry frees;
per-entry flags for every phase plus a per-entry state machine that a
reporter then scans with priority encoders; a second full copy of the table
inside the reporter; three 16-bit timers per entry ticking in parallel; an
8-deep 85-bit packet FIFO so the table need never wait. Every one of those
is a reasonable answer to a real requirement, and together they are 150
LUTs a slot.

### 4. The lite design (proposal)

`rtl/amba/monitor-lite/axi_monitor_lite.sv` (+ `_pkg` reuse from
`rtl/amba/includes/monitor_*_pkg.sv`; same packet builder). One module per
direction, selected inside the existing `axi4/axi5/axil*_{master,slave}_{rd,wr}_mon`
wrappers by a `MONITOR_LITE` parameter (generate-select between
`axi_monitor_filtered` and the lite), so no consumer changes a port. Bridge
generator: `mon_preset = "lite"`.

Entry (N slots, default 8): `valid, id[IW], addr[PKT_ADDR_BITS], beats_left[8],
phase[1:0], ts[16]` -- 63 bits at IW=4/AW=32.

- **One allocation port, one lookup.** Allocate on AR/AW (free-slot
  priority encode, N bits). Reads: R beats look up `rid`, pick the OLDEST
  matching entry by the smallest `ts` (an N-way 16-bit min tree; AXI
  returns same-ID responses in order, so oldest-matching is exact). Writes:
  no lookup at all -- push the slot index on AW, W beats follow the head of
  an N x log2(N) FIFO (the `USE_WDATA_ORDER_Q` idea, made the only path),
  B looks up `bid` like R. That deletes the age ranks, `pick_oldest`, the
  three-port CAM and the hit-suppression cones.
- **One timestamp does three jobs.** Captured at allocation, refreshed on
  every beat: latency at completion (`now - ts`), timeout (`now - ts >=
  cfg`), oldest-first ordering. Checked by one rotating pointer, one slot
  per cycle, one subtractor: a stuck transaction is reported within N
  cycles of crossing the threshold, which is nothing against a microsecond
  tick. No per-entry timers.
- **Events are computed at the handshake, not scanned for.** Error on
  RRESP/BRESP >= SLVERR, orphan (no match), beat-count mismatch (RLAST
  early or late against `len`), table full. Completion on the last beat /
  B. Threshold on the active count crossing `cfg_active_trans_threshold`
  (a popcount of N valid bits). No reporter-side table copy, no priority
  scan.
- **One packet register, not a FIFO.** Events go straight into the
  128+64-bit output register; error > timeout > completion when two land
  in one cycle; an event that arrives while the register is held by
  backpressure is DROPPED and counted, with one Error/DROP packet when the
  bus frees. The full monitor stalls admission instead; the lite never
  touches the traffic it watches.
- Reuse `counter_freq_invariant` for the microsecond tick (it is tiny) and
  `monitor_common_pkg`'s builder for the packet.

Estimate at N=8, IW=4, AW=32 (counted from the structures above, not
synthesized): table 504 FF + W-order FIFO 24 FF + output register 192 FF +
counters ~60 FF = **~800 FF**; per-slot update ~30 LUTs x 8 + match/min
tree ~90 + formatter ~120 + timeout/threshold ~60 = **~550-700 LUTs**.
Against 3,249 / 1,628 that is **~20% of the LUTs and ~50% of the flops**;
at N=16 roughly 28% / 80%. The flop floor is the 192-bit packet register
the monbus contract requires -- 12% of today's count on its own -- so the
"20%" is a LUT statement, and LUTs are what the routing and the timing pay
for. Every cone is a 4-bit compare, an 8-bit decrement or one 16-bit
subtract: 3-4 LUT levels, which is the timing half of the ask.

### 5. Options, and the recommendation

| | What | LUTs (est.) | Reaches 20%? |
|---|---|---:|---|
| A | Trim the existing family ([[TASK-072]]: dead timers, narrower timestamps, addr) | -5..-10% on FPGA (already pruned) | No. Right for the RTL, not for this ask |
| B | Replace only `axi_monitor_trans_mgr` with the lite table under the existing base/reporter/timeout | ~-55% | No: the reporter alone is 640 LUTs / 743 FFs, and it exists to scan a table the lite does not keep |
| C | `monitor-lite`: new table, events at the handshake, single output register; selected by a wrapper parameter | ~-75..-80% | Yes |

**Recommendation: C, behind the existing wrappers.** B looks like the safe
middle and is not: half the remaining cost is the reporter and timeout
blocks, whose design assumes a scanned table of rich records. A is worth
doing for ASIC honesty under TASK-072 and changes nothing here.

### 6. Verification contract

The lite is not a new protocol; it is a subset. The existing tests are the
contract, run against the same wrappers with `MONITOR_LITE=1`:
`test_axi4_monitor` (the stress sweep -- the modes that drive perf/debug/
addr-check skip by parameter), `test_axi_monitor_runtime_disable`,
`test_axi_monitor_soak`, `test_axi_monitor_wr_same_cycle`,
`test_axi_mon_block_ready` (inverted: the lite must NEVER deassert ready
into the traffic), `test_axi_monitor_pktgen`'s timeout starvation, and the
bridge's `test_bridge_*_mon_monitor` stress files on a `mon_preset = "lite"`
regeneration. New: a drop-and-count test (backpressure the bus, prove the
count and the DROP packet), and a directed same-ID reorder test for the
ts-oldest attribution. Formal: one harness, `formal/amba/axi_monitor_lite`,
proving the table cannot leak (every allocated slot frees on its last beat
or B) and active_count is a popcount. Synthesis gate: `bridge_1x2_rd_mon`
regenerated lite must land under 25% of today's monitor LUTs on the same
flow, and meet 10 ns on the Artix-7 with margin.

### 7. Risks and open questions

- **Data before address.** A slave-side write monitor can see W beats before
  AW. The lite buffers ONE early burst as a beat count and applies it at the
  AW; a second early burst before the first AW is an Error/ORPHAN. The full
  monitor tracks these as entries. Acceptable for 75%? (Sean.)
- **No admission stall.** Consumers that relied on `block_ready` to bound
  the table (the observers at 64 slots) get drop-and-count instead. That is
  a behaviour change worth stating on the observers' page.
- **STREAM/observers are perf-first.** They gain nothing from the lite until
  the perf path is confirmed fully outside the monitor (the memory says it
  is: `axi_bus_meter`); the lite has no perf class by design.
- **ID width.** The oldest-by-timestamp attribution is exact for any IW;
  the table depth is the only capacity knob, and refusing an allocation is
  a counted event, never a mis-attribution.

### Definition of done

`rtl/amba/monitor-lite/` with filelist, `docs/markdown/rtl-amba/monitor-lite/`
pages, the wrapper parameter, the bridge preset, the contract tests green at
gate/func/full, the formal harness non-vacuous, and the synthesis row that
shows the number. Then the observers and STREAM decide per instance.

---

## TASK-072: Lighten the gate-heavy monitor modules
**Status:** open 2026-08-31 (Sean)
**Priority:** P2
**Owner:** TBD

**MEASURED 2026-09-01 (stream-genesys session): the bank-local pre-reduction
`6617b0d2` does NOT recover the timing.** Genesys2 build-mon, same board, same
11.111 ns constraint, same flow, clean-all both times:

| | before | after `6617b0d2` |
|---|---|---|
| WNS | -1.733 ns | -2.008 ns |
| TNS | -9241.290 | -11288.290 |
| failing endpoints | 7,597 | 7,696 |
| total endpoints | 326,977 | 328,238 |

**Read that as "no measurable effect, direction indeterminate" -- not as a
regression.** Two runs of a congested design land more than 0.3 ns apart on
placement alone, and the endpoint count moved by 1,261 because other monitor
work landed between the builds, so the two numbers are not even the same
design.

What it actually tells us: the cross-bank OR was not the binding constraint.
The failing path was 8.305 ns route against 3.994 ns logic, and collapsing 72
fabric-crossing wires to 8 should have bought something -- so either the
congestion is broad enough that removing one cone does not move the critical
path, or the critical path has moved elsewhere. Nobody chased which, and that
is the right call: frequency is the knob here, and the monitor campaign now
builds at 75 MHz (CLKOUT0_DIVIDE=18), which closed at +0.009 ns even before
the change.

**The change stays in**, on the grounds it was committed under: strictly
better structure at zero behavioural risk (OR is associative; the rewrite is
bit-identical for every input). The difference now is that it is measured
rather than assumed, and `6617b0d2`'s framing -- which reads as though the
restructure would recover the 1.733 ns -- should be read with this row
attached.

Lesson for the rest of this task: **a route-dominated path does not mean the
widest cone is the cause.** The reasoning that picked this cone was sound and
still produced no movement, so the remaining TASK-072 levers need a measured
before/after each, not a structural argument.

Standing work item: the monitor family carries more registers and wider cones
than it needs, and it now costs something real -- the Genesys2 `build-mon`
configuration misses setup by 1.733 ns with 7182 of 7597 failing endpoints
inside `axi_monitor_trans_mgr`'s banked CAM. This is the scoping pass, done
against the tree 2026-08-31 so nobody starts from impressions.

### Why it is worth doing, with a number

Deleting ONE dead output on 2026-08-31 (`state_change`, `1f2043f0`) removed
`bus_transaction_t r_trans_table_prev [N]` -- N x ~285 bits. At the Genesys2
N=72 that is ~20,500 flops, and the board build's LUT count fell 138,996 ->
126,628 across that window. Dead state in this family is not a rounding error.

### The storage is dominated by ONE struct

`bus_transaction_t` (in `rtl/amba/includes/monitor_amba4_pkg.sv`) is ~285 bits
and the transaction table is N of them. Six 32-bit fields are 192 of those
bits. Everything below is a consequence of that.

### 1. THE THREE TIMERS ARE WRITE-ONLY -- 96 bits/entry, free to delete

`addr_timer`, `data_timer`, `resp_timer` are 32 bits each and **nothing reads
them anywhere in the repo**. Checked exhaustively over `rtl/`, `projects/`,
`val/` and `formal/`: every occurrence outside the declaration is an assignment
of `'0` --

    axi_monitor_trans_mgr.sv:1204,1210,1211,1222,1246,1341   next.*_timer = '0
    apb4_monitor.sv:342,343 / apb5_monitor.sv:429,430        r_trans_table[..] <= '0

...plus a field-layout table in `val/amba/test_axi_monitor_trans_mgr.py:97-99`
that merely describes the struct. The ACTUAL phase timing lives in
`axi_monitor_timeout.sv`, which keeps its own `r_addr_timer [MAX_TRANSACTIONS]`
at `TIMER_W` bits. So the struct copies are a second, dead set.

**96 bits x N.** At the default N=16 that is 1,536 flops; at the Genesys2 N=72,
6,912. Same class as the write-only `r_expected_weights`/`r_actual_weights`
removed from `arbiter_monbus_common` in `e7fec230`, roughly 90x the size.

Start here. It is the largest single win and the safest.

### 2. The timestamps are live, but wider than their use

`addr_timestamp`, `data_timestamp`, `resp_timestamp` -- another 96 bits/entry.
These ARE read, by exactly one consumer: `axi_monitor_reporter_threshold.sv`
lines 120-124, and only as DIFFERENCES (`resp_timestamp - addr_timestamp`).
Nothing consumes an absolute time. So the width only has to cover the longest
latency worth reporting, not a free-running 32-bit counter, and the threshold
they feed (`cfg_latency_threshold`) bounds that. Narrowing needs care about
wrap: a difference is only valid while the elapsed time is under half the
counter range, so the analysis is "what latency must we still measure
correctly", not "what fits".

### 3. `addr` is 32 bits per entry and may not need to be

`bus_transaction_t.addr` is a full 32-bit copy. Worth checking what actually
consumes it -- if it is only the packet payload and the address filter compare,
the entry may be able to hold fewer significant bits, or the filter verdict
alone (`filtered_mask` already latches per entry).

### 4. THE CROSS-BANK ALLOCATION CONE -- DONE, and CLOSED as a timing driver

**Decision 2026-08-31 (Sean): "don't sweat stream timing; we can lower the
frequency."** That is the recorded design point for this board -- 8 channels
and AR/AW=8 are REQUIREMENTS, frequency is the knob -- so the Genesys2
`build-mon` setup failure is NOT a justification for further monitor work.
Do not reopen this item on timing grounds.

What landed anyway, because it was free: `6617b0d2` reduces the hit_any cones
per bank before combining them. Bit-identical (OR is associative), but only
NUM_BANKS wires cross the fabric instead of N. Kept because it is strictly
better structure at zero behavioural risk, not because timing demanded it.

Two levers deliberately NOT taken, and they stay not-taken:

* Selecting `wb_addr_pend_any[bank_of(cmd_id)]` -- narrower, but it makes
  correctness depend on the same-ID-stays-in-one-bank invariant holding at
  RUNTIME rather than structurally. Not worth it for a frequency we can lower.
* Making `w_cmd_headroom` per-bank -- that changes admission semantics, not
  just timing.

**So the remaining value in this task is AREA, not speed.** Item 1 (the
write-only timers) is the whole point: 96 bits x N of dead registers. Judge
any future work here on flops removed at unchanged behaviour, and ignore WNS.

The original description follows, for the record:

    assign addr_hit_any     = |w_addr_pend_oh;                   // OR over ALL N slots
    assign w_cmd_headroom   = w_cmd_entry_count < (N - RESERVE); // count over ALL N
    assign addr_wants_alloc = cmd_valid && !addr_hit_any && w_cmd_headroom;

then per bank: `.addr_wants_alloc (addr_wants_alloc && (bank_of(cmd_id) == gb))`.

A valid bit in ANY bank feeds a 72-wide OR that gates allocation in EVERY bank,
so `g_cam_bank[1].r_v -> g_cam_bank[2].r_p` is a real edge -- which is exactly
the worst path the board report names. The per-bank gate does not break it
because the suppression term upstream is global. Banking localised the CAMs and
the age ranks; it never localised this.

`monitor_trans_cam.sv:98` documents the invariant that makes the fix safe: the
alloc mask exists to "keep every entry for a given ID inside that ID's bank".
If that holds, a same-ID pending entry can only be in `bank_of(cmd_id)`, so the
other slots are being scanned for an answer that cannot be there. Scoping
`addr_hit_any` to the ID's bank turns a 72-wide OR into a 9-wide one.

`w_cmd_headroom` is the second global term but is a DIFFERENT decision: the
reserve is table-wide today, and making it per-bank changes admission
semantics, not just timing. Measure `addr_hit_any` alone first.

### 5. Structural survey -- where the cones are

    module                       lines  always_ff  N-loops
    axi_monitor_trans_mgr         1606     12         24
    monbus_group_core             1176      6          0
    arbiter_monbus_common         1001      9         16
    axi_monitor_base               945      5          0
    axi_monitor_reporter           657      1          4
    axi_monitor_addr_check         424      1         10

`trans_mgr` is the target by every measure. `arbiter_monbus_common` is second
and already yielded dead state once, so it is worth a proper read.

### Constraints -- read before touching anything

- **`bus_transaction_t` is SHARED.** Every monitor and both APB monitors
  populate it. Removing or narrowing a field is a family-wide change: every
  producer must be updated in the same commit or the field reads X. This is
  the thing that makes it a task rather than a drive-by.
- **Prove each removal is dead the way the timers were proven** -- exhaustive
  grep over rtl/, projects/, val/, formal/ for reads, not just a glance at the
  owning module. The three timers survived years because "the timeout module
  has timers" reads as "the timers are used".
- **Mutation-check the area suite after each step**, and re-run the five
  monitor proofs -- `axi_monitor_filtered`'s harness went vacuous once
  already ([[8f1fc3e4]]), so a green proof is not by itself evidence.
- **Do not chase LUTs into the tests.** Success is fewer flops and shorter
  cones at unchanged behaviour; `val/amba` stays at its current pass count.

### Definition of done

Item 1 landed and measured; items 2-4 each either landed or explicitly
rejected with a reason in this entry. A re-synthesised `build-mon` number,
since that is the case that made this visible.

---

## TASK-014: Performance Characterization
**Priority:** P2
**Status:** Not Started
**Owner:** TBD

**Description:**
Characterize resource utilization and performance impact of monitors.

**Metrics to Collect:**
- [ ] Area (LUT, FF, BRAM) per monitor type
- [ ] Timing impact (critical path analysis)
- [ ] Power consumption (if measurable)
- [ ] Comparison: AXI4 vs AXIL vs APB vs AXIS
- [ ] Comparison: With vs without clock gating

**Deliverable:**
- [ ] Performance characterization report
- [ ] Recommendations for resource-constrained designs
- [ ] Optimization opportunities identified

---

## TASK-022: Make APB Crossbar Variants Functional
**Priority:** P2
**Status:** Not Started
**Owner:** TBD
**Effort:** Medium (2-3 days)
**Dependencies:** None

**Objective:** Get all APB crossbar variants working and tested

**Background (STALE — see note):** written when `apbx_xbar_thin` was the
only proven variant. As of 2026-08-27 all five generated variants
(1to1/2to1/1to4/2to4/2to2_mixed) pass 8/8 and lint clean, and thin has
been deleted. **This task looks complete; it needs closing or rescoping
rather than doing.**

**Requirements:**

2. **Fix/Verify Buffered Variants**
   - Test apbx_xbar with buffering enabled
   - Identify and fix any issues
   - Verify backpressure handling

3. **Full Feature Testing**
   - Multiple masters × multiple slaves
   - Concurrent transactions
   - Address decoding
   - Error responses

4. **Documentation**
   - Document working variants
   - Configuration guidelines
   - Performance characteristics

**Deliverables:**
- [ ] All APB crossbar variants functional
- [ ] Comprehensive test coverage
- [ ] Configuration guide for variant selection
- [ ] Integration examples updated

**Success Criteria:**
- All APB crossbar tests passing
- Documented working configurations
- Clear guidance on variant selection

---

## TASK-024: Write Monitor System Whitepaper
**Priority:** P3
**Status:** Not Started (stub created 2026-05-29)
**Owner:** Sean (author) / Claude (assist)
**Deliverable:** `docs/markdown/rtl-amba/monitor_system_whitepaper.md`
> Note (2026-07-22): the 2026-05-29 stub is not present in the current tree; recreate it when this task starts.

**Description:**
2-3 page whitepaper that frames the monitor system as a *design surface*
for SoC integrators -- not a status snapshot of what is in place, but a
guide to which knobs the integrator owns and how to spend them. Different
from `docs/markdown/rtl-amba/overview.md` (which describes the as-built
implementation) and from the per-module specs under `shared/` (which
describe specific blocks). This paper sits one level up: "here is the
spine, here are the axes, here are the tweaks."

**Section outline** (stub already in place):

1. **Identity space allocation** -- UNIT_ID / AGENT_ID / CHANNEL_ID as
   designer-owned. Includes the worked example of allocating UNIT_ID one
   level down so each unit gets up to 16 internal sub-busses to track.
2. **Where to insert monitoring** -- per-port (current default), mid-fabric
   (for localizing fabric-internal violations), root-of-tree (aggregate
   only, trades resolution for area).
3. **Timestamp policy** -- current locked to the monbus_group family's local
   counter. Future direction: hybrid `{global_us[47:0], local_cyc[15:0]}`
   so cross-subsystem correlation and per-wrapper resolution share the
   same 64-bit field. Also a note on PTP / external time-source variant.
4. **Drain path selection** -- err FIFO (IRQ) vs. write FIFO (bulk
   trace), per-packet-type routing via `cfg_*_err_select`.
5. **Packet-type filtering** -- masking strategy, the
   completion+performance congestion pitfall, runtime-reconfigurable
   masks via control APB.
6. **Aggregation topology** -- tree-of-arbiters default, WRR variant for
   skewed traffic, protocol-partitioned groups.

**Out of scope** for the whitepaper (covered elsewhere):
- Packet bit-layout (in `docs/markdown/rtl-amba/includes/monitor_package_spec.md`)
- Per-module port lists / timing (in `docs/markdown/rtl-amba/monitor/{module}.md`)
- Specific test recipes (in the relevant test source).

**Completion checklist** (already mirrored at the bottom of the stub):
- [ ] Pull representative deployment numbers from stream_char on
      Nexys A7 (perf-section figures).
- [ ] One block diagram per section showing as-built vs. tweaked
      configurations side-by-side.
- [ ] Cross-link each section to its per-module spec under `shared/`.
- [ ] Expand the timestamp section into an appendix once the
      hybrid-global scheme is prototyped.
- [ ] Add a verification section pointing at the slave-BFM error-
      injection pattern (`test_bridge_1x2_rd_monitor_error_inject.py`)
      as the template for validating tweaks in simulation.


---

## TASK-078: scrub the tests for completeness (amba)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way.

**Sequencing.** This is a FOCUSED pass, run after qc/humanize is finished
everywhere, and BEFORE coverage and formal are driven clean. Doing it after
coverage would mean chasing numbers produced by tests nobody has audited.

**Scope:** `val/amba/` -- AXI4/AXI5, APB4/APB5, AXI-Stream, gaxi, the monitor subsystem and monbus.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract, with the CocoTBFramework
treated as reviewed ground truth rather than an audit target. Start there
rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and this area has already produced them:

- `apb5_master` (2026-09-04): the suite was green *because* the RTL was
  broken. Nothing drove `rsp_ready`, so the response skid filled after
  RSP_DEPTH transfers and never drained; the master held PSEL/PENABLE past
  PREADY, and `wait_for_transaction()` scored that state a pass. Fixing the
  RTL made the old test time out. The witness added with the fix counted 59
  protocol violations across 70 bus completions on the unfixed design --
  none of which any prior test noticed.
- `apb5_slave` had no coverage at all for the orphan-response case that
  `apb4_slave` was hardened against after a real Nexys A7 misalignment.
- `test_apb5_master.py` pinned `testcase=` to a single cocotb test, so a
  second test added to the file silently never ran. Worth grepping for
  repo-wide: any pinned `testcase=` hides every other test in its module.

**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names (the
  `bin/check_test_dut_family.py` gate catches the family-level version of
  this; it does not catch a test that drives the right DUT trivially).
- No test asserts a condition the bug itself satisfies. The apb5 case is the
  template: `wait_for_transaction()` returned True on `PENABLE && PREADY`,
  which is exactly the state the defect produced.
- Inputs the DUT needs are actually driven. `rsp_ready` was never assigned in
  the apb5 master TB, so the response path was never exercised.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- the TASK-068 witness added beside the basic
  test ran zero times until the pin was widened. Grep for `testcase=`
  repo-wide; a comma-separated list is the fix when a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** amba TASK-077 (CLOSED 2026-09-25, now in `closed.md`)
documented the doc-side equivalent (examples that
name ports which do not exist). The test-side is this task.

---

## TASK-083: monitor TIMEOUT packets saturate at ~table depth per reset

**Priority:** P2. The class is proven reachable but its throughput is not, so
no campaign can use timeout counts as evidence of anything.

**Status:** FIXED IN COSIM 2026-09-15 -- rotating-priority grant in
`axi_monitor_reporter.sv`, gated by a sustained-competition regression.
Entry stays OPEN: the Done-when is board evidence, which is still owed.
Was: open 2026-09-07, scoped only, deliberately not fixed.

**The measurement, which is the part worth keeping.** Genesys 2 `build-obs`
(4ch, 60 MHz, three reps across both observers, slave response delayed 2048
cycles so transactions genuinely expire) — one campaign, one traffic pattern,
all seven classes keyed and 0 unexpected:

| class | packets |
|---|---|
| perf | 1,138,364 |
| compl | 13,470 |
| debug | 13,212 |
| addrmatch | 13,230 |
| error | 13,206 |
| threshold | 13,206 |
| **timeout** | **21** |

Timeout is three orders of magnitude below every other class **from the same
stimulus**. The 13,206 threshold packets are the control: they come from the
identical delayed traffic, so the stimulus and the keying are proven good and
the shortfall is in the monitor. 21 is close to the transaction-table depth, which is
the signature of "each slot reports at most once and is then never reusable for
another timeout" rather than of packets being dropped or miscounted.

**Why this is a task and not a bug report:** every link in the lifecycle exists,
so something in it fails to close, and which one is a measurement question:

    phase timer expires -> sticky per-slot detect
      -> entry moves to TRANS_ERROR
      -> the timeout reporter claims it
      -> event_reported is set ONLY on an ACCEPTED monbus FIFO write
      -> cleanup frees the slot (TRANS_ERROR is eligible, gated on that flag)
      -> retire clears the sticky flag and the slot is reusable

Ranked suspects, cheapest first: (1) reporter arbitration starvation — priority
is error > timeout > compl and exactly ONE slot is marked per accepted FIFO
write, so timeout may never win under completion traffic; (2) monbus FIFO
backpressure, which stalls retirement and reporting together because they share
the same accept; (3) a phase-pending that never drops. Instrument reporter
grants per class and sample active_count before changing anything.

**The wrong fix, recorded so it is not re-made:** do not retire the slot on
TRANS_ERROR. A detected timeout is what puts the entry INTO that state; the
error reporter masks slots whose timeout flag is set and the timeout reporter
claims them, so clearing there erases the flag exactly when the reporter needs
it and makes the timeout packet type unreachable entirely. That trade already
happened once.

**Scope:** shared `rtl/amba` monitor code, consumed by every `*_mon` variant and
by pumice. Needs the monitor formal set plus the `val/amba` monitor subset, not
a one-instance patch. Owner has simplification plans for the monitor, so treat
the RTL pointers below as "true on 2026-09-07", not as durable addresses:
`rtl/amba/monitor/axi_monitor_timeout.sv` carries the same note as
`TODO(MON-TIMEOUT-CAP)` (commit d3643c04), with the lifecycle detail in
`axi_monitor_reporter.sv` (the `w_fifo_wr_accept` marking) and
`axi_monitor_trans_mgr.sv` (`w_can_cleanup`). **If the monitor is rewritten and
those files change shape, this page is the surviving copy — re-point it, do not
delete it, until a campaign shows timeout tracking the other classes.**

**MEASURED AND FIXED 2026-09-15 (fix landed; entry stays OPEN -- see Done when).**

**Suspect (1) was right, but its stated MECHANISM was wrong, and the wrong
mechanism is the expensive part.** This page said timeout "may never win under
completion traffic". Completion is the LOWEST of the three priorities, so it
cannot starve timeout, and anyone who instrumented completions -- as this page
told them to -- would have found nothing and concluded the suspect was wrong.
Measured on a 16-slot table, both arms, same harness:

| competing class | timeout grants |
|---|---|
| vs COMPL | 8 of 8 |
| vs ERROR | 8 of 8 (finite burst) |
| vs ERROR, SUSTAINED | **0** |

Only ERROR starves timeout, and only when it is CONTINUOUSLY pending.

**Why the finite-burst arms both said "no bug".** With one FIFO write per cycle
and 16 total events, everything drains in ~16 cycles whatever the priority is --
a finite burst measures drain ORDER, not starvation. The board sees ~13,206
competing events sustained across a run. Reproducing that needs the higher class
to always have something pending:

    sustained 3000-cycle window, 8 timed-out slots + 8 continuously re-armed
    error slots:   error=2999  timeout=0  compl=0
                   timeout_detected=0xff   event_reported=0x600

Eight slots detected as timed out; not one ever reported. And because
trans_mgr's `w_can_cleanup` gates freeing on `event_reported`, those slots are
never freed either -- which is exactly this page's "~= table depth" signature.
Suspects (2) monbus FIFO backpressure and (3) a stuck phase-pending were not
needed to explain it and were not implicated.

**The fix: a rotating-priority grant in `axi_monitor_reporter.sv`.** As this
page required, it is a fairness term in the priority mux and NOT a change to the
retire policy; `w_auto_retire` is keyed off state and `cfg_*_enable` only and is
untouched, and TRANS_ERROR was NOT added to any retire path.

The one non-obvious constraint: the write mux and the event-MARKING block each
re-derived the same `err > to > compl` chain INDEPENDENTLY. A fairness term
applied to one alone would write one class's packet while crediting a different
class's slot -- worse than the starvation. So the grant is computed once
(`w_grant_sel`/`w_grant_valid`) and both consume it. The three classes are
disjoint by construction (reporter_error takes ERROR&&!detected plus ORPHANED,
reporter_timeout takes ERROR&&detected, reporter_compl takes COMPLETE), so
rotation can never double-claim a slot. The pointer advances only on an
ACCEPTED write -- advancing on a refused grant would rotate past a class that
never got to report.

    same sustained window, after the fix:
                   error=2991  timeout=8  compl=0
                   first timeout grant at cycle 3
                   event_reported=0x3ff   (was 0x600)

All eight timed-out slots now report and become reclaimable, and the dominant
class gives up 8 of 2999 grants to get it.

**Regression:** `cocotb_test_timeout_starvation_sustained` in
`val/amba/test_axi_monitor_pktgen.py` is the RED-to-GREEN gate (it arms on
`error > 100` first, so a quiet run cannot pass it vacuously);
`cocotb_test_timeout_starvation` is the finite-burst control that must stay
green. Both at `n_slots=16`, seed pinned.

**This entry stays OPEN.** The Done-when below is a Genesys 2 `build-obs`
campaign clearing `host_obs_matrix.py` at 7/7, which cannot be run on the
development host. The cosim defect is fixed and gated; the board evidence is
still owed.

**Done when:** a monitors-on campaign drives timeout packets into the same
order of magnitude as the other classes from the same traffic, and
`host_obs_matrix.py` clears its 1000-packet floor on 7/7 instead of 6/7.

## TASK-084: SOFT_RESET does not fully reset the monitor subsystem

**Priority:** P2. It makes the board campaign order-dependent, so a packet class
can read as broken purely because of what ran before it.

**Status:** open 2026-09-08. Diagnosed to the boundary; NOT fixed.
Narrowed 2026-09-15: BOTH the monbus GROUP and the OBSERVER are excluded in
cosim, each mutation-checked. The cause is still unidentified; what remains is
the tally CAMs, u_stream, the unit_aresetn FANOUT, and the host side.

**MEASURED 2026-09-15: the monbus GROUP is excluded as the carrier of the
surviving state.** This is the group-level half of the "next probe should be
internal" step this entry asks for, run in cosim, not reasoned from CSR reads.

`val/amba/test_monbus_group_soft_reset.py` drives two back-to-back scenarios
across a reset pulse on `monbus_axil4_axil4_group` and samples the group's own
FIFO-occupancy ports either side of it:

| phase | err_fifo_count | write_fifo_count |
|---|---|---|
| A: fill BOTH paths, no drain | 8 | 14 |
| B: after a 16-cycle reset pulse | **0** | **0** |
| C: drive + drain after the reset | 8/8 records decoded | - |

The group clears completely across the reset and emits normally afterwards,
with all eight phase-C records drained back OUT through the AXIL slave-read
port and each one's packet_type, protocol, channel_id and event_data verified.
It does not reproduce the order dependence.

**Mutation-checked, because a probe that has never failed proves nothing.**
With the reset pulse suppressed, phase B reports err=8 write=9 -- state
retained -- and phase C's decode fails on CONTENT (it drains stale phase-A
records). Both assertions fire with their intended diagnostics, so the test can
tell the defect from its absence.

**What this does NOT exclude, and where the next probe goes.** Only the LAST
stage of the board path is cleared here. The board path is
stream -> monitors -> observers -> tallies -> monbus group, so
`axi_monitor_base`, the two observers and the tally CAMs are all still live
candidates. And this pulses the group's own `axi_aresetn` directly, whereas
`CTRL.SOFT_RESET` drives `unit_aresetn` across a much larger subsystem -- the
reset FANOUT is not what is being tested here.

**Re-measure on the board before hunting further.** TASK-083's reporter
starvation fix landed the same day (b4d00d995). That defect left terminal slots
permanently unreported and therefore never freed, and "only the scenario that
runs first emits anything" is a plausible signature of slots leaking across a
run. Whether the two are connected is a board question, not a cosim one -- but
a `build-mon` campaign should be re-run on the fixed RTL before anyone spends
more time on this entry.

**Criterion discipline, recorded because it nearly produced a fake result.**
The first draft of this probe keyed on `test_basic_packet_flow`, whose
`success_rate` counts `send_packet()` returns -- the GAXI master accepting
packets INTO the group. That is the STIMULUS, not the emission: it reads 1.0
even when the group emits nothing, so it could never have detected this defect,
and it passed on the first run. The fix was to key on records drained back OUT.
Separately, an all-ERROR fill left `write_fifo_count` at 0, which made the
"write FIFO cleared" half of phase B vacuous -- a path that never held state
cannot demonstrate that reset clears it. Fill both paths, and arm on both.

**THE UPSTREAM HALF, MEASURED 2026-09-15: the OBSERVER is excluded too.**

`cocotb_test_observer_reset_reissue` in
`projects/components/misc/dv/tests/fub/test_axi4_intf_observer.py` (master and
slave wrappers, on `_PARAMS_ALL` so `N_ADDR_RANGES=4` and AddrMatch is
reachable). Two identical traffic batches separated by a reset pulse, with the
observer REPROGRAMMED between them exactly as a board scenario's `setup()` does
after `CTRL.SOFT_RESET`.

| | master | slave |
|---|---|---|
| batch 1 classes | AddrMatch, Completion, Debug, Perf, Threshold | same |
| batch 2 classes | **identical set** | **identical set** |
| packets (b1 / b2) | 39 / 39 | 42 / 55 |
| ADDR_RANGE_CTRL | 0x0 power-on -> 0x1 programmed -> **0x0 after reset** | same |
| timebase (b1 max ts -> b2 min ts) | 334 -> 135 | 256 -> 123 |

Batch 2 emits the same packet classes as batch 1, AddrMatch included -- the
exact class the board loses. So the observer does not carry the surviving state
either.

The timebase numbers are worth keeping: batch 2's lowest timestamp is BELOW
batch 1's highest, so the reset reaches the block's COUNTERS and not merely its
CSRs. (Corroborating evidence, not a mutation-proven assertion -- suppressing
the reset trips the CSR check first, which sits earlier.)

**Mutation-checked on both load-bearing assertions:**
- skip the reprogram after the reset -> "batch 2 emitted NO AddrMatch after a
  reset that followed prior traffic" fires;
- suppress the reset pulse -> "ADDR_RANGE_CTRL reads 0x1 after the reset pulse
  but 0x0 after power-on reset" fires.

**THE REPROGRAM BETWEEN BATCHES IS LOAD-BEARING, and mutation A is the proof.**
The reset disarms the address ranges (correctly -- it restores CSR reset
values). Omit the reprogram and batch 2 emits no AddrMatch for a completely
legitimate reason, which reads exactly like a reproduction of the board bug. A
probe written without it would have "confirmed" TASK-084 and been wrong.

**WHERE THIS LEAVES THE HUNT.** Cosim now clears both stages that were the
leading suspects:

    stream -> monitors/OBSERVER (cleared) -> tallies -> monbus GROUP (cleared)

Still untested here, in rough order of promise:
- the TALLY CAMs between the observers and the group;
- `u_stream` itself;
- the board's reset FANOUT. Every probe so far pulses one block's own
  `aresetn` directly; `CTRL.SOFT_RESET` drives `unit_aresetn` across a much
  larger subsystem, and nothing in cosim has exercised that distribution;
- the HOST side. The board runs scenarios from a host program over UART. An
  order dependence can live in host-side state or in the programming sequence
  and would look identical from the packet counts.

**Re-measure on the board before spending more on cosim.** TASK-083's reporter
starvation fix (b4d00d995) landed the same day; it left terminal slots
permanently unreported and therefore never freed, and "only the scenario that
runs first emits anything" is a plausible signature of slots leaking across a
run. A `build-mon` campaign on the fixed RTL may simply close this.

**Method note worth reusing:** the stock `check_record_framing()` CANNOT be used
across a reset. It walks every record with a 64-tick timestamp-monotonicity
tolerance, and the reset restarts the timebase -- measured 197 ticks
"backwards" at the batch boundary, which is the reset working correctly. It
failed the probe for entirely the wrong reason. Validate framing PER BATCH and
treat the backwards jump as evidence instead.

**The observation.** On Genesys 2 `build-mon`, the `addr_error` scenario emits
129/122 ADDR_RANGE packets when it is the FIRST thing run after the bitstream is
programmed, and ZERO if any other scenario ran first: `--only addr_error` passes,
`--only perf,addr_error` does not. Every scenario already begins with
`CTRL.SOFT_RESET`, which fans out to `unit_aresetn` and demonstrably clears the
datapath and the tally CAM.

**Ruled out -- all measured on the board, none of which fixes it:**

- restoring every monitor CSR to its RDL default (86 registers). This makes it
  WORSE: `PKT_MASK` resets to `0xFFFF` and `0` means allow, so the reset value
  blocks every class and the campaign reports 0/6.
- clearing the perf windows (`*_PERF_CTRL`, `*_PERF_WINDOW_CYCLES`)
- restoring `*_TIMEOUT` and `*_LATENCY_THRESH`, which the perf scenario leaves at
  5000 and 20 and nothing else ever rewrites
- running `enable_monitors` for every scenario instead of skipping it for
  `addr_error`. The skip was pointless anyway, since `setup()` runs after it.
- compression: inert here, the compressor is not built
  (`USE_COMPRESSION(0)`, `USE_MON_COMPRESSION(0)`), so `COMPRESS_EN` does nothing

**CORRECTION 2026-09-08 (later): the reset-domain theory below is WRONG.**

Proven in cosim, not on the board: `CTRL.SOFT_RESET` DOES clear the monitor
configuration registers. `cocotb_test_soft_reset_scope` writes values different
from each register's reset value to `RDMON_PKT_MASK`, `RDMON_ADDR_RANGE2_LOW`
and `MON_GROUP_BASE_ADDR`, pulses SOFT_RESET, and all three come back at their
reset values. Those CSRs are in the `unit_aresetn` domain, not the `presetn`
domain the section below assumes.

So there is no missing reset. A `CTRL.WARM_RESET[5]` bit was implemented to
cover the supposedly-excluded domain, measured to be IDENTICAL to SOFT_RESET on
all three registers, and REVERTED. Do not re-add it.

**Where the bad diagnosis came from, because it is the reusable lesson:** the
board check wrote `MON_GROUP_BASE_ADDR = 0x40000`, pulsed SOFT_RESET, read back
`0x40000` and concluded "config survives". 0x40000 is also that register's RESET
value, so the measurement could not distinguish "survived" from "was reset". Two
successive diagnoses were built on it. The cosim test now asserts up front that
every probe writes a value different from its reset value, so it cannot degrade
the same way.

**Still eliminated, and still unexplained.** Ruled out for the order dependence:
registers (a golden snapshot of all 140 restored before the run changes
nothing), monitor config surviving a reset (it does not), and reset coverage of
the monitors and tallies (u_stream, both observers and both tallies are all on
unit_aresetn). The cause remains unidentified. Next probe should be internal:
instrument reporter grants and monbus group FIFO occupancy in cosim across two
back-to-back scenarios, rather than reasoning from CSR reads.

**Superseded analysis follows.**

**Narrowed 2026-09-08 to the reset DOMAIN, with the register theory falsified.**

Answering the obvious question first -- is there a reset that can be run between
scenarios? Today, no. `CTRL` offers only START, CLEAR_STATS, FREEZE_TRACE,
SOFT_RESET and CAM_CLEAR, and SOFT_RESET is the only reset.

SOFT_RESET is NOT the problem it first looked like: it drives `unit_aresetn` for
16 cycles, and `u_stream`, `u_dma_observer`, `u_slave_observer`, `u_stream_tally`
and `u_slave_tally` are ALL on it. Monitors and tallies do get reset.

What it deliberately excludes is the APB/config domain: `u_stream` is wired
`.aclk(aclk), .aresetn(unit_aresetn), .pclk(aclk), .presetn(aresetn)`. The
register side stays on the global `aresetn` so configuration survives the pulse
-- which is correct and intended. Programming the bitstream asserts that global
`aresetn`, which is exactly why only a reprogram recovers it.

The state is NOT in a register. Measured: a golden snapshot of all 140 CSRs taken
fresh from a program, then the perf scenario, showed 43 registers changed;
restoring every one of them to its golden value before addr_error does not
restore the packets. Separately, every monitor CSR's hardware reset value was
confirmed to match its RDL default exactly (0 mismatches across 86 registers), so
default-restore is faithful and still insufficient.

Conclusion: sequential logic in the `presetn` domain inside `u_stream` (and/or
the monbus group's config/CDC side) carries state across SOFT_RESET that no
register write can clear.

**Two candidate fixes, both RTL:** extend the soft reset to that domain's LOGIC
while leaving the register storage intact, or add a dedicated monitor-reset
control bit alongside CAM_CLEAR in `CTRL` that the campaign can pulse between
scenarios. The second is the smaller change and gives the host the between-run
reset it currently lacks.

**Original finding retained below.**

**The only thing that restores it is REPROGRAMMING THE BITSTREAM.** So the state
that survives is not reachable from any monitor CSR: it is internal monitor state
-- transaction table, monbus group FIFO, reporter arbitration or similar -- that
`SOFT_RESET` does not clear. That is an RTL reset-coverage gap, not a host
programming bug, which is why every host-side attempt failed.

**Why it matters beyond tidiness:** the campaign reports mon at 5/6 classes when
the hardware does 6/6 -- ADDR_RANGE is proven working at 129/122. Any future
"class X is broken" result from this matrix is suspect until a scenario's result
is independent of its predecessors.

**Suggested next step:** in cosim, run two scenarios back to back and diff the
monitor's internal state across the second `SOFT_RESET`. The waved runs from
2026-09-07 (build-mon, 6 FST dumps) already contain sequenced traffic. Then
extend whatever reset the monitor subsystem is missing.

Related: TASK-083 (timeout saturation) is a different defect in the same
subsystem. The owner has monitor simplification planned, which may subsume both.

