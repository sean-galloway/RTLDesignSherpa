# TASK-001: monitor-lite -- three quarters of the AXI monitor for a fifth of the gates
**Status:** active (2026-09-25) -- built the same day the review was filed (Sean: "create a monitor-lite area please, follow all of your recommendations").
**Was:** open 2026-09-25 (Sean: "review `rtl/amba/monitor` with the eye of
making a new version of some or all to get 75% of the functionality with ~20%
of the gates; the solution space runs from a simpler `axi_monitor_trans_mgr`
to a new `monitor-lite` directory built for gate count and timing")
**Priority:** P2
**Owner:** TBD
**Was:** the legacy amba lane's TASK-098 (filed and committed there 2026-09-25 before this sub-area existed; re-filed here the same day at Sean's request, closed there with a pointer).
**Related:** amba TASK-072 (trim the existing family; area not speed),
amba TASK-014 (per-monitor area, never measured until now), amba TASK-083,
amba TASK-084.

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
  (threshold cone off), the channel field. amba TASK-072 item 1 (delete the
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

`rtl/amba/monitor/axi_monitor_lite.sv` (+ `_pkg` reuse from
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
| A | Trim the existing family (amba TASK-072: dead timers, narrower timestamps, addr) | -5..-10% on FPGA (already pruned) | No. Right for the RTL, not for this ask |
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
oldest-first attribution. Formal: one harness, `formal/amba/axi_monitor_lite`,
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
- **ID width.** The per-ID linked-list attribution is exact for any IW;
  the table depth is the only capacity knob, and refusing an allocation is
  a counted event, never a mis-attribution.

### Definition of done

`rtl/amba/monitor/axi_monitor_lite.sv` with filelist, `docs/markdown/rtl-amba/monitor/`
pages, the wrapper parameter, the bridge preset, the contract tests green at
gate/func/full, the formal harness non-vacuous, and the synthesis row that
shows the number. Then the observers and STREAM decide per instance.

### 8. Built and measured (2026-09-25)

Five synthesis passes in one day, each on `bridge_1x2_rd_lite_mon`
(Artix-7 100T -1 at 10 ns), each fixing what the previous report named:

| Pass | Change | Bridge LUTs | WNS | Levels | What the report said |
|---|---|---:|---:|---:|---|
| 1 | first RTL, 16 slots | -- | -51.6 ns | 89 | a running-max loop for "oldest matching" ([[priority-logic-depth]]) |
| 2 | tournament tree | 10,120 | -16.7 ns | 38 | a 16-bit incrementer, 16-bit subtractor and 8-bit decrementer in every slot |
| 3 | stamps only, arithmetic shared after the read mux; 8 slots | 6,339 | -6.6 ns | 23 | attribution, 8:1 payload muxes, packet pick, skid write and drop adder in one cycle; sequence stamps wrap |
| 4 | dense ranks; events registered before the pick; one payload mux; 66-bit entry | 5,575 | -0.6 ns | 12 | rank tournament into the beats mux; the generic skid buffer was 346 of the lite's 838 LUTs |
| 5 | per-ID linked lists (head/tail/next); per-slot beat flag; 4-entry unreset queue | 5,339 | -0.16 ns (not in the lite) | 16 (not in the lite) | done |

Result, per read monitor in the same fixture: **677 LUTs / 831 FFs against
3,249 / 1,628** (21% / 51%). Kintex-7 325T -2 at 6.667 ns: +1.09 ns.
The lite bridge's remaining -0.16 ns is the `s1_beats_to_limit` CARRY4
chain in `monbus_axil4_axil4_group`, shared with every monitored bridge and
filed separately; no `axi_monitor_lite` path is among the twenty worst.

Verification as built: `val/amba/monitor-lite/test_axi_monitor_lite.py` 8/8 at full
(read and write, id widths 4 and 8, 4 and 16 slots) through the real
`axi4_slave_{rd,wr}_mon` wrappers with `MONITOR_LITE=1`;
`formal/amba/axi_monitor_lite` prove PASS (count bounded, clear empties,
output hold) and all five covers reached; the 16 wrappers' own regression
112/112 at full on the default path; bridge lint 55/55; the bridge suite at
full on the regenerated fixtures (the `lite` preset now sizes the table at
the lite's default of 8).

Not done from section 6's contract, deliberately: the inherited monitor
suites (`test_axi4_monitor`, soak, runtime-disable, pktgen) were not re-run
with `MONITOR_LITE=1` -- they assert on perf/debug/addr-check packets the
lite does not emit and on `block_ready`, and would need per-class skips
first: that is amba/monitor-lite TASK-002. The lite's own suite covers the
four classes it emits, the drop count and the refused count. The observers
and STREAM have not been switched; that is per-instance and theirs to
decide: amba/monitor-lite ISSUE-001.

The lite has its own test area, `val/amba/monitor-lite/` (own Makefile on
make/tests.mk, own conftest), and its own TB package,
`bin/TBClasses/amba/monitor_lite/`, wired into `val/Makefile` AREAS and the
root gate/func/full targets (Sean, 2026-09-25).

