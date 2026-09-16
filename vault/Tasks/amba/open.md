<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# AMBA tasks — open (not started)

## TASK-077: four instantiation examples in components docs name ports that do not exist

**Priority:** P3. A reader copies the example and it does not compile.
**Status:** open 2026-09-02, reduced from 5 pages to 4 findings. Two fixed:
`pumice_top` (`.BL` -> `.DRAM_BL`, the real parameter) and most of
`rapids_core_beats` (12 names remapped: `apb_*` -> `src_apb_*`,
`cfg_channel_enable` -> `src_cfg_channel_enable`, `desc_m_axi_ar*` ->
`src_m_axi_desc_ar*`, `all_channels_idle` -> `src_system_idle`, and
`ENABLE_AXIS_WRAPPERS` removed -- no such parameter).

**What is left, and why I stopped:**

| Page | Module | Names | Why not fixed |
|---|---|---|---|
| `stream_mas/ch01_overview/03_clocks_and_reset.md` | `apb4_slave_cdc` | `SYNC_STAGES`, `m_paddr`, `m_pclk`, `m_prdata`, `m_presetn` | needs the stream owner: the real APB master-side names differ and the example may be describing a different wrapper |
| same | `clock_gate_ctrl` | `enable` | trivial but same page |
| same | `scheduler` | `aclk`, `aresetn` | `scheduler` uses `clk`/`rst_n`; confirm which module the page means |
| `rapids_beats_mas/ch03_macro_blocks/11_rapids_core_beats.md` | `rapids_core_beats` | `monbus_pkt_*`, `snk_fill_*` | **the module has NO monbus or fill ports at all** -- these belong to a different module, probably `rapids_beats_top`. Cannot be remapped without knowing which. |

**Method.** Get ground truth from the AST, never a regex over source:

    python3 bin/rtl_ast.py <module.sv> rtl/amba/includes rtl/common

Fix names in place. Do NOT regenerate the block: several of these contain more
than one instantiation and a whole-block rewrite silently drops the others.

`bin/check_doc_examples.py` ratchets at 9, so the count cannot grow.

**Measure the baseline at HEAD, not in the working tree.** I first set it to 4,
which is what my dirty tree showed -- other sessions had uncommitted fixes for
pages I had not touched. CI, which sees only HEAD, failed at 9. Use:

    git worktree add --detach /tmp/chk HEAD && cd /tmp/chk && python3 bin/check_doc_examples.py

The extra findings at HEAD are in `stream_mas/ch01_overview/02_port_list.md`,
`stream_mas/ch02_blocks/08_sram_controller.md`,
`rapids_beats_mas/ch04_interfaces/03_monbus_interface_spec.md` and
`pit_8254_mas/ch03_interfaces/01_top_level.md`; some already have fixes in
flight from their owners, so the number should fall on its own.

## TASK-074: test_axis4_slave dies with SystemExit under heavy parallel load

**Priority:** P3 — intermittent, and the cocotb test itself PASSES every time.
What fails is the pytest wrapper, so this costs a red suite rather than hiding
a functional defect.
**Status:** open 2026-09-02. Found while validating the clock-gating activity
term fix; NOT caused by it (see below).
Re-diagnosed 2026-09-15: seed-dependent, reproduces STANDALONE, confined to
skid depth 8. The load/ccache framing below is falsified -- read the next
block, not the original analysis.
RESOLVED 2026-09-15 (same day): it is GENUINE PACKET LOSS, measured. The P3
rationale is void -- see the top block.

**PACKET LOSS CONFIRMED 2026-09-15. This entry's whole premise -- "the cocotb
test itself PASSES ... this costs a red suite rather than hiding a functional
defect" -- is now false in both halves.** Instrumented
`bin/TBClasses/axis4/axis_slave_tb.py` to log PACKET counts (not just the
`*_transactions` fields) and re-ran the failing seed against a passing one:

| | fub_slave packets | axis_mon packets | fub_mon packets | sent |
|---|---|---|---|---|
| SEED=28162 (fails) | **8** | 10 | 8 | 10 |
| SEED=42 (passes) | 10 | 10 | 10 | 10 |

`packets_received` on the FUB SLAVE -- the receiving BFM, not an observer -- is
8. Ten packets enter at the AXIS input and eight arrive. This is not monitor
timing and not a counting artifact: two packets are LOST.

**Why it very nearly went unnoticed, and the reusable lesson.** Two independent
guards were both incapable of seeing it:

1. `assert received_packets >= num_packets` compared `received_transactions`
   -- which runs **2x** the packet count on this component -- against a PACKET
   count. It read `16 >= 10` and passed while only 8 packets had arrived. A
   UNIT MISMATCH made the packet-loss guard structurally unable to fire.
2. `min_expected_fub = num_packets - 1` for skid depth > 4 absorbed one of the
   two lost packets as "skid buffer depth effects on monitor timing".

So the only assertion that fired was the -1-tolerance one, pointing at the
monitor, which is why this read as a harness/monitor problem for two weeks.
**When a guard compares two counts, check they are the same UNIT.**

**Fixed in the TB (behaviour-neutral on passing runs, verified: all 14 param
sets pass at SEED=42):**
- the guard now compares packets to packets and names both numbers;
- `run_basic_transfer_test` logs a `[counts]` line with packet AND transaction
  counts side by side;
- the verification block is wrapped in try/finally so a FAILING run dumps the
  component Stats. Until now the assert aborted before
  `generate_final_report()` ever ran, so **a failing run produced ZERO Stats
  blocks and was undiagnosable from its own log** -- which is why the first
  attempt to settle this had to re-run the test to get any numbers at all.

**One LIMITATION of that fix, recorded so nobody trusts it further than it
goes.** The BFM stat counters are CUMULATIVE across calls on a single TB
instance -- they are never reset between phases. So `fub_pkts >= num_packets`
only bites on the FIRST call in a TB's life; on any later call the count has
already grown past the threshold and the guard can no longer fail, even if that
call loses packets. Measured in `test_axis4_slave_cg`, which calls the method
repeatedly on one instance:

    [counts] packets: fub_slave=5  ... | sent=5
    [counts] packets: fub_slave=10 ... | sent=5     <-- 10 received, 5 sent

The pre-existing guard had exactly the same property, so this is not a
regression -- but a CORRECT version would snapshot the counts before each phase
and compare DELTAS. Not done here: that changes the accounting for every
consumer of this shared TB (`AXISSlaveCGTB` subclasses it) and is a larger
change than settling this entry required.

**STILL OPEN: where the two packets go.** Not yet root-caused, and the entry
stays open for it. Unknown whether the loss is in `axis4_slave.sv` or in the
AXIS BFM, and only skid depth 8 reproduces (SEED=28162 across all 14 params:
1 failed, 13 passed, the sole failure being the only sd8 set). Next step is a
waveform on the failing seed: `WAVES=1 SEED=28162 pytest
val/amba/test_axis4_slave.py -k "8-32-8-4-1"`, and compare fub_axis handshakes
against s_axis.

**Priority should be re-read as a real defect, not a red-suite nuisance.**

**FALSIFIED AND REPRODUCED DETERMINISTICALLY 2026-09-15. Almost everything
below this block is wrong, and the "heavy parallel load" framing sent the
investigation at ccache when the failure is seed-dependent and reproduces
standalone in eight seconds.**

    SEED=28162 pytest val/amba/test_axis4_slave.py -k "8-32-8-4-1"

Single test, no parallel load, 13 other params deselected. Fails 2/2. Seeds
1, 7, 42, 999 and 12345 all pass, so it is DETERMINISTIC PER SEED and rare
across the seed space -- not intermittent.

| this page claims | measured |
|---|---|
| "the cocotb test itself PASSES every time" | the cocotb test FAILS: `assert 8 >= 9` |
| "Not the RTL ... the simulation succeeds; the wrapper exits" | sim reports FAIL at 1500.10ns, 4/4 attempts |
| "dies under heavy parallel load", "load-sensitive" | reproduces standalone, zero load |
| "A DIFFERENT parameter set each time" | the wrapper re-rolls the seed each run |
| "look at ccache / Verilator artifact contention" | wrong layer entirely |

**Why it looked load-sensitive.** `val/amba/test_axis4_slave.py` lines 214/339
set `'SEED': os.environ.get('SEED', str(random.randint(0, 100000)))`, so every
regression run rolls a NEW seed. A different seed exposes a different parameter
set, which reads as "a different one each time under load". Within one run the
seed is fixed, which is why all four attempts (initial + 3 reruns) failed
identically rather than flickering. The observed rate across three full val/amba
runs was 1 in 3.

**The real failure, and it is CONFINED TO SKID DEPTH 8.** With SEED=28162 across
all 14 parameter sets: 1 failed, 13 passed, and the only failure is
`[8-32-8-4-1]` -- the sole set with skid depth 8. Every sd4 and sd2 set passes
on the identical seed. `axis_slave_tb.py:250` already grants deep-skid builds a
tolerance for exactly this:

    min_expected_fub = max(1, num_packets - 1) if self.TEST_SKID_DEPTH > 4 else num_packets

with the comment "Allow for skid buffer depth effects on monitor timing".
So the TB already KNOWS the FUB monitor under-counts at deep skid and papers
over it with -1; this seed makes it under-count by 2. Same class as the axil4
monitor TB drain-window race.

**SUPERSEDED -- this WAS settled the same day; see the packet-loss block at
the top of this entry.** Whether
those two packets physically reached the FUB output is still open:

    FUB slave received 16    (received_transactions)
    AXIS monitor observed 10 (input side -- all 10 arrive)
    FUB monitor observed 8   (output side)

In a PASSING run the slave reports `packets_received: 10` alongside
`received_transactions: 20`, i.e. that field runs 2x the packet count -- so 16
implies 8 packets, agreeing with the FUB monitor. Two FUB-side components say 8
while the input says 10. But the 2x relation is INFERRED from one passing run,
not measured here, and it cannot be measured from a failing run: the assert at
line 251 aborts BEFORE the `log.info(... Stats ...)` calls, so a failing log
contains zero Stats blocks. Note also that the guard at line 246
(`received_packets >= num_packets`) compares `received_transactions` against a
PACKET count -- 16 >= 10 passes on a unit mismatch, so it is not evidence that
all 10 arrived.

To settle it, log the Stats before the asserts (or catch and re-raise) and read
`packets_received` directly on the failing seed.

**Priority should be re-read.** The P3 rationale was "the cocotb test itself
PASSES ... this costs a red suite rather than hiding a functional defect". The
cocotb test does not pass, so that rationale no longer holds as written. It is
still most likely a monitor-timing artifact rather than data loss, but that is
now an open question rather than an established premise.

**The rerun flag this page forbids IS in place:** `make/tests.mk:70` sets
`PYTEST_RERUNS ?= --reruns 3 --reruns-delay 1`. It masked nothing here (the
failure is deterministic within a run and lost 4/4), but it is there, contrary
to the instruction below.

**Method note worth keeping:** re-running the failure overwrote its log with a
passing seed's, and the passing log's numbers were briefly mistaken for the
failing ones. Copy a failing log aside BEFORE re-running anything.

**Superseded analysis follows.**

**What happens.** In a 16-worker run of
`test_mon_cg_gating + test_axil4_* + test_axil5_* + test_axis* +
test_axil_perf_byte_count`, exactly one `test_axis4_slave` parameter set fails
with `SystemExit`. Measured 4 runs: 2 failed, 2 clean (314 passed).

    run 1: FAILED test_axis4_slave[4-64-8-4-1]   313 passed
    run 2: FAILED test_axis4_slave[8-32-8-4-1]   313 passed
    run 3: clean, 314 passed
    run 4: clean, 314 passed

**A DIFFERENT parameter set each time**, so it is load-sensitive, not a bad
case.

**What it is not.**
- Not the RTL: the cocotb test reports `TESTS=1 PASS=1 FAIL=0` in the same run
  that pytest marks failed. The simulation succeeds; the wrapper exits.
- Not the 2026-09-02 gating change: the failing DUT is `axis4_slave`, and
  `rtl/amba/filelists/axis4_slave.f` does not reference `axis4_slave_cg.sv` at
  all. The edited file is not in that build.
- Not a sim_build collision between workers: `test_name_plus_params` includes
  `worker_id`, so each case owns its directory.
- Not the TB safety monitor: `_check_cpu_usage` only warns, and
  `_check_memory_usage` raises `MemoryLimitExceeded`, not `SystemExit`.
- Not axis in isolation: `test_axis*.py -n 16` alone is 58/58 clean,
  repeatedly. It needs the heavier mixed load.

**Where to look next.** `SystemExit` from `cocotb_test.simulator.run` is what a
failed BUILD raises. Under 16 concurrent Verilator invocations the likely
mechanism is ccache or Verilator artifact contention — the same class as
PUMICE-019 ("concurrent Verilator/ccache compiles destroy each other's
artifacts"), but that one was diagnosed for a SHARED sim_build and this one
has per-worker directories, so the shared resource is something else (ccache
itself is the obvious candidate). Capture the failing worker's build log:
`--tb=long` did not surface the message, so the runner is swallowing it.

**Do not paper over it with a rerun flag.** An intermittent failure is a real
bug in the runner, the harness or the RTL ([[feedback_no_flaky_dismissal]]);
`--reruns` would hide the one signal we have.


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
**Status:** 🔴 Not Started
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
**Status:** 🔴 Not Started
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
**Status:** 🔴 Not Started (stub created 2026-05-29)
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

**Related:** [[TASK-077]] documents the doc-side equivalent (examples that
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

## TASK-095: axi_split_combi's next-boundary arithmetic overflows in the top alignment window

**Priority:** P3. A latent hazard the design DOCUMENTS as out of scope, found
while proving TASK-094. Not a regression, and no in-tree RTL instantiates the
splitter today.

**Status:** open 2026-09-12, found by formal.

`axi_split_combi` computes the next boundary in AW bits:

```systemverilog
assign next_boundary_addr = (current_addr | AW'(alignment_mask)) + AW'(1);
assign crosses_boundary   = (transaction_end_addr >= next_boundary_addr);
```

For any transaction in the FINAL alignment window of the address space that
`+1` overflows to zero, and `crosses_boundary` then compares against 0 and
reads TRUE. A transaction that crosses nothing is split anyway.

**Counterexample** (from the rd splitter proof, AW=16, mask 0xFFF): a
ONE-BEAT read at `0xFFFC`. `next_boundary_addr` = `(0xFFFC | 0xFFF) + 1` =
`0x10000` -> `0x0000`; `0xFFFF >= 0x0000` is true; `split_required` asserts;
`split_len` = 0 and `remaining_len_after_split` = 0, so the FSM issues a
first split of one beat AND a second of one beat. Two downstream beats for a
one-beat original -- the extra beat arrives upstream with nothing owed, which
is how the rd splitter proof first surfaced it.

Note the transaction itself does NOT wrap here: `0xFFFC + 4` ends exactly at
the top of the space. The BOUNDARY arithmetic overflows before the
transaction does, so "the transaction does not wrap" is not a sufficient
guard -- the first constraint tried in the harness was exactly that, and the
solver walked straight back in.

**Why it is filed rather than fixed.** The module header states it as a
design assumption: "Assumption 4: No Address Wraparound ... No wraparound
handling in boundary crossing logic ... Real systems never allow this
condition due to memory layout and software design." Changing boundary math
the design explicitly excludes is a separate decision from TASK-094, which
was about acceptance timing. `formal/amba/axi_master_rd_splitter` now assumes
the next boundary exists inside the address space, which holds the proof to
the design's stated operating range and is commented as such.

**If it is fixed:** compare in AW+1 bits (or detect the overflow and treat
the window as non-crossing), then drop that harness assumption and re-prove
both splitters -- the write splitter shares `axi_split_combi` and has the
same exposure.
