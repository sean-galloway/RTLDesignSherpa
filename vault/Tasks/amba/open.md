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

## TASK-075: one module has no test coverage (was seven -- five of those claims were wrong)

**Priority:** P3.
**Status:** open 2026-09-02, corrected. qc round_38 disputed my "no coverage"
claim on the ECC pair and was RIGHT.

**What I got wrong.** I searched for `val/**/test_<module>.py` and for parents
in the RTL instantiation graph. Neither finds a test that names the module in a
Python string and builds its own wrapper. Re-checked by searching test SOURCES
for each module name:

| Module | Actually covered by |
|---|---|
| `dataint_ecc_hamming_encode_secded` | `test_dataint_ecc_hamming_secded.py` -- builds `ecc_secded_wrapper` around encoder+decoder, 5 tests |
| `dataint_ecc_hamming_decode_secded` | same |
| `sdpram_slave_axi4_axi4` | `test_sdpram_slave.py` |
| `axis4_master_pattern_gen` | `test_axis4_pattern_pair.py` |
| `axis4_slave_pattern_check` | same |

Both ECC modules were the P2 items in the original filing. They were covered
all along, and five of the seven pages carried a false "no test coverage"
warning that I put there. All five corrected.

**Fixed while checking:** `apb4_master_cg` had no coverage, and the reason was
that it had **no filelist** -- nothing could build it. Created
`rtl/amba/filelists/apb4_master_cg.f` and added it to
`val/amba/test_cg_peer_ready.py`, which needed per-DUT clock names because the
APB family uses `pclk`/`presetn` rather than `aclk`/`aresetn`. It now passes
both gating assertions.

**Genuinely uncovered, still open:**

| Module | Note |
|---|---|
| `monbus_axi4_axi4_group` | No test names it and no filelist-reachable parent has one. The axil/axil variant IS tested, so the gap is this variant only. |

**Method for next time:** a module is covered if any file under `val/` names
it, not merely if `test_<module>.py` exists. Tests that synthesise a wrapper
are invisible to the filename convention.

## TASK-074: test_axis4_slave dies with SystemExit under heavy parallel load

**Priority:** P3 — intermittent, and the cocotb test itself PASSES every time.
What fails is the pytest wrapper, so this costs a red suite rather than hiding
a functional defect.
**Status:** open 2026-09-02. Found while validating the clock-gating activity
term fix; NOT caused by it (see below).

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


## TASK-073: write monitors ID-filter W beats against the LIVE AWID

**Priority:** P2 — latent, but reachable at RUNTIME on any shipped build, and
the failure is a false error report rather than a missed one.
**Status:** open 2026-09-01. Found as a passing observation in qc round_30
(axi4_part_02), verified against the RTL, not yet fixed. Filed rather than
fixed because the fix is in `axi_monitor_base`, which is shared by the whole
family — scope call belongs to Sean ([[feedback_confirm_scope_shared_rtl]]).

**What the RTL does.** `axi_monitor_base` filters each channel's valid by the
ID window:

    assign w_cmd_valid_f  = cmd_valid  && id_owned(cmd_id);
    assign w_data_valid_f = data_valid && id_owned(data_id);
    assign w_resp_valid_f = resp_valid && id_owned(resp_id);

On READ monitors `data_id` is `RID` — the beat's own ID, correct. On the four
AXI4/AXI5 WRITE monitors it is the LIVE `AWID`:

| module | `.data_id` |
|---|---|
| `axi4_master_wr_mon` | `m_axi_awid` |
| `axi4_slave_wr_mon` | `s_axi_awid` |
| `axi5_master_wr_mon` | `m_axi_awid` |
| `axi5_slave_wr_mon` | `fub_axi_awid` |
| `axil4_*_wr_mon` | `1'b0` — correct, AXI4-Lite has no IDs |

AXI4 dropped WID, so a W beat carries no ID and the monitor cannot derive one
from the W channel. Sampling whatever AW happens to be presenting is not a
substitute: with more than one outstanding write, the AW on the bus belongs to
a LATER transaction than the W beats in flight.

**Failure scenario.** Runtime filter on, `cfg_id_match_base=0`,
`cfg_id_match_count=1` (own ID 0). AW id=0 is accepted and allocates an entry;
AW id=1 follows and is filtered out, correctly. While the W beats for
transaction 0 stream, `AWID` reads 1, so `id_owned(1)` is false,
`w_data_valid_f` drops, and NONE of transaction 0's W beats reach
`axi_monitor_trans_mgr`. Its data phase never completes: the entry holds a CAM
slot until `EVT_DATA_TIMEOUT` fires and reports a timeout on a transaction
that was healthy the whole time. The mirror case admits a beat for a
transaction the filter was supposed to exclude.

**Why it is reachable.** `id_owned` activates on `cfg_id_filter_enable` ALONE
— the `ID_FILTER_ENABLE` parameter is only the fallback branch — so this is a
CSR write away on any existing bitstream, not a synthesis-time choice. It is
inert today only because the runtime bit ships low.

**Proposed fix (needs the scope call).** Do not ID-filter the write data
channel at all: pass `w_data_valid_f = data_valid` when `!IS_READ`. The
justification is that the filter's job is already done upstream — an entry
exists only if its AW passed `id_owned(cmd_id)`, so a W beat can only be
attributed to an owned transaction, and gating the beat by a fabricated ID
can only ever drop beats belonging to owned transactions. The alternative
(carry the allocating entry's ID down the ordering queue and filter on that)
is more machinery for the same answer.

**Verify like a bug, not like a change.** The regression must fail against the
current RTL: two outstanding writes with different IDs, the runtime filter
owning only the first, asserting no `EVT_DATA_TIMEOUT` and a completed entry.
Revert the fix, confirm RED, restore ([[kimi-review-rounds]] rule 8).

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

**Status:** open 2026-09-07. Scoped only, deliberately not fixed.

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

**Done when:** a monitors-on campaign drives timeout packets into the same
order of magnitude as the other classes from the same traffic, and
`host_obs_matrix.py` clears its 1000-packet floor on 7/7 instead of 6/7.

## TASK-084: SOFT_RESET does not fully reset the monitor subsystem

**Priority:** P2. It makes the board campaign order-dependent, so a packet class
can read as broken purely because of what ran before it.

**Status:** open 2026-09-08. Diagnosed to the boundary; NOT fixed.

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
