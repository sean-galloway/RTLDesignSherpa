# TASK-037: Lighten the gate-heavy monitor modules

> Migrated 2026-09-27 from `vault/Tasks/amba/open.md` as **TASK-072** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
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
