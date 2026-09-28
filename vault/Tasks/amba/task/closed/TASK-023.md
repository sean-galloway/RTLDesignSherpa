# TASK-023: Split the address-range checker into independent DEBUG and ERROR range sets

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-027** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P3
**Status:** CLOSED 2026-08-31. The goal was achieved by a different and
cheaper mechanism than this task specifies (per-range flavor over ONE comparator
array, not two range-set parameter groups), and the one bullet that looked open
turned out to be a policy decision that is not this repo's to make.
**Owner:** TBD

**READ THIS BEFORE THE WORK LIST BELOW -- the work list is superseded.** The
task asks for two separate range-set parameter groups
(`N_DEBUG_ADDR_RANGES` / `N_ERROR_ADDR_RANGES` with their own cfg ports). The
RTL solved the same problem a different and cheaper way: a PER-RANGE FLAVOR
selector, `ADDR_RANGE_IS_ERROR[i]`, over ONE comparator array.

    0 = DEBUG range -> a hit emits AddrMatch  (gated by cfg_debug_enable)
    1 = ERROR range -> enabled ERROR ranges form an allowlist; an address in
                       NONE of them emits Error/ADDR_RANGE (cfg_error_enable)

The decoupling this task wanted is present: debug and error sets are
evaluated independently, and one command can hit a debug range (MATCH) while
falling outside every error range (MISS) -- two pending slots hold both and
the output serialises them. One comparator array instead of two is strictly
better than the requested shape, so this is NOT to be "fixed" back.

Already done, measured:
* `axi_monitor_addr_check.sv` -- flavor split implemented.
* Threaded to the wrapper level: `axi4_slave_rd_mon` (and siblings) carry
  `N_ADDR_RANGES` + `ADDR_RANGE_IS_ERROR` params and the
  `cfg_addr_range_{enable,low,high}` ports.
* `val/amba/test_axi_monitor_addr_check.py` covers the flavor split.
* `formal/amba/axi_monitor_addr_check/` covers it.

**What is actually left, and it is NOT the bullet as written.** The remaining
work list item asks for "default range values as module params at the AXI*
wrapper level ... so a consumer can set the allowlists purely by param".

**REJECTED 2026-08-30, with reason.** Implementing that literally is a
REGRESSION, not a completion:

* `cfg_addr_range_{enable,low,high}` are input PORTS and are sampled
  combinationally on each accepted command (`cmd_fire`). There is no stored
  range state, so the ranges are ALREADY runtime-changeable: a write lands on
  the next command, with no flush, no reprogramming hazard and nothing to
  invalidate.
* Setting them "purely by param" makes the allowlist static at elaboration
  and DESTROYS that. The requirement is the opposite of what the task asks
  for -- the addresses need to change over time.
* `N_ADDR_RANGES` is already a per-wrapper parameter, so every consumer picks
  its own count (wrappers default to 0 = checker off). A param array of
  default VALUES would therefore be sized per-N and meaningless to any other
  consumer, while still losing runtime updates.

**The actual gap is that NOTHING DRIVES THE PORTS.** Every `cfg_addr_range_*`
in the tree is pass-through plumbing (the twelve wrappers, the `_cg` variants,
`apb5_monitor`). The ranges are runtime-capable and currently unreachable.

**BUT `obs_regs` IS NOT THE BLOCK. Rejected 2026-08-31 (Sean): "the stream
observer doesn't check addresses, only BW and latency."** An earlier version
of this entry named `obs_regs.rdl` as the place to add the fields. That was
wrong on the block's own terms, independent of any tooling problem: the
observer is a MEASUREMENT block -- bandwidth, latency, occupancy -- and
address-range violation checking is not its job. It is also the block whose
measurement-only character is what makes the Genesys2 8-channel design close
timing, so it is the last place to spend comparators.

An implementation against `obs_regs` was written and REVERTED the same day. It
is worth recording why it was a bad idea twice over:

* **On the merits (the reason that matters):** wrong block, per above.
* **On the mechanics:** adding nine registers grew the generated regblock from
  `'h88` to `'hb4`, which pushed `obs_regs_top` past Verilator's inlining
  threshold. Un-inlined, Verilator failed to unify the
  `obs_regs_top__out_t` typedef across the two observer instances and emitted
  the struct PORT as `VL_OUT8(hwif_out,0,0)` -- one bit -- breaking C++ codegen
  for the Genesys2 harness build. `verilator --lint-only` passes CLEAN through
  all of this; only the C++ compile fails, so **a lint gate cannot catch this
  class.** Proven by building the harness closure at both regblock sizes.
  **CORRECTED 2026-08-31:** an earlier version of this entry claimed a
  pre-existing structural Verilator typedef bug underneath this. There is
  none. That conclusion came from a repro that passed a raw `-f` filelist to
  verilator, which double-compiles the shared packages (these filelists
  self-duplicate -- `amba_all.f` is 322 redundant of 700) and so mints two C++
  types for one typedef, with `-Wno-fatal` then papering over the errors.
  Resolved properly through `get_sources_from_filelist()`, the same closure at
  `'h88` verilates AND compiles with ZERO errors. See
  [[generated-rtl-discipline]]. Do not leave "Verilator won't allow it" in the
  record as a reason to reject this feature -- the reason is the block, above.

**THERE IS NO REMAINING WORK. Closed 2026-08-31 (Sean): "the monitors own
coding the address ranges, how they are defined is up to the customer."**

That resolves the question this entry had been circling. The MONITOR owns the
mechanism -- comparing an accepted command's address against N inclusive
`[low, high]` windows, the per-range DEBUG/ERROR flavor, and the packet
encoding. WHERE the range values come from is the integrator's choice, and
deliberately not this repo's: a customer wires `cfg_addr_range_{enable,low,
high}` to whatever register block, fabric CSR or tie-off their system already
has. That is why the ports are ports.

So "nothing drives the ports" was never a defect. It is the correct state for
a library block: the mechanism is complete and the policy is left open. The
earlier framing -- find a block, add RDL fields, wire it -- was inventing a
policy decision that belongs to the consumer, and the obs_regs attempt was
that mistake made concrete.

Everything the monitor side owes is done and verified:

* the checker, with the per-range flavor split (`axi_monitor_addr_check`);
* the ports exposed on all twelve `*_mon` wrappers AND, since 2026-08-31, on
  the twelve `*_mon_cg` clock-gated wrappers that had been missed (`ef019f1f`);
* `axi_monitor_addr_check.sv` present in all 24 filelists so a consumer setting
  `N_ADDR_RANGES > 0` can actually build it (`8cb0d5fc`) -- it was in 2 of 24;
* cocotb coverage of the flavor split, and a formal proof that now covers
  payload stability and passes its cover task (`8f1fc3e4`).

An integrator with a register block wires the ports to it. That is the whole
contract.

**Hard ceiling: 16 ranges.** The packet carries the matching range index in
`event_data[63:60]` -- 4 bits. Past 16 the index field has to be widened by
chopping address payload bits. Range 15 is SAFE despite
`MISS_RANGE_SENTINEL = 4'hF`: a MISS is `PktTypeError` and a MATCH is
`PktTypeAddrMatch`, so a decoder separates them on packet_type, not on the
index. Do not "fix" that collision -- it is not one.

**Do not confuse the two features' reprogramming behaviour:**
* the CHECKER (this task) re-evaluates per command, so a window change
  applies immediately to every command after it;
* the FILTER ([[TASK-015]]) latches its verdict at ALLOCATION and holds it
  for the slot's life, so widening the window mid-flight does not un-filter
  entries already in the table. That asymmetry is deliberate: it is what
  makes the filter safe to reprogram live, because an entry's fate is decided
  when it is admitted and the retire accounting cannot be corrupted
  afterwards.

Everything else in the work list below is done or superseded.

The integration bullet is also stale: `dma_slave_monitors.sv` was DELETED
(2881006b). The remaining tie-offs are in `stream_core.sv` and
`scheduler_group_array.sv`, which are project code, not monitor code.

**Context — what shipped first.** `axi_monitor_addr_check` was reworked from a
single-polarity violation checker into an ALLOWLIST checker with two report
paths off **one shared** range set (`cfg_addr_range_low/high/enable`,
`N_ADDR_RANGES`):
- MATCH (addr in a range), gated by `cfg_debug_enable` → `PktTypeAddrMatch (8)` /
  `AXI_ADDR_RANGE_MATCH (0x01)`.
- MISS  (addr in NO range), gated by `cfg_error_enable` → `PktTypeError (0)` /
  `AXI_ERR_ADDR_RANGE (0x0D)`.

Landed + verified: cocotb `test_axi_monitor_addr_check.py` and formal
`formal/amba/axi_monitor_addr_check/` (prove + cover PASS). Wired
`cfg_debug_enable`/`cfg_error_enable` into the `addr_check` instance in
`axi_monitor_base`. **Still tied off** in `dma_slave_monitors.sv` and the STREAM
in-core monitors (`stream_core.sv`, `scheduler_group_array.sv`) — see the
`cfg_addr_*` `1'b0` ties there.

**The evolution requested.** One shared range set couples the two paths (debug
watches exactly the addresses whose *absence* raises an error). Decouple them
into **two independent range sets** so the debug allowlist and the error
allowlist can differ:
- **Debug/match ranges** — their own params + cfg ports; a hit in a DEBUG range
  emits the `AddrMatch` packet.
- **Error ranges** — their own params + cfg ports; an address matching NONE of
  the ERROR ranges emits the `Error`/`ADDR_RANGE` packet.

**Where the params live (per the request): at the monitor core AND the AXI\*
wrapper module level** — threaded the same way `N_ADDR_RANGES` already is, so a
top consumer sets them on `axi4_slave_rd_mon` / `axi4_slave_wr_mon` /
`axi4_master_*_mon` and they flow down through `axi_monitor_filtered` →
`axi_monitor_base` → `axi_monitor_addr_check`.

**Work:**
- [ ] `axi_monitor_addr_check.sv`: replace the single range set with
      `N_DEBUG_ADDR_RANGES` / `N_ERROR_ADDR_RANGES` params + separate
      `cfg_debug_addr_range_{low,high,enable}` and
      `cfg_error_addr_range_{low,high,enable}`. MATCH decision uses the debug
      set; MISS decision uses the error set. Keep the master
      `cfg_addr_check_enable` and the `cfg_debug_enable`/`cfg_error_enable`
      path gates.
- [ ] Thread the two param groups + cfg ports through `axi_monitor_base` →
      `axi_monitor_filtered` → the `axi4_*_mon` wrappers (module-level params
      with sane defaults, e.g. debug set = match-all, error set = match-all so
      the default emits no error).
- [ ] Add **default range values as module params** at the AXI\* wrapper level
      so a consumer can set the allowlists purely by param.
- [ ] Update `val/amba/test_axi_monitor_addr_check.py` for the two range sets
      (drive debug vs error ranges independently; assert a debug-only hit, an
      error-only miss, and an address that is in the debug set but also a valid
      error address).
- [ ] Update `formal/amba/axi_monitor_addr_check/` (anyconst two range sets;
      MATCH membership vs the debug set, MISS non-membership vs the error set).
- [ ] Integration: expose the two range param groups on `dma_slave_monitors.sv`
      and enable them in the STREAM monitor-validation harness; retire the
      `cfg_addr_*` `1'b0` ties in `dma_slave_monitors.sv` /
      `stream_core.sv` / `scheduler_group_array.sv`.

**Related:** TASK-015 (address-range + ID *filtering* to cut traffic) — different
goal (drop mask) but same comparator neighborhood; fold in if done together.

---

---

---
