---
title: Area: measure by hierarchy before you cut
summary: Read the hierarchical utilization and the worst path after every pass; the block you suspect is rarely the block that costs. Five passes of axi_monitor_lite, 2026-09-25.
---

# Area: measure by hierarchy before you cut

**Rule.** When a block misses its gate or timing budget, the next edit is
chosen from two reports and nothing else: `report_utilization
-hierarchical` deep enough to see the sub-blocks, and the worst
register-to-register path. Guessing from the RTL picks the wrong target.

**The case.** `axi_monitor_lite` (amba/monitor-lite TASK-001) was written to be a fifth
of `axi_monitor_base`. It took five synthesis passes on the same bridge
fixture (`projects/components/bridge/fpga/`, minutes each), and every pass
fixed something the previous report named that the RTL did not suggest:

| Pass | Report said | Fix |
|---|---|---|
| 1, -51 ns, 89 levels | a serial running-max loop | tournament tree ([[priority-logic-depth]]) |
| 2, 10,120 LUTs, 38 levels | sixteen 16-bit incrementers and subtractors, one per slot | entries hold **stamps** (copies of shared counters); every subtract done once, after the read mux |
| 3, 6,339 LUTs, 23 levels | attribution, three 8:1 payload muxes, the packet pick, the queue write and a saturating adder in one cycle | register the cycle's events; pick and format from flops; one payload mux serves every class |
| 4, 5,575 LUTs, 12 levels, -0.6 ns | the depth-4 hierarchy report put **346 of the lite's 838 LUTs in a generic skid buffer**; the path ran through the rank tournament into a beats mux | a 4-entry FIFO in an unreset array ([[sram-and-memories]]); per-ID linked lists instead of any age compare; a per-slot 1-bit "last beat expected" flag instead of an 8-bit mux and compare |
| 5, 5,339 LUTs, meets on the lite | worst path now in a shared block | done: 677 LUTs per monitor against 3,249 |

Three of the five fixes contradict a rule of thumb. Sharing arithmetic
after the mux was right at 16 bits and wrong at 8 (pass 5 put an 8-bit
decrement back in every slot so the beat that lands reads one bit). The
generic buffer was the single largest item in the block, and nothing in the
RTL said so. And the "oldest matching" problem that produced the 89-level
chain had no good compare at all: the right answer was a data structure
that never compares.

**Also.** A per-ID linked list (head, tail, next pointer per slot) is the
cheap form of oldest-first attribution whenever the protocol returns
same-ID responses in order, which AXI does. An allocation sequence stamp is
not: it wraps for an entry that outlives 2^W allocations, and the slot
count bounds live entries, not how many come and go while one waits.

## A parameter the subset made inert must not feed a capability register (2026-09-27)

Swapping the observers (`misc/rtl/axi4_intf_{master,slave}_observer.sv`) onto
the lite left `TAP_ENABLE_PERF_LOGIC` / `TAP_ENABLE_DEBUG_LOGIC` declared -- two
consumers bind them -- but inert: the lite builds neither cone. `OBS_CAPS0[5:4]`
still reported the parameters, so the register advertised cones that did not
exist, and the block's own `all_classes` test, which derives its expected
classes FROM that register, waited for packets that can never come: six cells
red, every other class present. The fix was in the hardware, not the test:
the caps bits now read 0 regardless. When a subset makes a parameter inert,
find every register or status word that echoes it and pin it to the truth --
a test that trusts the hardware's self-description is the right test, and it
will be the first thing to catch the lie.

The swap itself: build-obs 184,047 -> 71,671 LUTs (-61%), WNS +1.334 -> +4.154,
per-iteration packet counts unchanged on the five classes the lite emits, DUT
bus meters bit-identical. The full monitor's "timeout saturates at ~7 per reset"
(a timed-out slot went to TRANS_ERROR and leaked) is gone: 55 per iteration.

## Subsetting a block: the "dropped" list comes from the consumers, not the block (2026-09-26)

The lite's "25% dropped" list was written by reading the full monitor and
judging which features were heavy: perf window, debug class, address-range
checker, ID/address filters, latency threshold, per-phase timers, block_ready.
Two of those came straight back the same day, each found only when a consumer
was actually swapped:

- STREAM's data ports are the one user of the **address-range checker** --
  `N_ADDR_RANGES` from the config, ranges from the register block, miss into the
  error enable, match into the debug enable. The swap would have silently
  dropped `Error/ADDR_RANGE` and `AddrMatch` from STREAM's monbus.
- STREAM's packet-class test provokes the threshold class through the
  **latency threshold**, not table occupancy; the lite had only the occupancy
  flavour and the test failed with zero packets on both data monitors.

Before writing a subset's drop list, grep every consumer's INSTANTIATION of
the full block for the ports and parameters that carry each candidate feature
(`grep -rn "cfg_addr_range\|latency_thresh" projects/`). A feature with a
live consumer binding is not a candidate; a feature bound only to `'0` or an
open port everywhere is. The synthesis reports say what a feature costs; only
the consumers say whether it can go. Both features came back as options
(`N_ADDR_RANGES`, default 0) or as a single compare on a value the lite already
had (the latency subtract), so the area case survived -- but a day of
regressions would have been saved by the grep.
