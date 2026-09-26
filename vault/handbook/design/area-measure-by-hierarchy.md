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
