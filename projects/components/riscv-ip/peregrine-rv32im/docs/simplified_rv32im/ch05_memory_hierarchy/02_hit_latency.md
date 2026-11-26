# Hit Latency

## The performance model (COD gap G3)

The PRD wrote the model down before the caches existed (§4.8; COD §5.4):

CPI = 1 + (load-use + load-to-branch bubbles) / insn + 2 x mispredicts / insn
+ M stall cycles / insn + memory-stall cycles / insn

Memory-stall cycles / insn = (I\$ miss rate + D\$ accesses / insn x D\$ miss
rate) x miss penalty.

With COD's example inputs (2% I\$ misses, 4% D\$ misses, 0.36 D\$ accesses
per instruction) and a 30-cycle line fill, the miss term is 0.6 + 0.43 =
**1.03 stall cycles per instruction**: the caches' misses alone roughly
double merlin's CPI. The model's largest unknown was the hit time.

## Measured: 4 cycles

Before peregrine was built around amber, the hit time was measured on
amber's own two-cache test rig (TASK-001 stage 6, P13):

| Access | Response valid after accept | Port ready again |
|--------|-----------------------------|------------------|
| Read hit | 4 | 3 |
| Write hit | 4 | 3 |
| Write to a Shared line (upgrade) | 18 | 17 |
| Read or write miss (rig memory) | 29 | 28 |

: amber's CPU-port latency in cycles, before the change (TASK-001 stage 6)

A blocking MEM stage that waits for each response pays about 3 extra
cycles per D\$ access over a 1-cycle hit. At 0.36 accesses per
instruction that is about **1.1 cycles per instruction for hits alone**,
more than the whole miss term. The measured miss (29 cycles) was close
to the 30 assumed.

## The decision: make amber's hit 1 cycle

The owner chose to change amber, not peregrine (P13 option (b)): amber
gained a pipelined hit path (cache-ip/amber-mesi-l1 TASK-005) with a
target of 1 cycle, so a single MEM stage needs no extra stall.

| Access | Before | After |
|--------|--------|-------|
| Read hit (latency / issue interval) | 4 / 3 | 1 / 1 |
| Write hit | 4 / 3 | 1 / 2 |

: amber's hit path, before and after TASK-005

The cycles came back. The bill arrived in the clock period, which is the
next section.
