# The Timing Story

## The target and the first measurement

The PRD's target was 100 MHz (10 ns) on the Nexys A7's xc7a100t-1
(P14). The first out-of-context build of the whole system
(`peregrine_top`, with amber) missed by **9.277 ns**, over 3,755 failing
endpoints (TASK-001 stage 4). The worst path started in amber's way
select, came out as the response data, went through the load align and
the forward from WB into EX's branch compare, and ended at the PC and the
I\$ RAM address: 24 logic levels in one cycle.

The cause is the decision of the last section. A 1-cycle hit delivers
the data late in the cycle, and peregrine consumed it in the same cycle
through a forward. Fast in cycles and slow in nanoseconds is the classic
trade.

## Phase 1: free fixes

The first pass removed paths that were not architectural: none of these
steps changes a cycle count, except one that saves cycles.

| Step | Change | WNS at 10 ns |
|------|--------|--------------|
| Base | Stage 4 as committed | -9.277 |
| 1 | I\$ tag read registered alongside the data | -9.949 |
| 2 | D request no longer gated by the I\$ stall; an early response waits in a register until WB | -9.974 |
| 3 | Branch and JAL targets, and their compare against the guess, computed in ID | -5.036 |
| 4 | I\$ read registers take `mem_wait` as an enable | -5.055 |
| 5 | JALR guess checked without the target adder; M-unit payload loads every idle cycle | -5.017 |

: Phase 1 (TASK-001 stage 7); step 2 saved 17 cycles in 4 rv32ui images

Step 3 is the big one: once the branch compare moved to ID, load data no
longer reached the PC. A single build moves by up to 1.5 ns from
placement alone, so each step was judged by the path group it targeted,
not by the total.

After step 5, the worst paths were amber's own. amber alone, at 10 ns on
this part, misses by 4.046 ns.

## Phase 2: the options for the response path

Three ways to stop consuming amber's response in the cycle it arrives
were measured or estimated (kernel CPI excludes the `mm` kernel, which
the iterative multiply dominates):

| Option | What | Worst slack on the path | Kernel CPI | rv32ui CPI |
|--------|------|-------------------------|------------|------------|
| None | Forward load data WB to EX the cycle it arrives | -5.017 | 1.343 | 1.989 |
| (a) | Register every load response (one more load cycle) | -0.230 at the register | 1.487 (+10.7%) | 2.017 (+1.4%) |
| (c) | No WB-to-EX forward of a load; ID waits instead | -1.761 | 1.429 (+6.4%) | 1.998 (+0.4%) |
| (b) | A 2-cycle amber hit (not built) | about (a) | +10.7% to +12.8% | +1.4% to +1.7% |

: The response-path options at 10 ns (TASK-001 stage 7)

None of them closes 100 MHz, because the response arrives about 11 ns
after the edge: registering it misses at the register, writing the
register file misses at the write port. Only (b) removes the late arrival
itself, at the cost of giving back the cycle TASK-005 won. Option (c)'s
cost is uneven: `sum` +16%, `memcpy` +13%, `list` +12%, `sort` +0.4%,
`crc` +1.6%.

## The decision: lower the clock

The owner kept the 1-cycle hit and the CPI and lowered the clock target
instead (2026-11-25). The sweep, with 0.2 ns of clock uncertainty added
to budget placement noise:

| Period | Frequency | WNS |
|--------|-----------|-----|
| 16.0 ns | 62.5 MHz | -0.607 |
| 16.67 ns | 60.0 MHz | -0.043 |
| 17.0 ns | 58.8 MHz | +0.331 |
| 17.5 ns | 57.1 MHz | -0.051 |
| 18.5 ns | 54.1 MHz | +0.100 (+0.342 with `MUL_DSP=1`) |

: Clock sweep, `peregrine_top` out of context on xc7a100t-1 (TASK-001 stage 7)

17.0 ns passes and 17.5 ns fails: near the edge, placement noise is
larger than the budget, so 17.0 ns is a lucky build, not a target. The
target is **18.5 ns, 54.1 MHz**, the period that closed in both
multiplier builds. Every remaining tight path runs through amber; every
path that stays inside peregrine has at least 3.5 ns to spare. amber's
own closure on this part is cache-ip/amber-mesi-l1 TASK-007.

## The floor: 75 MHz

The decision did not last. HIVE, the first system to carry peregrine,
runs every clock domain at 75 MHz, and the owner set that as the floor
(2026-11-26: "the slowest clock I want is 75mhz"). At 13.333 ns the
stage-7 design missed by 2.501 ns, and every failing path group ran
through amber:

- inside amber, its control state through the miss decision to the data
  RAM address (-2.50);
- core to amber, `mie` through the interrupt decision and the D request
  into amber's accept (-2.35);
- amber to core, the response through the load align and the WB-to-EX
  forward into the ALU (-1.94).

Four changes close it in the study (riscv-ip/peregrine-rv32im TASK-006),
each measured on top of the last:

| Change | Cost | WNS at 13.333 ns |
|--------|------|------------------|
| None (stage 7) | | -2.501 |
| Option (c): no WB-to-EX forward of a load | +6.4% kernel CPI | -2.003 |
| Register the interrupt decision | 1 cycle of interrupt latency | -0.525 |
| amber reads a miss's beat 0 a cycle later | 1 cycle per dirty miss | -0.305 |
| amber's clean-all commit check from a flop | none | +0.587 |

: The 75 MHz changes, timing study (TASK-006)

The two amber changes share a shape: a decision fed back into an address
or a write enable in the same cycle it was made. The miss path used to
switch the data RAM address to beat 0 while `CTRL_LOOKUP` was still
deciding it had missed; now the first miss cycle presents beat 0. The
clean-all commit used to compare the tag in the cycle that writes it; the
cycle before it (the drain's last) cannot change that tag, so the compare
is sampled there.

The finished RTL needed a fifth. With the four changes built for real,
one `MUL_DSP=1` placement missed by 0.003 ns on a path that is the same
shape again: amber's state, out as ready, through the CPU's request valid,
back in as the accept, selecting the tag LUTRAM address. The address only
matters when a request is accepted, and the accept can only happen in a
state where ready is high, so the mux now selects on ready (a register
function) and the CPU's logic leaves the address cone. With all five, every
placement closed with the 0.2 ns budget in:

| Period | Frequency | `MUL_DSP` | WNS |
|--------|-----------|-----------|-----|
| 12.5 ns | 80.0 MHz | 0 | +0.133 |
| 13.0 ns | 76.9 MHz | 0 | +0.316 |
| 13.0 ns | 76.9 MHz | 1 | +0.111 |
| 13.333 ns | 75.0 MHz | 0 | +0.300 |
| 13.333 ns | 75.0 MHz | 1 | +0.099 |

: Clock sweep, the TASK-006 RTL

The target is **13.333 ns, 75 MHz**. Time per kernel instruction went
from 1.343 x 18.5 = 24.8 ns to 1.429 x 13.333 = 19.1 ns, 1.30 times
faster. A 2-cycle amber hit, option (b), also closes 75 MHz (+0.30 ns as
a stand-in) but costs 10.7% to 12.8% CPI, about 20 ns per instruction.

## What the story teaches

- **A cycle saved in one block can cost nanoseconds in another.** The
  1-cycle hit was a CPI win measured in isolation; the system paid for it
  in the period.
- **Measure all the options before choosing.** Every option that kept
  100 MHz cost 0.4% to 12.8% CPI and still did not close.
- **Iron law.** Time = instructions x CPI x period. The stage-7 decision
  kept CPI and gave up period; the 75 MHz floor gave back 6.4% CPI for a
  39% faster clock, and won 1.30 times overall.
- **A floor set by the system beats a target set by the block.** The
  clock came from what HIVE needed, not from what peregrine reached.
