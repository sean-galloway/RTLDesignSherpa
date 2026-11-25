<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Performance Characteristics

peregrine has no performance target (PRD §2); this chapter reports what was measured. CPI figures come from simulation on the TB memory models, not from a board.

## Cycle Costs

| Event | Cycles added | Notes |
|-------|--------------|-------|
| Correctly predicted taken branch, JAL or JALR | 0 | The lesson of PRD §4.2 |
| Mispredict (direction, or target of a taken guess) | 2 | IF/ID and ID/EX flushed; merlin pays this on every taken branch |
| Load followed by a dependent instruction | 1 | Load-use bubble |
| Load followed by a dependent branch or JALR | 2 | Load-use bubble plus the load-to-branch interlock; 1 if one instruction sits between |
| CSR instruction behind an older CSR instruction | up to 2 | It waits in ID until the older one has written in MEM |
| M instruction, iterative | 33 | Hold-in-EX: start cycle plus 32 steps |
| Divide by zero, or -2^31 / -1 | 1 | Early-out |
| Multiply with `MUL_DSP=1` | 2 | One registered 32x32 product |
| Trap, `mret`, `fence.i` | 3 | The three younger instructions are discarded |
| `fence.i`, cached build | + the D\$ clean | One write-back per dirty amber line, then a 1-cycle I\$ invalidate; later fetches miss |
| D\$ hit (load or store) | 0 | Accepted in MEM, response in WB (amber TASK-005) |
| Access in the cycle after a D\$ write hit | 1 | A write hit holds amber's port a second cycle |
| D\$ miss | amber's miss time | 29 cycles from accept to response on amber's pair rig bench memory (PRD P13) |
| First store to a line a load brought in | amber's upgrade | amber installs fills Shared; the store pays a CleanUnique upgrade, 18 cycles on the rig (amber TASK-006 is open to install Exclusive) |
| I\$ miss | refill | One AR, a whole-line INCR burst (8 beats at 64 B / 64-bit), one replay cycle, plus fabric latency |
| CLINT access | 0 | Response the next cycle |
| Uncached access | one AXI4 round trip | A store waits for its B response (stores are not posted) |

: Cycle costs as built

## Measured CPI

All on `peregrine_sys_tb_top` (`peregrine_top` on a behavioral AXI4 memory) unless noted.

| Workload | CPI | Source |
|----------|-----|--------|
| Five self-checking kernels (`sum`, `list`, `sort`, `memcpy`, `crc`; the sixth, `mm`, is left out because its iterative multiply dominates it) | 1.343 | TASK-001 stage 7 CPI harness |
| rv32ui images | 1.989 | TASK-001 stage 7 CPI harness |
| M-heavy stress program (5,941 instructions, 34% M), iterative multiply | 9.16 | TASK-001 stage 2, cacheless |
| The same program, `MUL_DSP=1` | 3.83 | TASK-001 stage 2, cacheless |

: Measured CPI

The rv32ui images are short self-checking tests dominated by cold misses and traps; the kernels are the better guide to steady-state CPI. The stress program is not a benchmark: it makes the M unit's structural hazard visible.

## Branch Prediction

`BP_EN=1` against `BP_EN=0` (predict not taken, merlin's fetch) on the PRD §5 predictor streams, full level (speedup = cycles at `BP_EN=0` / cycles at `BP_EN=1`):

| Stream | Speedup |
|--------|---------|
| Loop, trip count 1 / 2 / 3 / 4 | 1.32 / 1.18 / 1.28 / 1.35 |
| `bht_alias` | 1.81 |
| `btb_alias`, `jalr_targets` | 1.33 |
| `interlock` (mispredicts with an ID interlock on the wrong path) | 1.04 |
| `trap_shadow` | 1.05 |
| Generated hazard programs | 1.005 |

: Predictor A/B speedups

## Clock and Area (PRD P14)

The FPGA target is **18.5 ns (54.1 MHz)** on the Nexys A7 part, xc7a100t-1, set by the owner on 2026-11-25. Measured out of context on `peregrine_top` with 0.2 ns of setup uncertainty added:

| Period | MHz | `MUL_DSP` | WNS (ns) |
|--------|-----|-----------|----------|
| 15.5 | 64.5 | 0 | -0.684 |
| 16.0 | 62.5 | 0 | -0.607 |
| 16.67 | 60.0 | 0 | -0.043 |
| 17.0 | 58.8 | 0 | +0.331 |
| 17.5 | 57.1 | 0 | -0.051 |
| **18.5** | **54.1** | **0** | **+0.100** |
| **18.5** | **54.1** | **1** | **+0.342** |

: OOC timing sweep, xc7a100t-1

17.0 ns closed but 17.5 ns did not: near this edge the placement noise is larger than the 0.2 ns budget, so 18.5 ns, which closed in both multiplier builds, is the target.

At 17.0 ns the build used 5,064 LUTs, 3,004 flip-flops, 9 RAMB36 and 922 LUTRAM (`MUL_DSP=0`).

The three tightest path groups all run through amber: amber's own control state into its data RAM address, the core's request into amber's accept-cycle lookup, and amber's response into the core's load alignment and forwarding. Every path group that stays inside peregrine has at least 3.5 ns of slack. amber built alone with `MAINT_EN=1` misses 10 ns on this part by 4.05 ns. The owner kept amber's 1-cycle hit and lowered the clock rather than add a stage to the load path; amber's paths are filed as cache-ip/amber-mesi-l1 TASK-007.

---

**Last Updated:** 2026-11-25
