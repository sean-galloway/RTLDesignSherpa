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

# Characterization

**Status:** measured 2026-11-21 and 2026-11-22 (onyx TASK-001 steps 2, 6 and 6b; success criteria 4, 5 and 6).

## The manager alone, out of context

Kintex-7 325T-2, 10 ns clock, synth + place + route, both at 18 slots and SNOOP_INFLIGHT 2, clocked on `clk` (`make ooc CACHE=onyx2` and `CACHE=jetp_fabric` on the reference rig):

| manager | LUT | FF | LUTRAM | RAMB | WNS at 10 ns | worst path levels |
|---|---|---|---|---|---|---|
| `onyx_ccu`, N_PORTS 2 | 4,628 | 1,664 | 1,296 | 0 | +2.885 ns | 9 |
| `jet_prime_pair_fabric` | 4,300 | 1,660 | 1,296 | 0 | +2.757 ns | 10 |

: Table 6.2: The two managers alone

The generalization to N ports costs 328 LUT (7.6 percent) at two ports -- the per-buffer CD write arbitration, the rotating grants and the per-slot peer counters -- and no flops or LUTRAM; the snoop-data buffers are the same two 18-slot by 8-beat distributed RAMs. Timing is unchanged in kind: the worst path is the pending-queue count into a table write enable in both.

## The reference rig at 100 MHz

The Genesys2 reference rig, two jet-primes behind the manager, the house memory, the pipelined injector, the UART host stack:

| build | manager | WNS at 100 MHz (0.2 ns uncertainty budget) | LUT | FF | worst path |
|---|---|---|---|---|---|
| `REF_CACHE_SEL=3`, bin 7 | pair fabric | +0.040 ns | 18,241 | 11,896 | jet-prime fill-engine staging read pointer into the data-array address |
| `REF_CACHE_SEL=4` | onyx, read alongside the snoop | +0.006 ns | 18,672 | 11,900 | the same path |
| `REF_CACHE_SEL=5` | onyx, read deferred | +0.000 ns, 0 failing endpoints | 18,633 | 11,881 | the same path |
| `REF_CACHE_SEL=4`, observation build (bin 2) | onyx + observer + counters + the pair block's MonBus tally chain | +0.001 ns | 27,872 | 25,877 | the same path |
| `REF_CACHE_SEL=5`, observation build (bin 2) | the same, read deferred | +0.027 ns | 27,143 | 25,854 | the same path |
| `REF_CACHE_SEL=4`, mask layers (bin 3) | the same as bin 2 with the observer's mask layers on the harness CSR | -0.001 ns, 1 failing endpoint (placement noise under the budget) | 27,668 | 25,090 | the same path |
| `REF_CACHE_SEL=5`, mask layers (bin 3) | the same, read deferred | -0.035 ns, 6 failing endpoints (within the budgeted spread) | 26,955 | 25,071 | jet-prime fill staging RAM, the same family |

: Table 6.3: Reference-rig builds

Both onyx builds meet 100 MHz under the budget; the margins are placement noise around the same jet-prime path, and onyx is not on it. (The flow keeps one report set per build and SEL 5's overwrote SEL 4's; SEL 4's utilization is from a rebuild, which reproduced its WNS of +0.006 ns.)

## Cycles per transaction on the board

The 55-point sweep (seven configurations by five depths), injector 1 idle, 20,000 transactions each; the dual sweep the same with both injectors active. Against the pair fabric's bin 7:

| | SEL 4 (onyx) | SEL 5 (onyx, deferred read) |
|---|---|---|
| single sweep, 55 cells | every cycle count equal to bin 7's; every CRC equal | resident cells equal; `r16k_we64` +0.4 to +0.9 %; thrash depth 1: `r64k_we64` +11.4 %, `r64k_we255` +8.1 %, `r128k_we64` +12.2 %; at depth 16: +1.8 / +0.2 / +1.5 %; every CRC equal |
| dual sweep, 55 cells, both injectors | every cycle count equal to bin 7's on both injectors; every CRC equal | `r64k_we64` depth 1 12.28 -> 13.68 and 12.25 -> 13.62, depth 16 5.30 -> 5.40 and 5.32 -> 5.42; `r128k_we64` depth 1 16.95 -> 18.96, depth 16 7.54 -> 7.66; every CRC equal |
| hit floor (`r4k_we0` depth 1 minimum latency) | 2 | 2 |
| MLP on `r64k_we64` at depth 16 | 10.60 | 10.72 |

: Table 6.4: Board sweeps against the pair fabric

PRD criterion 6 is met by SEL 4 exactly: onyx in parallel-issue mode is the fabric it replaces, cycle for cycle, with two real caches at every depth. SEL 5 prices the D6 trade's latency side: a miss served from memory pays the gather before the read, 8 to 12 percent at depth 1 on the thrash rows, under 2 percent at depth 16 where the gather overlaps other misses. The bandwidth side -- memory reads not issued when a peer supplies the line -- is not counted by the rig yet; a memory-side AR counter is a D9 tap and the next measurement.

The observation builds (bin 2) add the pair block's MonBus tally chain, the observer and the counters: about 9,200 LUT and 14,000 flip-flops over the bin 1 builds, almost all of it the chain the jet rig also carries (its 32-bin tally with a 16-deep latch bank and the AXI-Lite group writer), and no cycle: all 220 bin 2 cells, both modes, both sweeps, reproduce their bin 1 cycle counts exactly.

## The D6 trade, counted (criterion 4)

The exact counters, read in the tally's frozen window after each cell (both injectors, 20,000 transactions each; the full table is the "onyx counters" section of the reference comparison):

| config | depth | mode | transactions | memory reads | lines supplied | reads wasted | wasted / issued |
|---|---|---|---|---|---|---|---|
| `r16k_we64` | 1 | read alongside the snoop | 381 | 381 | 116 | 116 | 0.304 |
| `r16k_we64` | 1 | read deferred | 381 | 265 | 116 | 0 | 0 |
| `r64k_we64` | 1 | read alongside the snoop | 20,240 | 20,240 | 192 | 192 | 0.009 |
| `r64k_we64` | 1 | read deferred | 20,240 | 20,048 | 192 | 0 | 0 |
| `r64k_we255` | 1 | read alongside the snoop | 20,490 | 20,303 | 637 | 637 | 0.031 |
| `r64k_we255` | 1 | read deferred | 20,490 | 19,666 | 637 | 0 | 0 |
| `r128k_we64` | 16 | read alongside the snoop | 30,083 | 30,072 | 638 | 627 | 0.021 |
| `r128k_we64` | 16 | read deferred | 30,083 | 29,445 | 638 | 0 | 0 |

: Table 6.5: Reads issued, lines supplied, reads wasted

The reading. With the read alongside the snoop, every line a peer supplies is a read the memory answered for nothing: `reads wasted` equals `lines supplied` in every cell but the deep ones, where a few snoops answered before the memory port took the AR (11 of 638 on `r128k_we64` at depth 16) and the read was never issued. The wasted share is the sharing rate: 30 percent of the memory reads on the shared resident set (`r16k_we64`), 1 to 3 percent in the thrash cells, where almost every miss is a capacity miss nobody else holds. With the read deferred, `reads wasted` is zero in every one of the 110 cells and `memory reads` falls by exactly `lines supplied`: the elision is complete, and its price is the latency Table 6.4 measured (+8 to +12 percent per transaction at depth 1 in thrash, under 2 percent at depth 16). The two counters, and the agreement between them, are the measurement D6 asked for; the 55 single-injector cells supply no line (no peer holds anything) and read as the control: wasted 0, memory reads equal in both modes.

On the MonBus side the tally bins carry the same classes but not the same totals when every class is open, as the channel's design intends: the house MonBus is a low-bandwidth event channel, the pair block's one channel (an AXI-Lite group writer, several cycles a packet) serves three observers, and four of onyx's classes fire once a transaction, so at the thrash cells' rates the observer's holders overflow and it reports loss, with the drop report's 8-bit payload saturating. Bin 11 (`TXN_START`) reads 12,613 against 20,240 transactions on `r64k_we64` depth 1 and 3,891 at depth 16; on the resident and warm-up cells the bins and counters agree. With every class open the tally bins are lower bounds on the board and the counters are the measurement. The observer's mask layers (Table 4.2) are the remedy the house monitors carry for this, and the bin 3 build measures them: with `MEM_READ` opened alone (`--onyx-mon-classes MEM_READ`) its bin equals its counter in 39 of the 55 dual cells and in every cell at depth 1 and 2 (`r64k_we64` depth 1: 20,240 = 20,240, where the all-open bin read 12,603), the 16 short cells are the 64k and 128k thrash cells at depth 4 to 16, where the channel is still shared with the two caches' unmasked observers and each carries a drop report, and the masked classes' bins are zero in all 55; the all-open sweep on the same build is cycle-identical to bin 2 in all 55 cells. The deferred build (SEL 5, bin 3) reads the same way: `MEM_READ` alone equals its counter in 45 of 55 cells and 21 of the 22 at depth 1 and 2 (`r64k_we64` depth 1: 20,048 = 20,048), the short cells are the same thrash cells at depth, every one with a drop report, the masked bins zero in all 55, reads wasted zero in all 55, and the all-open sweep is cycle-identical to bin 2 in 51 of 55 cells (the four are the first depth-1 cells, where the dirty state carried in from the preceding run differs). One class at a time is what the channel carries exactly; the union is the lower bound (onyx ISSUE-001, closed into TASK-001 step 6c).

Reproduction: Chapter "Reproduction" of the [reference comparison](../../../../docs/reference_l1_comparison.md); results `perf_sweep_onyx_bin1_*` and `perf_sweep_onyxd_bin1_*` (cycles) and `perf_sweep_onyx_bin2_*` and `perf_sweep_onyxd_bin2_*` (cycles, tally bins and counters, `--profile ref-onyx`), and `perf_sweep_onyx_bin3_dual_*` / `perf_sweep_onyx_bin3_memread_dual_*` and the `onyxd` pair (the mask layers: every class open, then `MEM_READ` alone) under the rig's `results/`.
