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

**Status:** measured 2026-11-21 (onyx TASK-001 steps 2 and 6; success criteria 5 and 6).

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

Reproduction: Chapter "Reproduction" of the [reference comparison](../../../../docs/reference_l1_comparison.md); results `perf_sweep_onyx_bin1_*` and `perf_sweep_onyxd_bin1_*` under the rig's `results/`.
