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

# Purpose and Scope

## What peregrine Is

peregrine is rung 3 of the RTL Design Sherpa falcon suite: an in-order, single-issue RV32IM core with merlin's five-stage pipeline extended by four things, each of them a lesson (PRD §1):

1. **Speculation.** A 32-entry BTB and a 256-counter 2-bit BHT fetch down the predicted path. A correctly predicted taken branch costs no cycles; a mispredict costs 2.
2. **Precise traps.** A machine-mode CSR file, exception delivery through `mtvec`, `mret`, and three interrupt sources. The halt contract of kestrel and merlin is retired: every exception is a trap.
3. **The M extension.** One iterative multiply/divide unit, `peregrine_mdu`. An M instruction holds in EX until its result is ready (33 stall cycles iterative), so the result writes back in program order.
4. **The memory hierarchy.** Split blocking L1 caches behind AXI4 masters: a 4 KiB direct-mapped I\$ inside peregrine, and amber (cache-ip/amber-mesi-l1) as a 32 KiB 4-way write-back D\$.

peregrine is meant to diff against merlin as additions: merlin's stage registers, forwarding unit (EX/MEM over MEM/WB, select computed in ID), load-use bubble, load-to-branch interlock and WB-to-ID bypass are carried over.

## Two Builds

| Build | Top module | Memory side | Purpose |
|-------|-----------|-------------|---------|
| Cacheless (`CACHE_EN=0`) | `peregrine_core` | Two registered-read ports (fetch and data) and the `mem_wait` hold, merlin's contract | Fast batteries, riscv-formal reach (P12), core bugs isolated from cache bugs |
| Cached | `peregrine_top` | One AXI4 fabric master; I\$, amber D\$, CLINT and the uncached port inside | The system build; the timing target of P14 |

: The two peregrine builds

## Scope of This Document

In scope: the ISA implemented, the programmer-visible state, the address map, every port of `peregrine_core` and `peregrine_top`, the memory and trap contracts at those ports, the cycle costs, the clock reached on the Nexys A7 part, integration rules, and a summary of how the RTL was verified.

Out of scope: block internals (MAS), the predictor drill and the study book (riscv-ip/peregrine-rv32im TASK-003), and the hive-serv HIVE-C integration (TASK-004).

## Non-Goals

These are PRD §2's, and the RTL holds to them:

- No out-of-order execution and no superscalar issue (gyrfalcon's lesson).
- No A, F, C or D extensions.
- Machine mode only: no supervisor or user mode, no MMU, no PMP regions (the PMP CSRs exist with zero entries; see "Programmer-Visible Machine State and Traps").
- No non-blocking caches: one memory access is in flight at a time.
- No performance target. Clocks and area are reported; the FPGA point is P14 (see "Performance Characteristics").

## Lineage

| Rung | Core | Adds |
|------|------|------|
| 1 | kestrel | Single-cycle RV32I |
| 2 | merlin | Five-stage pipeline, forwarding, interlocks |
| 3 | **peregrine** | Prediction, precise traps, M extension, L1 caches |
| 4 | gyrfalcon | Out-of-order issue (rename, ROB); reuses peregrine's predictor, traps, L1s and fabric on the same RV32IM baseline |

: The falcon ladder around peregrine

---

**Last Updated:** 2026-11-25
