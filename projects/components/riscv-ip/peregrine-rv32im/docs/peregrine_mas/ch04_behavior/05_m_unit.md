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

# The M Unit and Hold-in-EX

## The Decision

The spec's busy scoreboard would let independent instructions pass the divider, with the M result written back after younger instructions had retired. RVFI cannot report that write, and riscv-formal's instruction checks (PRD P12) depend on RVFI. The owner chose hold-in-EX instead (P3, 2026-11-23, "Hold in EX"): the M instruction waits in EX until its result is ready and writes back in program order. The scoreboard is gyrfalcon's lesson.

## Signals

```systemverilog
ex_m_valid = id_ex_q.valid & id_ex_q.m_op;
mdu_start  = ex_m_valid & mdu_idle & ~mem_wait & ~mem_redirect_nw;
ex_m_stall = ex_m_valid & ~mdu_done;
```

The unit's `cancel` is `mem_redirect` and its `consume` is `~mem_wait`.

## The Hold

While `ex_m_stall` is high:

- the PC, IF/ID and ID/EX hold (the M instruction stays in EX);
- EX/MEM takes a bubble each cycle (`ex_mem_flush_eff` includes `ex_m_stall`), so the instructions ahead drain to WB and retire;
- the ID interlock bubble is suppressed (it would overwrite the held instruction);
- the EX redirect is suppressed (`ex_flush` includes `~ex_m_stall`): an M instruction that hit a stale BTB entry redirects only as it leaves;
- the predictor is not written.

When `done` rises, `ex_m_stall` falls, the result (`mdu_result`, selected into `alu_y`) moves to EX/MEM, and `consume` clears `done` at the same edge (unless `mem_wait` holds it).

## Operands

The unit starts on the first EX cycle without `mem_wait`, when the forwarded operands are valid, and latches them. During the hold the producers drain past WB, so the forwarding selects go stale. The core latches the same operands (`ex_m_rs1`, `ex_m_rs2`) for RVFI: `rvfi_rs1_rdata` and `rvfi_rs2_rdata` of an M instruction are the values it computed with. A mutant that reported the unlatched operands was caught by the RVFI shadow check and by riscv-formal's `insn_mul`.

## Latency

| Case | Stall cycles |
|------|--------------|
| Multiply or divide, iterative | 33: the start cycle, then 32 steps |
| Divide by zero, -2^31 / -1 | 1: the start cycle writes the result |
| Multiply, `MUL_DSP=1` | 2: the start cycle, then one registered product |

: M-unit stall cycles (PRD P8)

On one M-heavy stress program (34% M instructions) the iterative unit gave CPI 9.16 and `MUL_DSP=1` gave 3.83: the option nearly removes the structural hazard for multiplies.

## Interaction with Traps

An M instruction raises no exception of its own. A MEM redirect (an older trap or `mret`) cancels the unit; under hold-in-EX this can happen only in the M instruction's first EX cycle, because after that MEM holds bubbles. A mutant that did not cancel was caught only after the ecall handler changed the operand (re-executing with the same operands hid it). An interrupt also cancels it: a running M instruction is interrupted from EX, `mepc` = its PC, and runs again from the start after `mret`; a finished one is not interruptible in MEM ("Traps, Interrupts and the Commit Point").

## Timing

The `MUL_DSP=1` product is combinational between registers that sit behind muxes, so the DSP cannot absorb a pipeline register; the stage-2 review flagged it for P14. Measured at stage 7: at 18.5 ns `MUL_DSP=1` closed with +0.342 ns, better than the iterative build's +0.100 ns. At 13.333 ns (TASK-006) it closed with +0.099 ns against +0.300; in both builds the limiting path is the CPU request into amber, not the multiplier.

---

**Last Updated:** 2026-11-25
