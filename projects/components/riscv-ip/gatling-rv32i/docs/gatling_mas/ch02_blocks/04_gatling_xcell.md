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

# gatling_xcell

## Purpose

The Xcell unit: it answers `gatling_core`'s Xcell port for the seven custom-0 instructions (PRD 3.1) and drives, per context, that context's cell -- the input memory's read port, the result memory's write port and the alu-infer issue and retire handshakes. It replaces the cell's own execution FSM as the ALU's driver (cell MAS 4, owner ruling 2026-10-19): the program is the schedule.

## The contract with the core

The core presents one Xcell instruction per cycle, in X: `xc_req`, its context `xc_ctx`, `xc_funct3`, `xc_reg0` (the register field, insn[11:7], is x0), `xc_rs1` (that register's value) and `xc_imm` (insn[31:20]). The unit answers `xc_ok` in the same cycle. `xc_ok = 0` is an interlock stall: the core retires nothing, writes nothing and leaves the PC, so the context fetches the same instruction on its next slot, NUM_HARTS cycles later, and tries again. POP rd and CFG rd take their value from `xc_rdata` the next cycle, in W, like a load.

Nothing in this block waits on another context. A context's cell is its own (PRD 4.2), and a context's next instruction is NUM_HARTS cycles behind its last, so no two of one context's accesses meet.

## The instructions

| funct3 | Instruction | Completes when | Action |
|---|---|---|---|
| 000 | `POP x0` | the stager is empty and the input memory holds `cfg_op_lines` lines | read line A now (and B the next cycle), offer both to the ALU with `cfg_func_sel`, `cfg_threshold` and acc_ctrl = insn[21:20] |
| 000 | `POP rd` | the input memory holds a line | read it; it reaches rd in W |
| 001 | `PUSH x0` | `alu_result_valid` and the result memory is not full | `alu_result_ready`; write `result_line \| result_flags` at the tail |
| 001 | `PUSH rs1` | the result memory is not full | write rs1 at the tail |
| 010 | `ECTX` | always | (the core halts the context, cause 8) |
| 011 | `FLUSH rs1` | no earlier command is waiting | latch {tag = rs1[18:15], dest = rs1[14:0]}; offer it on `flush_valid` until `flush_ready` |
| 100 | `KICK rs1` | always | set the context's event bit; pulse `kick_valid` with `kick_value` = rs1 |
| 101 | `WAIT rs1` | every context in mask rs1[NUM_HARTS-1:0] has its event bit set or is done | none |
| 110 | `CFG rd, idx` | always | rd <- 0: `cfg_func_sel[8:7]` (element format), 1: `cfg_credit_batch`, else 0 |

: Table 2.5: Xcell instructions in gatling_xcell

Register x0 is the ALU port (owner, 2026-11-26). It reconciles the PRD's register-to-memory POP and PUSH with the cell MAS's POP-issues / PUSH-retires: a program moves lines through the ALU with `POP x0` / `PUSH x0`, or handles them in RV32I with `POP rd` / `PUSH rs1`, and never leaves an ALU result nobody retires. x0 costs nothing: as a source it is the constant zero, which no program needs to push.

`result_line | result_flags` is exact: the compare row returns a zero line and its mask on flags, every other row its line and zero flags (alu-infer PRD 4).

acc_ctrl rides in POP x0's insn[21:20], where the PRD's encoding has zeros; zero is HOLD, which every row except MAC and REDUCE ignores. It is the program's, not the cell configuration's, because a MAC chain clears once and accumulates after: the sequence is a schedule, and the program is the schedule.

## The issue stager

The input memory has one registered read port, so a two-line invocation is read over two cycles. In X the unit reads line A (and the head advances); the next cycle `stg_cap_a_q` captures A and, for a two-line function, reads line B; the cycle after, `stg_cap_b_q` captures B. The operands are then offered (`op_v_q`) and held, with the function and acc_ctrl latched at the POP, until the ALU takes them. A one-line function is offered a cycle earlier with B = 0. While any of the three is set, the next `POP x0` of the context stalls.

The read port is shared by the stager's B read and a `POP rd` of the same context, but the B read happens one cycle after the POP and the context's next instruction is NUM_HARTS cycles after it, so they never meet.

## Pointers and the consumed-line pulse

The unit owns the input memory's head and the result memory's tail, one each per context, wrapping at `IN_DEPTH` and `OUT_DEPTH`. The fill side (rx demux) owns the input tail and the drain side (packetizer) the result head; the memories' occupancy counters, which count every write and read, are the only shared state, and the interlocks read them. Every input-memory read pulses `line_consumed[c]`: one consumed line, which the cell's credit block (cell TASK-001) batches into credit returns (PRD 5: credits count elements consumed, not instructions).

## KICK and WAIT

Each context has one event bit, set by its KICK and cleared only while the context is held (`hart_run` low). WAIT completes when every context in its mask has either kicked or is done (ECTX). That makes a one-shot barrier per run, which is what a tetrad's group-done needs (owner, 2026-11-26); a reusable barrier with generations belongs to the tetrad MAS when it exists. A context that halts for any other reason never satisfies a WAIT: a locked context is a bug to surface, not a member that finished.

## The program contract

Every interlock waits on something outside the context -- a line arriving, a result-memory slot draining, the drain controller taking a FLUSH, the ALU taking or returning an invocation -- with three exceptions that only the program can rule out, because the thing waited for is the waiting context's own next instruction:

- `PUSH x0` with no invocation outstanding waits for a result that was never issued.
- More than `PIPE_DEPTH + 1` `POP x0` outstanding (issued and not yet retired by a `PUSH x0`): the ALU holds `PIPE_DEPTH` and the stager one more, so the next `POP x0` waits for the stager, the stager for the ALU, and the ALU for a `PUSH x0` the stalled context can never reach.
- `WAIT` on a context that never KICKs or finishes.

Outside those, no interlock can wait forever: the bounded-liveness proof (Chapter 5, `formal/gatling/xcell_live`) shows it on the real core and unit against a fair abstract cell. The tetrad program keeps one invocation outstanding (POP x0 then PUSH x0), well inside the bound.

## Status

`ctx_stalled[c]` is set while context c's last X slot stalled and `ctx_stall_op[c]` names the instruction (funct3), `event_flags` shows the event bits, `kick_valid` / `kick_value` the KICKs. With the core's `done` these are the per-context status the PRD gives the tetrad MonBus (active, stall reason, done).

## Parameters

`NUM_HARTS` (4..32: the WAIT mask is a register), `LINE_W` (32 only: a line is one register), `IN_DEPTH` and `OUT_DEPTH` (at least 2; need not be powers of two).
