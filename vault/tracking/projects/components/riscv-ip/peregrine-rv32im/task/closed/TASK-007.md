# TASK-007: interruptible M instructions -- cancel in flight, one instruction of progress after mret

**Priority:** P3
**Status:** closed 2026-11-27 (filed 2026-11-27; owner: "yes"; started after TASK-005 landed, owner "start 7").
**Owner:** Claude
**From:** [ISSUE-001](../../issue/closed/ISSUE-001.md), option 2 with a progress guarantee

## Why

An M instruction can't be interrupted today: a pending interrupt waits for
every M instruction ahead of it, about 34 cycles each. Cancelling on its
own is not enough. The first stage-2 build cancelled and restarted, and
livelocked when interrupts arrived faster than the divider finished
(`test_peregrine_mext`, mutant M5).

## What

- **Take the interrupt while an M instruction holds in EX.** Cancel the M
  unit and discard its result; `mepc` is the M instruction's own PC.
- **Progress rule:** the first instruction after an `mret` cannot be
  interrupted until it retires. One flag: set by `mret`, cleared when the
  next instruction retires or takes a synchronous trap. Every interrupt
  return then retires at least one instruction, so a cancelled M
  instruction completes on its second issue, whatever the interrupt rate.
- **Worst-case latency is one M instruction** (about 34 cycles), and only
  when an interrupt arrives right after an `mret` into one. Today it is
  about 34 cycles per back-to-back M instruction.

## Done when

- `test_peregrine_mext`'s re-raise case retires every M instruction.
- A new directed test of k back-to-back divides under interrupts measures
  the latency bound, and the bound is written into PRD §4.3/§4.4.
- Mutants:
  - with the progress flag dropped, the suite livelocks (times out);
  - with the cancel dropped, it shows the old latency.
- riscv-formal, the shadow CSR model and spike lockstep agree: `mepc`
  points at the M instruction.
- 75 MHz still closes, measured in both `MUL_DSP` builds.
- peregrine FULL is green from clean.
- The HAS/MAS trap chapters are updated, at their current revision.

## As built (2026-11-27)

- **EX interrupt** (`peregrine_core`): `ex_m_irq = ex_m_valid & ~mdu_idle &
  ~mdu_done & ~ex_mem_q.valid & csr_irq_pending & ~mem_wait`. That cycle
  EX/MEM takes the M instruction (tagged `irq_take`, a new `ex_mem_t`
  bit) instead of the hold bubble, and `r_ex_irq_cause` latches the cause;
  in MEM the tag is an interrupt unconditionally, `mepc` = the M
  instruction's PC, and the redirect cancels the unit and flushes the copy
  ID/EX still holds. Busy, not idle: the latched operands RVFI reports
  are valid. Not done: a finished M instruction still commits and the
  interrupt goes to the next one. `mem_ls_ok` reads the untagged term
  (`mem_irq_lv`), keeping the tag out of the 75 MHz accept cone;
  `ex_leaves` includes the tagged instruction (it retires as a trap beat).
- **Progress rule**: `r_mret_shadow`, set by `mem_mret`, cleared when the
  next instruction commits at MEM; its next state `w_irq_block` goes to
  `peregrine_csr` (new port `irq_block`), which holds the registered
  `irq_pending` low, so neither path takes an interrupt and the commit
  cone is unchanged.
- **DV**: `test_peregrine_mext` irq variants now require interrupts on M
  instructions (full: 531 to 1,288 per variant and build) and check every
  handler `mepc` read against the shadow trap-CSR model (`csr_shadow.py`;
  the handler reads mepc on every interrupt). New
  `cocotb_test_peregrine_mext_latency`: 8 back-to-back divides per pass,
  the timer re-raised 3-120 cycles after each acknowledge, every quotient
  checked; latency (raise to trap beat) bound `LAT_BOUND = 40`, measured
  worst 38, mean 8.1, about 2,100 interrupts per build at full, every
  divide retired.
- **Mutants** (each restored byte-identical): cancel dropped (`ex_m_irq`
  = 0) -> no interrupt on an M instruction, latency 271 behind 8 divides;
  progress flag dropped (`w_irq_block` = 0) -> the mext irq variants
  livelock (no `tohost` in 14,600 cycles).
- **Gates**: peregrine FULL 100/100 from clean (94 + the 6 latency cells).
- **OOC** xc7a100t-1, 13.333 ns, 0.2 ns uncertainty, the TASK-005 script:
  `MUL_DSP=0` +0.273 (TASK-005 +0.270), `MUL_DSP=1` +0.466 (+0.320); 14
  levels (15 before); 5,061 / 5,076 LUT (+17 / +11). The `MUL_DSP=0` worst
  path now starts at the `irq_take` flop and ends in amber's control
  state, as the irq-pending path did before.
- **Formal**: riscv-formal 52/52 on both `MUL_DSP` builds; `top_props`
  prove PASS and cover 14/14; `core_props` prove (BMC 20) PASS with two
  new asserts (`ap_i_after_mret_not_irq`: the retire after an mret is
  never an interrupt; `ap_i_m_cancelled`: the M unit is idle the cycle
  after a tagged instruction traps) and cover 13/13 (new: an interrupt on
  an M instruction; the post-mret instruction retiring with the timer
  line up). Formal mutants: progress flag dropped fails
  `ap_i_after_mret_not_irq`; the cancel dropped on a tagged trap fails
  `ap_i_m_cancelled`.
- **Docs**: PRD §4.3 / §4.4 (the latency bound) and history; HAS trap
  chapter and verification summary; MAS traps, M unit, package and CSR
  port table; books rebuilt at v0.1. Handbook
  [[interrupts-must-not-discard-finished-work]] gains the progress rule.
