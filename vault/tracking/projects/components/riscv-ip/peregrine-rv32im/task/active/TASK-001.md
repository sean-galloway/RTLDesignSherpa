# TASK-001: peregrine RV32IM core -- RTL, DV and targeted formal per PRD 0.2

**Priority:** P2
**Status:** ACTIVE (2026-11-24; stages 1-3 and 6 done)
**Owner:** TBD (owner, 2026-11-23: "accept defaults on the rest, commit and
push", ruling PRD P5-P14)

## What

Build peregrine to its [PRD](../../../../../../../../projects/components/riscv-ip/peregrine-rv32im/PRD.md)
0.2. Every decision row is DECIDED; the staging is PRD §7, each stage gated
before the next:

1. **Traps first, cacheless.** merlin's pipeline copied, plus the CSR file
   (P6), trap commit at MEM, `mret`, and `rv32i_decode` gaining `M_EXT` and
   `ZICSR` parameters, both default 0 (P11). Gate: `CACHE_EN=0`, rv32ui +
   rv32mi; kestrel, merlin and gatling full suites and the common-rv32i
   unit tests unchanged.
2. **M unit** (P3 revised to hold-in-EX, P8). Gate: rv32um,
   riscv-arch-test `rv32i_m/M`.
3. **Predictor** (P2, P5). Gate: predictor stress streams, `BP_EN` A/B.
4. **Caches and fabric.** `peregrine_icache` (P9), amber as D$, the AXI4
   arbiter and CLINT (P7), `fence.i` (P10). Gate: everything at
   `CACHE_EN=1`, `Zifencei`, the interrupt suite.
5. Targeted formal; riscv-formal insn checks on `CACHE_EN=0` (P12).
6. Measure amber's hit latency before stage 4 is designed around it (P13).
7. OOC timing at 100 MHz on xc7a100t-1 (P14).

## Depends on

- cache-ip/amber-mesi-l1 TASK-004 (CPU-side clean-all) for stage 4's
  `fence.i`. Stages 1-3 do not need it.
- cache-ip/amber-mesi-l1 TASK-005 (pipelined hit path, P13 option (b)) for
  stage 4's MEM stage. Closed 2026-11-24: a hit is 1 cycle.

## Stage 1: traps first, cacheless (done 2026-11-23)

Owner, 2026-11-23: "continue" (after the PRD 0.2 commit).

- **Shared decoder.** `rv32i_decode` gained `M_EXT` and `ZICSR`, both
  default 0 (PRD P11). The new outputs (`m_op`, `csr_op`, `mret`) are
  connected empty in kestrel, merlin and gatling.
  - The common-rv32i unit test gained a `M_EXT=1 ZICSR=1` cell.
  - The default cell now also checks that the M encodings are illegal and
    the new outputs stay 0.
- **`peregrine_core`.** merlin's pipeline with traps committed at MEM:
  - `peregrine_csr` holds the machine-mode CSRs of P6, plus zero-entry
    PMP CSRs;
  - interrupts are sampled at MEM;
  - `mret` redirects from MEM;
  - a CSR instruction reads in EX and writes in MEM, and waits in ID
    behind an older CSR instruction.
- **DV.**
  - `test_peregrine_battery`: rv32ui and rv32mi, with spike `--priv=m`
    lockstep on the (pc, insn) stream and every trap's kind and epc.
  - `test_peregrine_irq`: a self-checking program with a registered TB
    interrupt source and a seeded random re-raise delay.
  - Every run checks that data-memory requests equal retired accesses.
  - GTKW save file with a trap group.
- **Results, from clean** (`make run-all-full-parallel`, 9/9 cells):
  - rv32ui 42/42 against spike. `ma_data` is an expected failure at
    TESTNUM 668, the same as spike's: RV32I lets misaligned loads trap.
  - rv32mi 12/16. Four are excluded for hardware P6 leaves out: `zicntr`,
    `instret_overflow` (counters), `breakpoint` (debug triggers),
    `pmpaddr` (PMP regions). Each was run once and confirmed to fail on
    that hardware first.
  - Interrupts: about 125 taken per run, 17 to 24 of them on a load or
    store, with and without random `mem_wait`.
- **Mutation checks** (restored and diffed after each):
  - An interrupted load or store still accessing memory: caught by the
    side-effect count, 796 requests against 773 retired.
  - A trapping (misaligned) access still accessing memory: 6 rv32mi
    tests and `ma_data` fail.
  - ecall reporting mcause 8 instead of 11: 53 battery images fail
    lockstep.
- **Lessons.** Handbook
  [precise-trap-checks](../../../../../../../handbook/dv/precise-trap-checks.md).

## Stage 2: the M unit (done 2026-11-24)

Owner, 2026-11-23: "Hold in EX" (the P3 conflict: a busy scoreboard writes
the M result back after younger instructions retire, which RVFI cannot
report), then "yes" to build it.

- **`peregrine_mdu`** (new FUB, own filelist `peregrine_mdu.f`).
  - Busy, done and a 5-bit count, no state-encoded FSM.
  - Radix-2 shift-add multiply and restoring divide, 32 steps after a
    start cycle that captures the operand magnitudes.
  - Early-out for divide by zero and -2^31 / -1.
  - Sign fixup on the registered result: the high word of a negated
    product is `~hi + (lo == 0)`.
  - `MUL_DSP=1` replaces the multiply with one registered product.
  - Stall cycles: 33 iterative, 1 early-out, 2 `MUL_DSP` multiply.
- **`peregrine_core`.**
  - Hold-in-EX: the PC, IF/ID and ID/EX hold, and EX/MEM takes bubbles.
    The ID interlock bubble is masked while the M instruction holds.
  - The unit starts on the first EX cycle without `mem_wait` and latches
    its operands. RVFI reports the latched operands, because the
    forwarding selects go stale during the hold.
  - A MEM redirect cancels the unit.
  - `rv32i_decode` `M_EXT=1`, and `misa.M` is set.
  - **An M instruction is not interruptible in MEM**; the interrupt is
    taken on the next instruction. The first build let an interrupt
    discard the finished M instruction, and a timer re-raised 3 to 40
    cycles after each acknowledge livelocked it (PRD §4.3, handbook
    [interrupts-must-not-discard-finished-work](../../../../../../../handbook/design/interrupts-must-not-discard-finished-work.md)).
    This is a design addition beyond the owner's ruling. Owner,
    2026-11-24: "do the simple solution first; we can reevaluate later.
    add an issue to track it" -- kept, tracked as
    riscv-ip/peregrine-rv32im ISSUE-001.
- **DV.**
  - `test_peregrine_mdu`: the unit. A 14 x 14 edge cross product of all
    eight operations against a spec model, plus 2,000 (func) or 20,000
    (full) seeded random operations. It checks the exact stall count of
    each operation, the done result held until consumed, operands
    latched at start, and a cancel at every step. Both `MUL_DSP` builds.
  - `test_peregrine_battery`: rv32um added, on both builds. spike runs
    every suite as `rv32im`, because misa now says M.
  - `test_peregrine_arch`: riscv-arch-test 3.10.0 `rv32i_m/M` through
    the shared runner, which gained `ext=` and `halt="tohost"` (the
    reference image is the DUT image, since peregrine traps on ecall).
  - `test_peregrine_mext`: seeded generated programs of 15 hazard shapes
    around M instructions, checked three ways (in-program register
    compare, an RVFI shadow regfile on every operand and M result, spike
    lockstep), plus timer-interrupt and `mem_wait` variants.
- **Results, from clean** (`make clean-all && make run-all-full-parallel`):
  - peregrine 33/33 cells.
  - rv32um 8/8 and arch-test `rv32i_m/M` 8/8 (signatures equal to
    spike's and Sail's), on both builds.
  - rv32ui 42/42 and rv32mi 12/16, unchanged.
  - mext full: 2,005 M results and about 16,800 operands checked per
    interrupt variant; about 1,100 interrupts per run, none on an M
    instruction and about 960 on the instruction after one.
  - kestrel 66, merlin 60, gatling 45 and common-rv32i 12, the same
    counts as before the shared runner changed.
- **Mutation checks** (8 mutants, each rebuilt from clean, restored and
  byte-compared; each failure read for its reason):
  - mul-high negation carry dropped; divide-by-zero early-out removed;
    remainder given the quotient's sign: caught by the unit test, rv32um
    and arch-test.
  - Unit not cancelled by a MEM redirect: caught by the shadow check
    (x29 read stale). This needed the ecall handler to change the
    operand: the same instruction re-executed with the same operands
    hides it.
  - M instruction interruptible: the livelock, a timeout.
  - RVFI operands not latched: caught by the shadow check.
  - The ID interlock bubble overwriting the held M instruction: caught by
    the load-then-M-then-branch and CSR-around shapes.
  - No EX/MEM bubble during the hold: caught by mext and rv32um.
- **P8 measurement** (one seed, the same 5,941-instruction mext program,
  34 % M instructions, so a stress mix and not a benchmark): 54,419
  cycles iterative (CPI 9.16) against 22,737 with `MUL_DSP=1` (CPI 3.83).
- **Independent RTL review** (rds-rtl-review, 2026-11-24): no defects.
  - Risk: the `MUL_DSP=1` product is combinational between registers
    that sit behind muxes, so the DSP cannot absorb a pipeline register.
    It may miss 100 MHz on xc7a100t-1. To be measured at stage 7 (P14).
    A fix adds a stall cycle and changes P8's 2.
  - Cancel after start is unreachable in the core today: MEM holds only
    bubbles once the unit runs. Only the unit test covers it. It becomes
    live if a later stage lets MEM fill during the hold.
  - The new M muxes select on unreset payload, so 4-state simulation
    shows X on bubbles. Every consumer is gated by valid, per the
    pipeline-register convention.
- **Lessons.** Handbook
  [precise-trap-checks](../../../../../../../handbook/dv/precise-trap-checks.md)
  (multi-cycle units section) and
  [interrupts-must-not-discard-finished-work](../../../../../../../handbook/design/interrupts-must-not-discard-finished-work.md).

## Stage 3: the predictor (done 2026-11-24)

Owner, 2026-11-24: "Push and continue".

- **`peregrine_bpred`** (new FUB, own filelist).
  - Direct-mapped BTB: 32 entries, full tag, target, unconditional bit.
  - BHT: 256 2-bit counters indexed by PC[9:2].
  - `BP_EN=0` instantiates nothing and never predicts taken.
  - A non-branch that hits the BTB (a stale entry after rewritten code)
    clears its entry.
  - Only the BTB valid bits reset. The BTB payload and the BHT are
    LUTRAM. Installing a conditional entry writes its counter to weakly
    not taken (`01`) instead of stepping it, so no lookup reads a value
    nothing wrote (see the review below).
- **`peregrine_core`.**
  - IF fetches the predicted PC.
  - EX flags a mispredict (wrong direction, or a wrong target on a taken
    guess) and redirects to the resolved next PC: 2 bubbles. A correct
    taken guess costs 0.
  - The predictor is written once per instruction as it leaves EX: not
    under `mem_wait`, not during an M hold, not when a MEM redirect kills
    it.
  - An instruction held in EX redirects only as it leaves.
  - The guess and the flag are reported at retire (`rvfi_bp_pred_taken`,
    `rvfi_bp_pred_target`, `rvfi_bp_mispredict`).
- **DV.**
  - `test_peregrine_bpred`: the unit against an exact model, cycle by
    cycle, over a PC pool built to alias. Both `BP_EN` builds.
  - `test_peregrine_predictor`: the PRD §5 streams. Loops of trip count 1
    to 4, BTB and BHT aliasing pairs (the alias property checked from the
    linked symbols), JALR target changes, mispredicts with an ID interlock
    on the wrong path, a stale entry on an M instruction, a branch killed
    by a trap in EX, and the generated hazard programs.
    - Some streams run again under random `mem_wait`.
    - Every program runs on both builds, with the program's own result
      check, spike lockstep, the RVFI shadow check, and a per-instruction
      prediction check against the model under the states pipeline
      timing allows (BHT counters as value sets, because they carry over
      a reset).
    - The pytest wrapper then makes the A/B comparison.
- **Results, from clean** (`make clean-all && make run-all-full-parallel`,
  final RTL): 42/42 cells, 0 reruns, on the failing seed base 1764875541
  (replayed) and on a fresh one (1428106066).
  - A/B at full: with `BP_EN=0` every taken transfer mispredicts, as on
    merlin. With `BP_EN=1` the speedup is 1.32 / 1.18 / 1.28 / 1.35 on
    loop trip counts 1 to 4, 1.81 on `bht_alias`, 1.33 on `jalr_targets`
    and `btb_alias`, 1.04 on `interlock`, 1.05 on `trap_shadow`, and
    1.005 on the generated programs. The table is
    `logs/predictor_full/predictor_ab_full.txt`.
  - One gate cell failed before the replay: `generated`, x26 wrong. spike
    failed the same program, so it was a stage-2 generator bug, not the
    core: `csr_around` let an M instruction read the register holding
    `mie`, which the generator does not model. Fixed in
    `mext_program.py`.
  - No shared file changed in this stage, so kestrel, merlin and gatling
    are untouched.
- **Mutation checks** (9, each rebuilt from clean, restored and
  byte-compared, each failure read for its reason; the final pass ran on
  the final RTL and streams, all 9 caught):
  - BHT counter moving against the outcome; stale-entry kill removed; BTB
    tag not compared: caught by the unit test and the streams.
  - Redirect during the M hold: wrong result on `stale_entry`.
  - Predictor written by a trap-killed instruction: `trap_shadow`.
    Caught by the first version (alternating direction), then **survived
    once installs wrote `01`**: the killed copy's update lands before the
    re-executed copy's lookup, and both counters re-converge at 00 on
    every not-taken pass. Caught again after the stream changed to T, T,
    N, N.
  - Install stepping the old counter (the review finding): caught by the
    unit test's randomized initial memory.
  - Wrong-target guess not flagged: `jalr_targets`.
  - Fetch ignoring the guess: wrong result.
  - Predictor written during `mem_wait`: **survived the first pass.** The
    only `mem_wait` run was the generated program, whose branches mostly
    execute once. It was caught once `loop_trip3`, `interlock` and
    `trap_shadow` also ran under `mem_wait`.
- **Independent RTL review** (rds-rtl-review, 2026-11-24): no
  correctness defect.
  1. A real 4-state defect: installing a conditional entry stepped a
     counter nothing had written (X in Icarus or Questa; Verilator's
     2-state zeros hid it). The unit test now randomizes the initial
     memory contents (`--x-initial unique`, `+verilator+rand+reset+2`),
     which failed the old RTL on seeds 11, 22 and 33.
     - Fixed: an install writes a fixed value.
     - The first fixed value, weakly taken, passed every correctness check
       but lost to predict-not-taken on alternating branches: `loop_trip2`
       0.998x, `interlock` 0.982x.
     - Weakly not taken (`01`) is a zeroed counter after one taken step
       (the board's power-up behaviour) and wins on every stream. **A
       policy choice: flagged for the owner.**
  2. "A function of the retired stream" was imprecise: an instruction
     that traps on its own exception, or is interrupted, also updated. The
     wording was fixed in the PRD, the core header and the model, and
     the model already replays trap beats.
  3. The EX mispredict redirect path is longer (target add, 32-bit
     compare, PC mux): added to P14's paths to watch at stage 7.
  4. `ram_style` sat under an `ifdef XILINX` no flow defines; now
     unconditional (the repo idiom).
- **Limit of the check.** On some beats the allowed states predict
  differently, so the check accepts either answer there: 400 of
  `loop_trip2`'s beats and about 1,600 of `interlock`'s at full, 0 on the
  generated programs. Pinning those down needs the lookup cycle modelled
  exactly.
- **Lessons.** Handbook
  [branch-predictor-checks](../../../../../../../handbook/dv/branch-predictor-checks.md).

## Stage 6: amber's hit latency, P13 (measured 2026-11-24)

- **Test.** `dv/tests/test_peregrine_amber_latency.py` runs amber's own
  pair rig (two ambers, the fabric, the bench AXI4 memory) at the l1_pkg
  default geometry (128 sets, 4 ways, 64 B lines, 64-bit bus). Every
  request goes through the rig's transaction path, so its model still
  checks the data. A pin monitor samples cache 0's CPU port mid-cycle.
  The first version sampled after the rising edge and saw no handshake
  at all, because by then the BFM had already moved valid.
- **Result (cycles from the accept):**

  | Access | Response valid | Port ready again |
  |---|---|---|
  | Read hit (S or M) | 4 | 3 |
  | Write hit (M) | 4 | 3 |
  | Write to an S line (CLEAN_UNIQUE upgrade) | 18 | 17 |
  | Read miss, write miss (bench memory) | 29 | 28 |

  The hit path is IDLE (accept), LOOKUP (tag read), HIT_RD or HIT_WR,
  IDLE with ready high, and then the response leaves the 2-deep staging
  FIFO. `l1_control` sends E and M writes down the same HIT_WR path. The
  rig's fabric answers a read miss shared, so no silent E-to-M write was
  timed here. The test asserts the hit numbers; the miss and upgrade
  numbers depend on the rig's fabric and memory, so it only reports them.
- **What it means (PRD §4.8).** A blocking MEM stage pays about 3 cycles
  per D$ access over a 1-cycle hit: about 1.1 CPI at 0.36 accesses per
  instruction, more than the whole miss term.
- **Decided (2026-11-24, owner: "b, please").** amber gains a pipelined
  hit path: cache-ip/amber-mesi-l1 TASK-005. Its target latency is set
  together with stage 4's MEM design: 1 cycle keeps a single MEM stage, 2
  needs M1/M2 or one stall per access.
- **Landed (2026-11-24, owner: "1-cycle").** TASK-005 closed: a read hit
  is valid 1 cycle after the accept and the port accepts every cycle; a
  write hit is 1 / 2. The test asserts (1,1), (1,1), (1,2). Stage 4
  consequence: a load issues from EX and has its data in MEM; a store
  issues from MEM (an older instruction can still trap there). Budgets
  left at 10 ns (amber OOC, 0 ns I/O delay): +2.60 ns in front of the
  request (peregrine's address ALU), +2.27 ns after `cpu_rsp_rd_data`.

Next: stage 4, the caches and fabric, which depends on cache-ip/amber-mesi-l1
TASK-004 (`fence.i`); TASK-005 (hit path) is done.
