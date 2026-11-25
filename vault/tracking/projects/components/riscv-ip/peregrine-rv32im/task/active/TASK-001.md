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
       (the board's power-up behaviour) and wins on every stream. A
       policy choice, flagged for the owner; **approved 2026-11-25
       (owner: "Keep 01").**
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

## Stage 4: caches and fabric (done 2026-11-24)

Owner, 2026-11-24: "start amber TASK-004, then stage 4". amber TASK-004
(the CPU-side clean-all) runs in parallel in cache-ip; this pass builds
everything in stage 4 that does not need it, with the D$ slot stubbed.

- **Blocks (all new, peregrine `rtl/`, each with a `.f`):**
  - `peregrine_icache` (P9): direct-mapped 4 KiB, 64 B lines, read-only,
    one AXI4 read master (whole-line INCR burst, one replay cycle), an
    invalidate-all (`inv_req` / `inv_ack`, taken between refills). The
    hit test runs on the registered PC (valid flops, tag LUTRAM); the
    data RAM is sync-read at `imem_addr_next`. Nothing to reuse in the
    tree: no other core here has an I$.
  - `peregrine_axi4_arb` (P7): 3 masters (I$, D$, uncached) onto one
    fabric port. AR and AW each use `arbiter_round_robin` (rtl/common) in
    ACK mode; R and B route by an id prefix (fabric id = {master, id});
    W follows AW by serializing writes (an AW grant blocks the next one
    until wlast), so no W-order FIFO. No N:1 AXI4 merge exists in rtl/amba
    (only the vendored pulp `axi_mux`).
  - `peregrine_clint` (P7): msip / mtimecmp / mtime at the SiFive offsets,
    1-cycle register port, `MTIME_DIV`, registered `irq_timer`.
  - `peregrine_uc_axi`: one 32-bit load or store at a time as a
    single-beat AXI4 transaction; stores wait for B (not posted).
  - `peregrine_top`: the cached build: core at `CACHE_EN=1`, the I$ on
    the fetch path, the D-side decode and handshake, the CLINT, the
    uncached port, the arbiter.
- **Core (`peregrine_core`, new parameter `CACHE_EN`, default 0).** At 0
  the core is the stage-3 core: fence.i is a no-op, the two new outputs
  (`dmem_req_pre`, `fencei_req`) are 0, the interrupt lock is a constant
  0. The cacheless suite (`peregrine_tb_top`) is unchanged and green. At 1:
  - fence.i raises `fencei_req` in MEM and waits under the wrapper's
    `mem_wait` while the wrapper cleans the D$ and invalidates the I$;
    then it commits and redirects to pc + 4, flushing everything younger.
  - a load, store or fence.i that presented its request during a hold is
    not interruptible on the cycle the hold drops, so the D-side request
    never falls before its handshake (the GAXI rule amber's port needs).
- **D-side shape: loads stay in MEM (revises the stage-6 note above).**
  The stage-6 note said a load issues from EX with its data in MEM. Built
  instead: every load and store issues in MEM from the EX/MEM register and
  takes its data in WB, the stage-1 registered-read contract unchanged.
  amber's 1-cycle hit fits it exactly (accepted in MEM, the response
  valid in WB), with no added stall and the same load-use bubble as
  today. Issuing from EX would buy nothing and put peregrine's ALU in
  front of amber's tag LUTRAM and compare (the +2.60 ns budget). The
  request address is a flop.
- **Address map (P7).** CLINT 0x0200_0000-0x0200_FFFF; uncached I/O
  0x1000_0000-0x1FFF_FFFF; everything else RAM (cacheable). The window is
  bounded because the riscv-tests and arch-test images link at
  0x8000_0000 (battery `LINK_BASE`) and must be cacheable; the owner
  amended P7 to match (2026-11-24, "Amend P7").
- **Stubbed until amber (marked `TODO(TASK-004)` in `peregrine_top`).**
  - The D$: the cacheable window goes through the uncached port; arbiter
    port 1 is idle. amber's `m_axi` read/write masters go on port 1, its
    snoop port tied idle, its CPU GAXI port on the D-side handshake
    (valid/ready request, response the next cycle on a hit).
  - The fence.i D$ clean: done the cycle it is asked (the stub has no
    dirty line). Expected from TASK-004: a clean-all op on amber's GAXI
    request, answered after the last write-back's B; the wrapper
    sequence is already clean, then invalidate, then release.
- **Test hook.** `peregrine_top` has `tb_irq_software` / `tb_irq_timer`,
  ORed into the CLINT's; systems tie them 0. It lets the stage-1
  pin-driven interrupt suite run on the cached build.
- **Tests (Pattern B, gate/func/full).**
  - `test_peregrine_icache`: directed phases with exact refill counts
    (cold sweep 64, warm 0, conflict 16 of 16, invalidate 64 again, an
    invalidate raised mid-refill acked only after it), then a random
    stream on a slow memory; every fetched word checked against the AXI4
    slave BFM's MemoryModel. The first monitor sampled after the rising
    edge and counted 0 refills while every word checked; it now samples
    mid-cycle.
  - `test_peregrine_axi4_arb` (harness `peregrine_axi4_arb_th`): three
    house AXI4 masters, one house AXI4 slave; at func a slow fabric with
    out-of-order, beat-interleaved R. Every read checked against its
    master's model; a monitor checks R/B routing by id and W order.
  - `test_peregrine_clint`: against a cycle model, `MTIME_DIV` 1 and 3.
  - `test_peregrine_sys` (`peregrine_sys_tb_top`: `peregrine_top` on a
    behavioral AXI4 memory, the same port list as `peregrine_tb_top`):
    rv32ui (with `fence_i`), rv32um, rv32mi with spike lockstep at func;
    a 15% random memory-stall soak; `irq_basic.s` (pin-driven) and the new
    `clint_basic.s` (CLINT timer and software interrupts, mip.MTIP, and
    fence.i over a store to .text). `PeregrineSysTB` stops on the tohost
    store's retire (the cacheless TB's fixed 4-cycle window counted one
    extra loop store on the cached build) and checks the D-side request
    contract.
  - **Known gap:** with the stub D$, the D-side request never waits (the
    uncached port is always idle when the wrapper presents one), so the
    contract monitor saw 0 waiting cycles and the interrupt lock is not
    exercised. Both become live with amber (write hits hold ready one
    cycle, misses many).
- **Timing paths created (stage 7 to measure):**
  - fetch: PC flop -> I$ tag LUTRAM -> compare -> `stall` -> `mem_wait` ->
    the core's `pc_d` mux -> the I$ data RAM read address. The longest new
    path; the RAM address mux is also fed by the EX redirect and the
    predictor.
  - D side: EX/MEM `alu_y` (a flop) -> decode -> amber's tag LUTRAM and
    compare (amber's +2.60 ns input budget is for this, and the address
    no longer comes through the ALU).
  - D ready (amber `cpu_req_wr_ready`, registers only) -> `mem_wait` ->
    every pipeline enable, and the `pc_d` mux into the I$ RAM address.
  - response data (amber RAM out -> `cpu_rsp_rd_data`, +2.27 ns) -> the
    wrapper's capture mux -> WB load align -> the regfile write and the
    WB->EX forward.
- **Mutation pass (14 mutants).** 13 caught after one round of test
  fixes; the first round left four alive, three of them test gaps:
  - *no replay cycle after a refill*: only a word on a line's LAST beat
    needs the replay, and every directed refill started at beat 0. Added
    the "last-beat miss" phase.
  - *no response capture while the core holds*: hidden because the
    uncached port held `rsp_rdata` until its next response. amber's
    response data does not hold, so the port now drives 0 outside the
    `rsp_valid` cycle (registered, no path cost); rv32ui `lw`/`sw` then
    catch it.
  - *fence.i does not redirect*: both fence.i tests ran the patched code
    behind a jump, fetched after the invalidate anyway. `clint_basic.s`
    test 6 patches the instruction right after fence.i.
  - *interrupt lock removed*: survives, as expected (the known gap above:
    the stub D$ never makes a request wait).
  Caught as written: invalidate not clearing valid, tag not compared, AW
  granted while W is owed, R to master 0, B routed by grant, timer `>`,
  mtime write vs tick, store strobes on lane 0, request accepted while
  held, fence.i skipping the invalidate.
- **Results (2026-11-24, clean-all, 0 reruns).** Area FUNC 47/47 twice,
  seed bases 4106925726 and 1943782932 (the second after the test fixes):
  the cacheless suite unchanged, plus icache, axi4_arb, clint x2, sys x5,
  each at gate and func. Area FULL 70/70, seed base 2540653139.
  The first FULL run (seed base 146514292) failed one cacheless cell, battery
  rv32um `div` at full: "lockstep: no spike commit at the ELF entry". Not
  the RTL: the battery's work directory was per suite, not per level, so
  the func and full cells (running in parallel) wrote the same
  `spike_rv32um_div.log` and the full cell parsed the func cell's
  half-written log. `test_peregrine_battery`, `test_peregrine_irq` and
  `test_peregrine_sys` now put the level in the work directory (mext and
  arch already did); the FULL rerun above is clean.

### Part 2: amber as the D$ (2026-11-24)

amber TASK-004 (da9e8df71) and part 1 (f0f49a62c) committed; this pass
replaces the stub.

- **amber in `peregrine_top`.** `amber_top` with `MAINT_EN=1`, l1_pkg
  default geometry 128 sets x 4 ways x 64 B = 32 KiB (the geometry P13
  was measured at; new parameters `DC_SETS` / `DC_WAYS` / `DC_LINE`),
  `BUS_WIDTH = AXI_DW` = 64, so no width converter: the 32-bit word rides
  its lane (`be = wstrb << 4*lane`, `wdata` replicated) and the response
  lane is selected by the address bit registered at the accept. Its AXI4
  master is arbiter port 1; the ACE snoop port is tied idle (one core);
  `USE_MONITOR=0`; `cpu_rsp_rd_ready` = 1 (the wrapper captures a
  response that arrives while the core holds).
- **Clean engine.** One clean-all ({maint=1, we=0}) in flight, issued only
  with no access outstanding, done on amber's response (after the last
  WriteClean's B). Sources: fence.i (then the I$ invalidate, then the
  release, as part 1 built), and a new `dc_clean_req` / `dc_clean_done`
  hook (TB / debug; tie 0), which `peregrine_sys_tb_top` exposes as
  `tb_dc_clean_*`. The core is held while either is pending.
- **amber installs every read fill Shared** (its AXI4 plane sees no
  IsShared), so the first store to a line a load brought in pays a
  CleanUnique upgrade, a 1-beat AR the memory answers. Correct on any AXI4
  memory; a performance cost of the single-core system. An "install E when
  the system has no other cache" option would be an amber change (not
  made; cache-ip scope). **Filed** (owner 2026-11-25, "File an amber
  task"): cache-ip/amber-mesi-l1 TASK-006, install E on IsShared = 0.
- **Tests added.**
  - `smc_basic.s` (`test_peregrine_sys` smc): code written with stores
    (dirty in amber) runs only after fence.i: new code across three
    lines; rewriting code the I$ holds; a store that upgrades a line a
    load brought in; data of every size across a clean; WAYS + 2 dirty
    lines in one set (evictions, then a clean).
  - `io_basic.s` (io): the uncached window on both lanes at every size;
    the window bypasses amber (an aliased RAM store sits dirty in amber
    while the I/O load sees the old memory word until fence.i); an
    uncached load whose response lands while an I$ refill holds the core.
  - `irq_lock.s` (irq_lock) with an aimed interrupt source: the timer is
    raised in the sample where a D request is valid and not ready, so the
    interrupt is pending in the cycle that request's hold drops. With
    amber a request waits on ready only behind a write hit (amber accepts
    a miss at once and the core waits on the response, not on ready), so
    the program pairs a write hit with a load of the same word.
  - riscv-arch-test `Zifencei` (Fencei) added to the shared
    `common-rv32i/dv/arch_test/rv32_arch_test.py` (additive: `EXT_ISA` and
    the gate list); `test_peregrine_arch` gains cached cells (M, Zifencei
    on `peregrine_sys_tb_top`; `ArchSysTB` cleans amber after the tohost
    store, before reading the signature from memory).
- **Cacheless fence.i redirects (owner 2026-11-25, "Give it the
  redirect").** As the stage-3 no-op, instructions already in the pipeline
  behind a fence.i ran stale at `CACHE_EN=0`: Fencei failed 2 of 6
  signature words on `peregrine_tb_top` (measured 2026-11-24). Now fence.i
  commits in MEM and redirects to pc + 4 in both builds (`fencei_req`
  stays 0 at `CACHE_EN=0`, there is nothing to clean), and the cacheless
  Zifencei arch cell is in. `bpred_model` counts fence.i as a redirect
  (the next instruction is fetched after it resolves).
- **Mutation pass, rerun with amber (18 mutants).** 17 caught. Part 1's
  survivor is now caught: *interrupt lock removed* gives 161 dropped
  requests on irq_lock (aiming at the store handshake instead caught none,
  measured). Two part-1 mutants that had been caught survived the first
  run with amber, because their path left rv32ui: *uncached store strobes
  on lane 0* and *no response capture while held* (cacheable RAM no
  longer goes through the uncached port, and amber's response data stays
  stable while the core holds); io_basic catches both. New D$ mutants:
  clean stubbed out (smc, Zifencei, rv32ui `fence_i`), response lane not
  selected, store strobes not shifted (rv32ui) caught. Survives, as an
  equivalent: *clean issued while an access is in flight* (amber is
  blocking; it cannot accept the clean before answering). A sixth, *the
  clean's response taken as a data response*, was equivalent by
  construction (a response counts only with `r_outstanding` set), so the
  mask was removed from the RTL instead.
- **Results (clean-all, 0 reruns).** FUNC 57/57, seed base 1677929868;
  FULL 85/85, seed base 3310830104. Includes the cacheless suite
  unchanged, `test_peregrine_amber_latency`, rv32ui (with `fence_i`) /
  rv32um / rv32mi in spike lockstep with the stall soak on the cached
  build, irq_basic, clint_basic, smc, io, irq_lock, and cached arch-test
  M 8/8 and Zifencei 1/1 at full. The first FUNC run (seed base
  3333699153) failed only the cacheless Zifencei cells, above.
- **OOC timing (P14 measurement, not a gate; xc7a100t-1, 10 ns,
  `peregrine_top`, scratchpad builds).** WNS -9.277 ns (3 builds: -8.5 to
  -9.3), TNS -7011 ns over 3,755 endpoints; 5,137 LUT / 2,894 FF / 9
  RAMB36 / 922 LUTRAM. The failing families, worst first:
  - amber response -> core: amber's LRU / victim / data-way select ->
    `cpu_rsp_rd_data` -> WB load align -> WB->EX forward -> branch
    compare -> mispredict -> `pc` and the I$ RAM address: -8.9 ns, 24
    levels. The 1-cycle hit leaves the response late in the cycle, and
    peregrine forwards it into EX's branch resolve in the same cycle.
  - core -> amber: PC -> I$ tag LUTRAM -> hit -> `w_other_hold` ->
    the D request valid -> amber's accept-cycle classify -> its data RAM
    address: -8.1 ns, 22 levels (part 1's run had the same path from
    `mie` through the interrupt decision into the request valid).
  - inside the core: PC -> I$ hit -> `mem_wait` -> pipeline enables
    (MDU accumulator, mepc / mscratch, regfile write): -4.6 ns.
  - fetch: I$ tag -> hit -> stall -> `pc_d` -> I$ data RAM address:
    -3.3 ns, 12 levels.
  Structural, for stage 7: the hold (`mem_wait`) and the D request valid
  are combinational from the I$ hit and the interrupt decision, and
  amber's response is consumed by a same-cycle forward. Registering the
  load response in WB (one more load-use cycle), or a 2-cycle hit, and
  making the D request valid and the hold come from flops, are the
  candidate fixes.

Next: stage 5 (targeted formal; riscv-formal on `CACHE_EN=0`) and stage 7
(timing at 100 MHz, from the measurement above).

## Stage 7: timing, P14 (done 2026-11-25)

Owner, 2026-11-25: "Commit, then start stage 7". Phase 1 removes paths
that are not architectural, with no cycle-count change; phase 2 measures
the options for the D$ response path and leaves the choice to the owner.
All builds: `peregrine_top` out of context, xc7a100t-1, 10 ns, from a
snapshot of the tree (scratchpad), no I/O delays. Single builds move a
core path by up to 1.5 ns while amber's paths dominate placement, so each
step is judged by its own path group, not by WNS alone.

**Reference: amber on this part.** `amber_top` alone (`MAINT_EN=1`, no
monitor) at 10 ns on xc7a100t-1: WNS -4.046 ns, its own control state into
its data RAM's B address (on xc7k325t-2 the same build had +0.357). Inside
`peregrine_top`, with the snoop port tied idle: amber-internal -4.3 to
-4.9 ns; amber's accept-cycle cone (request valid -> tag LUTRAM address
mux -> compare -> `state_d` -> data RAM address) is about 11.7 ns by
itself; its response data (`cpu_rsp_rd_data`, way select behind the LRU /
victim state) arrives 10.4-11.1 ns after the edge. None of these can be
closed from the peregrine side.

**Phase 1 steps** (CPI harness: 6 self-checking kernels plus the rv32ui and
rv32um images on `peregrine_sys_tb_top`, cycles compared to HEAD 8658fea13
per program):

| step | change | WNS | groups moved | cycles |
|---|---|---|---|---|
| base | stage 4 as committed | -9.277 | | |
| 1 | I$ tag read registered at the next PC with the data, write-first | -9.949 | the tag LUTRAM off the hit compare | identical |
| 2 | D request no longer gated by the I$ stall: an access may be accepted while the core is held (`r_mem_done`); a response for MEM's access waits in `r_mem_have` and moves to WB with it | -9.974 | I$ -> D$ gone (was -8.2); I$ -> core -4.6 -> -2.7 | 17 fewer in 4 rv32ui images (30 accepts under a hold) |
| 3 | branch / JAL target and its compare against the guess computed in ID (`br_target`, `br_tgt_hit`); `mem_redirect_nw` (the MEM redirect without its `~mem_wait`) for the PC mux, flushes, M-unit start and predictor write | -5.036 | load data no longer reaches the PC: D$ -> core -8.4 -> -4.6 (now ends at EX/MEM) | identical |
| 4 | I$ read registers take `mem_wait` as their enable and read at `imem_addr_next_nw` (the next PC without the hold); the replay cycle reads at the PC; valid read straight from flops | -5.055 | D$ -> I$ -3.3 -> +0.28, I$ -> I$ -1.3 -> +0.44 | identical |
| 5 | JALR guess checked without the target adder (`rs1 == pred_target - imm` or `+ 1`, `jalr_x` from ID); M-unit payload loads on every idle cycle | -5.017 | the M-unit start path gone; core groups within noise | identical |

After step 5, with amber's paths relaxed to two cycles (a measurement
constraint standing in for a 2-cycle amber), the core-only groups are
core -> core -0.72, core -> I$ -0.97, I$ -> core -0.15 ns: the core itself
is about 1 ns short, through `mem_wait` (I$ hit, D handshake, interrupt
decision) and its fanout to the pipeline enables and CSR write enables.

**Phase 2: the D$ response options** (built on step 5; CPI from the same
harness; kernels without `mm`, whose iterative multiply dominates it):

| option | what | D$ data path | D$ -> core group | CPI kernels | CPI rv32ui |
|---|---|---|---|---|---|
| none (step 5) | load data forwarded WB -> EX the cycle it arrives | -5.017 (into EX/MEM) | -5.017 | 1.343 | 1.989 |
| (a1) | response registered in `peregrine_top`, every load one more cycle | -0.230 (at the register) | -1.409 (ready -> `mem_wait`) | 1.487 (+10.7%) | 2.017 (+1.4%) |
| (a1s) | every response registered (loads and stores) | as (a1) | | 1.515 (+12.8%) | 2.024 (+1.7%) |
| (c) | no WB -> EX forward of a load: ID waits while it needs a load still in MEM, and reads it through the WB -> ID bypass | -1.761 (regfile write) | -1.761 | 1.429 (+6.4%) | 1.998 (+0.4%) |
| (a) proper | response registered and only load-use pays (a sixth stage for loads) | about (a1) | | as (c), +6.4% (same stalls by construction) | as (c) |
| (b) | amber 2-cycle hit (cache-ip change, not built) | see below | | about (a1) to (a1s), +10.7 to +12.8% | +1.4 to +1.7% |

Per kernel, (c) against none: `sum` +15.9%, `list` +11.7%, `sort` +0.4%,
`memcpy` +13.3%, `crc` +1.6%. (a1) and (c) cost the same where every load
is used by the next one or two instructions.

(a1) and (c) both stay negative because amber's response arrives about
11 ns after the edge: registering it at once (a1) misses at the wrapper
flop, writing the regfile (c) misses at its write port. (b) is what removes
it. What amber would need, from the jet-prime precedent (delta 04, TASK-002,
a 2-cycle hit at 100 MHz on Kintex): capture the request in the accept
cycle and classify a cycle later from the registered tag read (no
`state_d` behind the arriving valid), read every way's data at the arriving
`{set, beat}` keyed off the valid alone, and register the selected word
(or the RAM output) before `cpu_rsp_rd_data`. That also takes amber's
accept-cycle cone (core -> D$, -4.1 to -4.8) and its internal state ->
data-RAM path (-4.0 standalone) toward closure; neither is peregrine's.

**Verification of phase 1** (none committed yet):
- Tests changed: the I$ unit TB drives the new fetch contract
  (`fetch_addr_next_nw` + `hold`) and adds holds the cache did not cause
  (30% in two directed phases, 20% in the random phase); the predictor
  test adds `stale_target` (a rewritten JAL fetched with a taken guess at
  the old target) and `jalr_odd` (a JALR whose rs1 + imm is odd), each with
  a per-beat check. `peregrine_tb_top` ties the new `imem_addr_next_nw`.
- Mutation (`mutate7.py`, scratchpad: the stage-4 set re-anchored plus 10
  stage-7 mutants): 25 of 27 caught. Stage-7 mutants caught: MEM's access
  re-issued after an accept under a hold; I$ read registers ignore the
  hold; replay reads the next PC; replay read not enabled; branch / JAL
  target compare from ID ignored and JALR `jalr_x + 1` dropped (both only
  after the two new streams; they survived the first pass); M-unit payload
  reloads while its result waits; ungated redirect drops fence.i. D2
  (clean issued while an access is in flight) survives as at stage 4, an
  equivalent. S2 *MEM's early response not handed to WB* and S3 *MEM's
  early response captured as WB's* survived that pass; closed below.

**Decision (owner, 2026-11-25): keep amber's 1-cycle hit and the CPI;
lower the clock target instead.** Options (b) and (c) are not built. The
phase-1 changes stay.

**S2 / S3 closed.** Measured first, on the CPI harness: all 30 early
responses (an access accepted while the core was held) were amber's, 10 of
them loads, and in all 10 amber still drove the captured word on the cycle
WB read it -- amber keeps its last response on `cpu_rsp_rd_data`, so a
wrapper reading it late passes by luck. The uncached port and the CLINT
already drive 0 outside their valid. Fix, TB only: `peregrine_sys_tb_top`
parameter `RSP_SCRAMBLE` (default 0) forces amber's response beat
(`u_top.w_dc_rsp_data`) to an LFSR value whenever its valid is low, and
passes amber's own value in the valid cycle (re-derived from
`l1_cpu_frontend`'s response mux, since the port net is the forced one).
The force sits upstream of peregrine_top's lane select: a first version
that forced the selected word replaced the lane mux and let *response lane
not selected* (D3) survive. On: `test_peregrine_sys` and the cached
`test_peregrine_arch` cells. With it the held word matches at WB's read 0
of 10 times, all 57 CPI programs pass, cycle counts identical. No RTL or
cache-ip change.

**Clock reached** (step 5, `MUL_DSP=0`, OOC xc7a100t-1,
`set_clock_uncertainty -setup 0.2`; Vivado reports 0.235 ns total):

| period (ns) | MHz | WNS | WHS | worst |
|---|---|---|---|---|
| 15.5 | 64.5 | -0.684 | | CLINT `msip` -> amber data RAM address |
| 16.0 | 62.5 | -0.607 | | `mie` -> amber data RAM address |
| 16.67 | 60.0 | -0.043 | | amber state -> its data RAM address |
| **17.0** | **58.8** | **+0.331** | +0.086 | amber state -> its data RAM address |
| 17.5 | 57.1 | -0.051 | +0.043 | amber state -> its data RAM address |
| 18.5 | 54.1 | +0.100 | +0.043 | amber state -> its data RAM address |
| 18.5, `MUL_DSP=1` | 54.1 | +0.342 | | |

Highest closing: 17.0 ns (58.8 MHz), 5,064 LUT / 3,004 FF / 9 RAMB36 /
922 LUTRAM. Top path groups there: amber internal (state -> data RAM B
address, 20 levels) +0.331; core -> amber (`mie` -> interrupt decision ->
request valid -> amber accept-cycle lookup -> data RAM address) +0.495;
amber -> core (response -> load align -> forward -> ALU -> EX/MEM) +0.637.
Every peregrine-only group has 3.5 ns or more. The sweep is not monotonic
(17.5 fails by 0.051 where 17.0 passes by 0.331): placement noise near the
edge is above the 0.2 ns budget, and all three binding groups are amber's
paths or pass through amber. 18.5 ns closes with and without `MUL_DSP`.

**Mutation, final** (`mutate7.py`, all 27, `RSP_SCRAMBLE` on): 26 caught;
S2 and S3 caught by rv32ui (gate and func), D3 by rv32ui. D2 (clean issued
while an access is in flight) survives, the stage-4 equivalent.

**Regression:** peregrine FULL, clean-all, 0 reruns, 88/88, seed base
2050116747. kestrel / merlin / gatling: no file changed.

**Target (owner, 2026-11-25): 18.5 ns, 54.1 MHz** ("54.1 MHz / 18.5 ns").
It closed in both multiplier builds (`MUL_DSP=0` +0.100, `MUL_DSP=1`
+0.342) with 0.2 ns of uncertainty; 17.0 ns was rejected because 17.5 ns
failed, so the edge is inside the placement noise. peregrine has no
PeakRDL config CSRs, so there are no config false paths to add. PRD P14
records the period. amber's limiting paths are filed as
cache-ip/amber-mesi-l1 TASK-007 (open, not scheduled). Stage 7 is done;
stage 5 (formal) is what remains of this task.
