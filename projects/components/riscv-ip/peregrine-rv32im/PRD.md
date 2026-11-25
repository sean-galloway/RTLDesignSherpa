# PEREGRINE PRD — Advanced In-Order RV32IM

**Version:** 0.2 (2026-11-23 — P5–P14 ruled (Sean); all fourteen
decision rows now DECIDED)
**Date:** 2026-11-23
**Design source:** [riscv-falcon-suite design spec](../../../../docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md),
rung 3. Where this PRD narrows a choice the spec left open, the row says
so and waits for the owner's name and date.

---

## 1. Purpose

The fastest falcon: speculation, traps and the memory hierarchy. peregrine
is **merlin's pipeline extended**. It keeps the same five stages, the same
forwarding unit and the same load-use and load-to-branch interlocks. Four
things are added, and each is a lesson:

1. **Speculation.** A BTB and a 2-bit bimodal predictor fetch down the
   predicted path; a misprediction flushes it.
2. **Precise traps.** A machine-mode CSR file, real exception delivery
   through `mtvec`, and interrupts from a CLINT-shaped block. kestrel's and
   merlin's halt contract is retired.
3. **The M extension.** An iterative multiply/divide unit that the M
   instruction holds in EX until it is done: the structural-hazard
   lesson (P3, revised 2026-11-23).
4. **The memory hierarchy.** Split blocking L1s behind AXI4 masters onto
   the repo fabric, with MonBus visibility.

Two later consumers depend on what peregrine chooses:
- **gyrfalcon** reuses peregrine's predictor, trap machinery, L1s and AXI
  fabric (spec rung 4). Its baseline ISA is peregrine's RV32IM exactly, so
  every peregrine battery has to carry over unchanged.
- **hive-serv HIVE-C** names peregrine as the successor `CORE_FLAVOR` to
  VexRiscv (hive-serv PRD §10.3). The LDR testplan becomes peregrine's
  system bring-up test on the day the RTL exists.

## 2. Non-goals

- **No out-of-order execution and no superscalar.** The core is
  single-issue and in order. That is gyrfalcon's lesson.
- **No A, F, C or D extensions.** Atomics are gyrfalcon-A's, and F is
  garuda's.
- **No supervisor or user mode, no MMU and no PMP.** Machine mode only
  (spec goals). The caches are physically indexed by construction, so
  virtual-index aliasing cannot occur (COD gap G6; the book cites Handy
  §2.2.1 for why).
- **No full riscv-formal through the predictor and the traps.** Spec rung
  3 rules it disproportionate. Targeted formal replaces it, and P12 keeps
  the insn checks reachable on a cacheless build.
- **No non-blocking caches.** An in-order single-issue core has at most
  one memory access in flight, so jet's lockup-freedom would be invisible
  (amber PRD v0.8).
- **No performance target.** Clocks and area are reported, not chased
  (spec non-goal). The FPGA closure point is P14.

## 3. ISA — RV32IM + Zicsr + machine mode

- **RV32I** as in kestrel and merlin, with the `common-rv32i` blocks
  (`rv32i_decode`, `rv32i_imm_gen`, `rv32i_alu`, `rv32i_pkg`) reused.
  The M opcodes and the CSR and `mret` forms go into the one shared
  `rv32i_decode` behind elaboration parameters, not into a second decoder
  (P11).
- **M.** `mul`, `mulh`, `mulhsu`, `mulhu`, `div`, `divu`, `rem`, `remu`.
  The edge cases are pinned to the unprivileged spec's division table
  (COD gap G4, where COD §3.4 states the intent: "software must check the
  divisor"). Spike agrees with this table, and lockstep enforces it:

  | Case | `div` / `divu` | `rem` / `remu` |
  |---|---|---|
  | divisor 0 | all ones (−1 / 2^32−1) | the dividend |
  | `div`: −2^31 / −1 (overflow) | −2^31 | 0 |

- **Zicsr.** The six CSR instructions, with the machine-mode CSRs listed
  in P6.
- **Zifencei.** `fence.i` becomes real work: the I$ and the D$ are split
  (P9).
- **Traps.** These are the exceptions the spec names: illegal
  instruction, `ecall`, `ebreak`, and misaligned fetch, load and store.
  Load and store access faults (AXI SLVERR and DECERR) are added
  (P7). Interrupts are machine software, machine timer and machine
  external.

## 4. Microarchitecture

### 4.1 The pipeline

merlin's five stages, with the additions marked:

```
  IF : PC select (+ BTB/BHT lookup, predicted next PC); I$ access
  ID : decode, regfile read, imm_gen (+ CSR read, M-op issue check)
  EX : ALU, branch resolve (+ mispredict detect, M unit start)
  MEM: D$ access (+ trap commit point, CSR write)
  WB : regfile write, RVFI retire
```

merlin's forwarding (EX/MEM over MEM/WB, select computed in ID), its
load-use bubble and its load-to-branch interlock carry over unchanged.
peregrine is meant to diff against merlin as additions only.

### 4.2 Branch prediction

- **Lookup in IF.** The PC indexes a direct-mapped BTB, which holds a tag
  and a target, and a BHT of 2-bit saturating counters (COD Fig 4.65,
  verbatim). On a BTB hit with the counter in a taken state, the next PC
  is the BTB target; otherwise it is PC+4. JAL and JALR go in the BTB as
  well. JALR targets are predicted with no return-address stack (P5).
- **Resolve in EX**, as in merlin. A misprediction (wrong direction, or
  wrong target on a BTB hit) flushes IF/ID and ID/EX: 2 bubbles, merlin's
  taken-branch cost. A correctly predicted taken branch costs **0**. This
  is the lesson. The penalty is now a function of the mispredict rate (COD
  gap G2): merlin pays 2 on every taken branch, and peregrine pays 2 only
  on a mispredict.
- **Update at EX resolution.** The counter and the BTB entry are written
  when the branch resolves, not when it retires. An update from a branch
  that a trap later squashes is harmless, because predictor state is not
  architectural. As built (2026-11-24), the write happens once per
  instruction as it leaves EX: not under `mem_wait`, not while an M
  instruction holds, and not when a MEM-stage redirect kills it. Every
  instruction that leaves EX retires, as an ordinary beat or as a trap
  beat (its own exception, or an interrupt taken at MEM), so the
  predictor state is a function of the retire stream including trap
  beats. That is what lets the DV hold every prediction to a model. An
  interrupted branch is the exception: it updated in EX with an outcome
  its trap beat does not report, so the model check runs without
  interrupts.
- **As built (TASK-001 stage 3, 2026-11-24).**
  - A non-branch that hits the BTB (a stale entry after the code was
    rewritten) mispredicts once and clears the entry.
  - An instruction held in EX by the M unit redirects only as it leaves:
    a flush during the hold would kill it in ID/EX.
  - The BTB valid bits reset. The BTB payload and the BHT are LUTRAM with
    no reset, so BHT counters carry over a core reset. A lookup reads a
    counter only on a hit of a conditional entry, and installing a
    conditional entry writes its counter to weakly not taken (`01`)
    instead of stepping it, so no prediction depends on a value nothing
    wrote. (The first build stepped it from its old value: X in a 4-state
    simulator. The independent review found it, and the unit test now
    randomizes the initial memory contents.) `01` is a zeroed counter
    after one taken step, the board's behaviour from power-up. Weakly
    taken (`10`) was measured first and made alternating branches
    mispredict every outcome: `loop_trip2` and `interlock` fell to 0.998x
    and 0.982x of predict-not-taken.
  - The prediction and the mispredict flag are reported at retire
    (`rvfi_bp_pred_taken`, `rvfi_bp_pred_target`, `rvfi_bp_mispredict`),
    beside `rvfi_trap_cause`.
- **Sizes (P5):** BTB 32 entries and BHT 256 entries, both
  elaboration parameters, plus a `BP_EN=0` build that falls back to
  merlin's predict-not-taken. The predictor drill (core_drills mode 3)
  and the book's accuracy table need the A/B that build gives.

### 4.3 Traps and the commit point

The trap is taken at **MEM**. The argument (Smith and Pleszkun 1988, the
in-order case):
- Memory is written in MEM, and the regfile is written in WB.
- An exception found in IF, ID or EX travels with its instruction in the
  pipeline registers as a cause code.
- When the instruction reaches MEM, it does not access memory. The trap is
  taken there: `mepc` and `mcause` are written, the PC goes to `mtvec`,
  and IF/ID/EX are flushed.
- The instruction in WB is older, so it retires. Nothing younger has
  touched memory, the regfile or a CSR.
- A load or store access fault arrives from the D$ in MEM, at the same
  point, so it is precise as well.
- CSR writes happen in MEM, so a CSR write never lands under an older
  trap. A CSR read in ID that follows a CSR write still in EX or MEM
  stalls until the write lands. The alternative is forwarding CSRs, and
  P6 decides.
- `mret` redirects at MEM in the same way.

Interrupts are sampled at the MEM boundary. A pending, enabled interrupt
is attached to the instruction entering MEM, which then traps instead of
executing ("precise at the oldest instruction", spec rung 3). An
instruction stalled in MEM on a D$ miss cannot take an interrupt until its
access completes, because the cache is blocking.

**An M instruction is not interruptible** (added 2026-11-23, TASK-001
stage 2). It reaches MEM only with its result done, and the interrupt is
taken on the next instruction instead, which is still precise: the
boundary falls between the M instruction and its successor, and `mepc` is
the successor's PC. The first stage-2 build let the interrupt take the M
instruction, discarding its 33 cycles of work. A timer re-raised 3 to 40
cycles after each acknowledge then caught every M instruction before it
retired: a livelock, measured in the directed suite. The cost is interrupt
latency: a run of back-to-back M instructions delays an interrupt by
about 34 cycles each. Kept as the simple solution for now (Sean,
2026-11-24: "do the simple solution first; we can reevaluate later"); the
alternatives are tracked in riscv-ip/peregrine-rv32im ISSUE-001.

### 4.4 M unit

- One iterative unit, `peregrine_mdu`, is started from EX. The spec's
  lesson is a structural hazard, so the unit is a single shared resource.
- **Hold in EX (P3, revised 2026-11-23, Sean: "Hold in EX").** The M
  instruction waits in EX until its result is ready. The PC, IF/ID and
  ID/EX hold, and EX/MEM takes bubbles. The result then writes back in
  program order, so RVFI stays exact and the riscv-formal insn checks P12
  relies on still apply. The busy scoreboard the spec described would
  have let independent instructions pass the divider, with the M result
  writing back after younger instructions retired; RVFI cannot report
  that write. That scoreboard is gyrfalcon's lesson now.
- **Operands.** The unit starts on the first EX cycle without `mem_wait`,
  when the forwarded operands are valid, and latches them. The
  forwarding selects go stale while the producers drain, so RVFI reports
  the latched operands too.
- **Latency (P8), in stall cycles with the M instruction in EX:**
  - Divide is radix-2 restoring (COD §3.4): a start cycle that captures
    the operand magnitudes, then 32 steps, so **33**. Divisor 0 and the
    signed overflow -2^31 / -1 take the early-out: **1**.
  - Multiply is radix-2 shift-add (COD §3.3): **33**. With `MUL_DSP=1` it
    is one registered 32x32 product: **2**. The option is the measured
    contrast, and it makes the structural hazard nearly disappear for
    multiplies.
  - The sign fixup is applied on the registered result, so the start
    cycle's negate sits after the forwarding mux, at about the ALU's
    depth.
- **Interaction with traps.** An M instruction raises no exceptions of its
  own. A MEM-stage trap or `mret` cancels the unit. Under hold-in-EX this
  can only happen in the M instruction's first EX cycle: after that, the
  instruction in MEM is a bubble. An M instruction is not interruptible
  (§4.3).

### 4.5 Memory hierarchy

- **D$ = amber**, the cache-ip blocking MESI L1. This was ruled in amber
  PRD v0.8 (2026-10-30): peregrine is amber's target client.
  - The CPU side is GAXI (amber D2), and the memory side is the AXI4
    read and write masters (amber D3).
  - The snoop port is tied idle: there is one core and no coherent peer.
  - Write-back with write-allocate is amber D5 and the spec's
    open-decision default. amber's `AMBER_WRITE_WT_NA` mode is the
    write-through escape hatch the spec names.
- **I$ (P9).** A small blocking read-only cache inside
  peregrine, `peregrine_icache`: direct-mapped, 4 KiB, 64-byte lines,
  one AXI4 read master, and no dirty state. A second amber was the
  alternative; it would carry MESI and a snoop port that an I$ never
  uses. The contrast between the I$ and the D$ is itself part of the
  lesson (COD §5.3 and gap G7: the split doubles the bandwidth, and write
  policy only matters on the D side).
- **`fence.i` (P10).** With a write-back D$, an I$ refill reads memory and
  misses dirty lines. `fence.i` therefore has to:
  1. clean the D$, writing back every dirty line;
  2. invalidate the I$;
  3. flush the pipeline.

  amber has no CPU-side maintenance request today: `l1_pkg` has snoop
  types but no clean or invalidate op on the CPU port. A "clean all" request
  is added to amber (cache-ip/amber-mesi-l1 TASK-004). Two alternatives
  exist: route I$ misses through amber's snoop port, or run the D$
  write-through. The rv32ui `fence_i` test and arch-test `Zifencei` are
  the gates.
- **Uncached window.** The CLINT, `tohost` and board I/O bypass the D$
  (P7).
- **Cacheless build (P12).** `CACHE_EN=0` replaces both caches with
  merlin's Harvard registered-read ports. That build runs the batteries
  fast, keeps riscv-formal's insn checks reachable, and isolates core bugs
  from cache bugs.

### 4.6 Bus and observation

- **AXI4 masters** go onto the repo fabric:
  - I$ read;
  - D$ read and write (amber's);
  - the uncached path.
- The path through the fabric to one memory port is P7.
- Observation uses `axi4_monlite` wrappers (spec dependencies; amber D8),
  never the heavyweight `_mon`.
- Core-side MonBus events: a mispredict, a trap (with its cause), and
  M-unit busy cycles. The perf model below needs these counts.

### 4.7 RVFI / retire

RVFI is driven at WB, in order, as in merlin. `rvfi_trap`, `rvfi_intr`
and the CSR fields for `mepc`, `mcause` and `mtvec` are added, so the
trap directed suite and the targeted formal can check trap entry against
the retire stream.

### 4.8 Performance model (COD gap G3)

These are predictions for MonBus to confirm or break. The book carries
the worked version, with measured miss rates replacing the assumed ones.

- CPI = 1 + (load-use bubbles + load-to-branch bubbles)/insn
  + 2 x mispredicts/insn + M busy stalls/insn + memory-stall cycles/insn.
- Memory-stall cycles/insn = (I$ miss rate + D$ accesses/insn x D$ miss
  rate) x miss penalty (COD §5.4).
- Worked example. Inputs:
  - **Assumed:** 2% I$ misses, 4% D$ misses, 0.36 D$ accesses per
    instruction (COD's §5.4 example values).
  - **To be measured on the TB memory model:** a 30-cycle penalty for a
    64-byte line fill.
  - Result: 0.6 + 0.43 = **1.03 stall cycles per instruction**.
  - At those rates, the caches alone roughly double merlin's CPI.
- If amber's hit latency exceeds one cycle (P13), every hit adds to the
  memory-stall term. That is the largest unknown in this model.
  **Measured (2026-11-24): 4 cycles.** With a blocking MEM stage that
  waits for the response, each D$ access holds MEM about 3 cycles longer
  than a 1-cycle hit would. At 0.36 accesses per instruction that adds
  about **1.1 cycles per instruction for hits alone**, more than the miss
  term above (1.03). The measured miss is 29 cycles on the rig's bench
  memory, against the 30 assumed. P13 chose a pipelined hit path in amber
  (cache-ip/amber-mesi-l1 TASK-005), so this term is the pre-change figure.

## 5. Verification

- **Batteries.** rv32ui (42/42 precedent), plus rv32um and rv32mi from
  `vendor/riscv-tests`. With real traps, the p-env's own trap handler
  replaces the halt contract: pass or fail comes from `tohost`.
- **riscv-arch-test** at the 3.10.0 pin, checked against spike and Sail,
  which must agree:
  - `rv32i_m/I`, `M`, `Zifencei` and `privilege`;
  - the DUT model halts on a `tohost` store, like the reference env,
    because `ecall` now traps.

  `common-rv32i` TASK-002 named M as peregrine's.
- **Spike lockstep** in the rds-dv cocotb flow, with RV32IM retirement
  compared per instruction.
  - Exceptions are synchronous, so lockstep covers them.
  - Interrupts are asynchronous. The TB raises them
    at a retire boundary it also tells spike about. Where that cannot be
    done, the directed suite checks them against RVFI (P12).
- **Trap and interrupt directed suite:**
  - every exception cause;
  - a trap in each stage, with an older instruction in WB and a younger
    store in EX;
  - an interrupt during a D$ miss, during an M-unit busy period, and on a
    mispredicted path;
  - nested `mret`.
- **Predictor stress streams:**
  - a loop of every trip count from 1 to 4 (the 1-bit/2-bit contrast);
  - aliasing pairs in the BHT and in the BTB;
  - JALR target changes;
  - a mispredict and a load-use interlock in the same cycle.
- **Targeted formal (SymbiYosys).** Three properties:
  - exception precision: no memory, regfile or CSR write by an
    instruction younger than a trapping one;
  - mispredict recovery: no instruction from the wrong path retires;
  - M-unit results equal to a reference function.

  Each property is mutation-checked. On `CACHE_EN=0`, merlin's
  riscv-formal insn checks also run (P12).
- **Arch-test gate on the D$.** amber's own grids verify amber. peregrine
  verifies the integration: fill, eviction and `fence.i` under the
  batteries.
- **Waves.** A house GTKW file from day one. The book needs three
  waveforms: a correctly predicted taken branch (0 bubbles) beside a
  mispredict (2), a trap entry, and an M-unit stall.

## 6. Decision rows

| # | Decision | Status | What it drives |
|---|---|---|---|
| P1 | Pipeline shape | **DECIDED (spec, rung 3):** merlin's pipeline extended, single issue, in order | everything |
| P2 | Predictor kind | **DECIDED (spec open-decisions row):** 2-bit bimodal + BTB, not 1-bit and not TAGE | IF, book, drill mode |
| P3 | M unit | **DECIDED (spec), REVISED 2026-11-23 (Sean, "Hold in EX"):** iterative multicycle, the M instruction held in EX until done (front end stalls behind it), not a busy scoreboard with late writeback: the scoreboard's late rd write is invisible to RVFI and breaks P12's insn checks. The true scoreboard is gyrfalcon's lesson | EX, hazard unit |
| P4 | Caches | **DECIDED (spec; amber PRD v0.8, 2026-10-30, Sean):** split blocking L1s, the D$ is amber, write-back + dirty bit | memory path |
| P5 | Predictor sizing | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"); built 2026-11-24:** BTB 32 entries direct-mapped, BHT 256 counters indexed by PC[9:2], no RAS, `BP_EN` parameter for the predict-not-taken A/B | IF area/timing, drill |
| P6 | CSR set | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"):** `mstatus` (MIE, MPIE, MPP fixed at M), `mie`, `mip`, `mtvec` (direct mode only), `mepc`, `mcause`, `mscratch`, `mtval`; read-only `misa`, `mhartid`=0, `mvendorid`/`marchid`/`mimpid`/`mconfigptr`=0; PMP CSRs with zero entries (`pmpcfg0-15`, `pmpaddr0-63` read 0, writes ignored: the spec makes them WARL, so a core without PMP still accepts them; added in stage 1, 2026-11-23); no Zicntr (gatling's 2026-10-21 precedent; cycle counts come from MonBus). CSR read-after-write stalls rather than forwards | decode, trap unit, rv32mi pass set |
| P7 | Address map and fabric | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"):** RAM cacheable from `RESET_ADDR` (kestrel's 0x0000_0000); CLINT at 0x0200_0000 in the SiFive layout (`msip` +0x0, `mtimecmp` +0x4000, `mtime` +0xBFF8) inside the core wrapper; 0x1000_0000-0x1FFF_FFFF uncached I/O (board UART and other MMIO), everything else cacheable. **AMENDED 2026-11-24 (Sean, "Amend P7"):** the row said "0x1000_0000 and up", but the riscv-tests and arch-test images link at 0x8000_0000 and must stay cacheable, so the window is bounded at 0x1FFF_FFFF. The sim TBs detect `tohost` from the store's RVFI retire, so a `tohost` in the cacheable image needs no uncached path; the I$, D$ and uncached masters merged by a small house AXI4 arbiter to one fabric port | TB top, hive-serv glue |
| P8 | M-unit latency | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"):** radix-2 for both (33 cycles), `MUL_DSP` parameter for a 1–2 cycle DSP multiply as the measured contrast. Built 2026-11-23: 33 stall cycles iterative, 1 on a divide early-out, 2 with `MUL_DSP=1` | CPI, book chapter |
| P9 | I$ | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"):** in-core `peregrine_icache`, direct-mapped 4 KiB, 64 B lines, read-only, one AXI4 read master; marked as the slot a cache-ip I$ would replace | IF, area |
| P10 | `fence.i` | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"):** D$ clean-all + I$ invalidate + pipeline flush; needs a CPU-side clean-all request on amber (filed as cache-ip/amber-mesi-l1 TASK-004, done 2026-11-24). The cacheless build (`CACHE_EN=0`) flushes and redirects too (owner 2026-11-25), so both builds pass Zifencei | amber, Zifencei tests |
| P11 | Decode growth | **DECIDED 2026-11-23 (Sean: "can't it have a param so there is one common file?"):** one `rv32i_decode` with parameters `M_EXT` and `ZICSR` (real CSR ops, `mret`, and trap causes in place of halt causes), both default 0. The new outputs (`m_op`, `csr_op`, `mret`) always exist and are constant 0 when their parameter is off, so kestrel, merlin and gatling elaborate the same logic they do today; their full suites and the common-rv32i unit tests are the proof. gyrfalcon's `A_EXT` and garuda's F decode extend the same file the same way | common-rv32i decode, its testplan and unit test; the three existing cores re-run unchanged |
| P12 | Cacheless build + formal reach | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"):** `CACHE_EN=0` gives merlin's Harvard ports; merlin's riscv-formal insn checks run on that build (with traps off via the formal harness); interrupts checked by the directed suite where lockstep cannot align them | DV plan, formal |
| P13 | amber hit latency | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"): measure first.** **MEASURED 2026-11-24 (TASK-001 stage 6): 4 cycles.** At amber's CPU GAXI port (pair rig, l1_pkg default geometry), a read or write hit's response is valid 4 cycles after the accept, and the port accepts again after 3: IDLE (accept), LOOKUP (tag read), HIT_RD/HIT_WR, IDLE, then the 2-deep response staging FIFO. A miss on the bench memory is 29. **Option (b) CHOSEN 2026-11-24 (Sean, "b, please"): amber gains a pipelined hit path**, filed as cache-ip/amber-mesi-l1 TASK-005; the target latency (1 cycle keeps a single MEM stage, 2 needs M1/M2 or one stall per access) is set there together with stage 4. **Implemented 2026-11-24 (TASK-005, target 1 cycle): a hit answers 1 cycle after the accept; read hits accept back to back (occupancy 1), a write hit holds the port 2.** The test now asserts those numbers. The rejected option was peregrine accepting the stall. Gate: `dv/tests/test_peregrine_amber_latency.py` asserts the hit numbers | CPI model, MEM stage |
| P14 | FPGA target | **DECIDED 2026-11-23 (Sean, "accept defaults on the rest"):** 100 MHz OOC on the Nexys A7 (xc7a100t-1), the riscv-ip ISSUE-001 anchor, with config CSR paths false-pathed per house rule; the predictor lookup and the trap redirect are the paths to watch; since stage 3 also the EX mispredict redirect (forwarded operand, target add, 32-bit compare against the predicted target, PC mux, fetch address), which the stage-3 review expects to become critical | timing, book |

## 7. Deliverables & sequencing

1. This PRD (ruled 2026-11-23). Implementation is riscv-ip/peregrine-rv32im
   TASK-001.
2. `peregrine_has` and `peregrine_mas` book skeletons. The heart of them is
   the predictor, trap and M-unit chapters.
3. RTL in stages, each gated before the next:
   1. merlin copied, with the CSR file and real traps added. Gate:
      `CACHE_EN=0`, rv32ui + rv32mi.
   2. The M unit. Gate: rv32um, arch-test M.
   3. The predictor. Gate: predictor streams, `BP_EN` A/B.
   4. The I$ and amber D$, the AXI fabric and the CLINT. Gate: everything
      at `CACHE_EN=1`, `fence.i`, the interrupt suite.
4. Targeted formal; riscv-formal on `CACHE_EN=0`.
5. Book: *Simplified RV32IM: peregrine — speculation and traps*, with
   predictor drill mode 3 in `core_drills`.
6. The hive-serv HIVE-C `CORE_FLAVOR=peregrine` swap, as the system
   bring-up.

## 8. History

- 2026-11-24: TASK-001 stage 4 done. amber (cache-ip/amber-mesi-l1,
  `MAINT_EN=1`, 32 KiB) is the D$ in `peregrine_top`; fence.i is amber's
  clean-all, then the I$ invalidate, then the redirect (amber TASK-004
  closed). Gate at `CACHE_EN=1`: rv32ui (with `fence_i`), rv32um, rv32mi
  in spike lockstep, arch-test M and `Zifencei`, the interrupt suite, and
  self-modifying code through dirty D$ lines. fence.i also redirects at
  `CACHE_EN=0` (owner 2026-11-25), so the cacheless build passes
  `Zifencei` too. The fill-as-S upgrade cost is amber TASK-006. First OOC of `peregrine_top` on xc7a100t-1: WNS -9.3 ns at
  10 ns, input to stage 7 (P14).
- 2026-11-24: P7 amended (owner): the uncached I/O window is
  0x1000_0000-0x1FFF_FFFF, not "0x1000_0000 and up", so the test images at
  0x8000_0000 stay cacheable. amber TASK-005 (1-cycle hit) landed; stage 4
  built its amber-independent blocks (I$, AXI4 arbiter, CLINT, uncached
  port, `peregrine_top`), loads issuing in MEM from the EX/MEM address.
- 2026-11-24: TASK-001 stage 6 (P13) measured amber's hit latency: 4
  cycles from accept to response, the port free again after 3; a miss 29
  on the bench memory. The owner chose P13 option (b): amber gains a
  pipelined hit path (cache-ip/amber-mesi-l1 TASK-005).
- 2026-11-24: TASK-001 stage 3 landed (the predictor): BTB 32 + BHT 256 as
  P5 sizes them, `BP_EN` A/B. The §5 stress streams run on both builds,
  with every retired prediction held to a model; §4.2 records the as-built
  update and recovery rules.

- 2026-11-23: TASK-001 stage 2 landed (the M unit). P3 revised to
  hold-in-EX (Sean: "Hold in EX"): the busy scoreboard's late writeback
  could not be reported on RVFI. §4.3 gains the rule that an M
  instruction is not interruptible, after the first build livelocked under
  a fast timer. Gates: rv32um 8/8 and riscv-arch-test rv32i_m/M 8/8 on
  both `MUL_DSP` builds.

- 2026-11-23: TASK-001 stage 1 landed (traps, CSR file, cacheless): rv32ui
  42/42 and rv32mi 12/16 against spike, the four exclusions being the
  hardware P6 leaves out (counters, debug triggers, PMP regions); a
  directed interrupt test. P6 gains the zero-entry PMP CSRs the
  privileged spec requires (see the row).
- 2026-11-23: PRD 0.2. P11 revised to one parameterized `rv32i_decode`
  (Sean: "can't it have a param so there is one common file?"); P5–P10,
  P12–P14 ruled at their defaults (Sean: "accept defaults on the rest").
  P13 is decided as "measure first". Implementation filed as
  riscv-ip/peregrine-rv32im TASK-001; the amber clean-all request (P10) as
  cache-ip/amber-mesi-l1 TASK-004.
- 2026-11-23: PRD 0.1 scaffold. P1–P4 are carried from the falcon-suite
  spec and the amber v0.8 client ruling. P5–P14 are proposed with
  defaults, and P13 is open pending a measurement. The COD alignment gaps
  that name peregrine are answered in place: G2 (§4.2), G3 (§4.8), G4
  (§3), G6 (§2) and G7 (§4.5). G8, the naming divergence between machine
  mode and supervisor mode, is the book's.
