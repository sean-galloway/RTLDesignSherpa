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

# COD-RISC-V ↔ Falcon Suite Microarchitecture Alignment Memo

**Version:** 0.1
**Date:** 2026-10-10
**Status:** Research memo — cited authority for the education site's book references
**Scope:** `projects/components/riscv-ip/` (falcon suite + hive-serv) and
`projects/components/cache-ip/` (amber-mesi-l1, jet-mesi-l1), mapped against
Patterson & Hennessy, *Computer Organization and Design, RISC-V Edition*
(hereafter **COD**) and, for the cache decisions and the out-of-order capstone,
Przybylski, Handy, and Hennessy & Patterson's *Computer Architecture: A
Quantitative Approach* (**H&P**).

---

## 1. How to cite this memo

The education site cites COD by chapter and section number (e.g. "COD §4.8"),
the same way the suite already cites the RISC-V ISA manuals by chapter. This
memo is the **mapping layer** that makes those citations safe: every rung of
the falcon ladder and every cache-IP decision is mapped to a specific COD (or
H&P / Handy / Przybylski) section, with the markdown file path of the converted
source, and a verdict — **aligned**, **aligned-with-divergence** (the
educational rationale is stated; the divergence is never papered over), or
**gap** (the books cover ground our plans do not, or vice versa). Where a book
does not cover something, that absence is stated explicitly and is itself a
citable fact. Rule for the site: a rung doc may say "as COD §X.Y shows" only for
rows marked aligned or aligned-with-divergence in this memo, and must
reproduce the divergence note when citing an aligned-with-divergence row.

## 2. Per-rung alignment table

Book anchors give print section numbers and the calibre markdown path
(`<book>/` prefixes per the bibliography). Verdicts are per the rule above.

### 2.1 kestrel (single-cycle RV32I) — "see everything"

| Decision | Plan (what the suite specifies) | Book anchor | Verdict |
|---|---|---|---|
| Single-cycle datapath: PC, regfile (2R/1W), ALU, ImmGen, branch target adder, separate I/D memories | Spec rung 1; kestrel HAS ch3; RTL complete | COD §4.3 *Building a Datapath* (`computer-organization-and-design-risc-v-edition/ch04-4-the-processor/4.4-4-3-building-a-datapath.md`), §4.4 *A Simple Implementation Scheme* (`4.5-4-4-a-simple-implementation-scheme.md`) — COD's single-cycle machine is the same architecture: separate instruction and data memories because "the processor operates in one clock cycle and cannot use a (single-ported) memory for two different accesses" (§4.3 Check Yourself) | **aligned** — kestrel is a superset of COD's §4.4 subset (full RV32I vs lw/sw/beq/add/sub/and/or) |
| Control as an explicit decode truth table, no FSM | Spec rung 1 ("there is no time dimension to control yet"); kestrel MAS decode tables | COD §4.4 (control completely specified by opcode truth table, COD Figs 4.22/4.26; "this process is completely mechanical"), Appendix A §A.2 (`ch07-appendix/7.1-appendix-a-the-basics-of-logic-design.md` — truth tables, sum-of-products, PLA/ROM) | **aligned** |
| Combinational-read memories, Harvard | Spec open decision (default chosen), documented in kestrel memory contract | COD §4.3 treats instruction memory as combinational ("the output at any time reflects the contents of the location specified by the address input, and no read control signal is needed"); §4.4 load path sets the single-cycle clock | **aligned-with-divergence** — COD's combinational memory is a modeling choice it silently makes; kestrel documents it as a contract and makes its cost the lesson (kestrel book ch7 "The critical path is the whole machine") |
| Full RV32I incl. JAL/JALR, shifts, 6 branches; FENCE = documented NOP; ECALL/EBREAK halt into a trap stub (no CSR file) | Spec rung 1; kestrel HAS ISA scope | COD §2.5 (instruction formats, `ch02-.../2.7-2-5-representing-instructions-in-the-computer.md`), §2.7 decisions; §4.10 *Exceptions* (`4.12-4-10-exceptions.md` — SEPC/SCAUSE, single entry point, "the hardware contract is normally to stop the offending instruction in midstream… and then branch to a prearranged address") | **aligned-with-divergence** — kestrel halts into a stub instead of vectored handler entry; the divergence is documented in the HAS halt/trap chapter. COD names supervisor CSRs (SEPC/SCAUSE); kestrel's later rungs use machine-mode names per the RISC-V privileged spec — see gap G8 |
| Misaligned L/S handled by a documented two-clock retry in hardware | kestrel book ch5/ch7 (cross-word occupies two clocks) | COD §5.3 assumes aligned data ("we'll assume that data are aligned in memory, and discuss how to handle unaligned cache accesses in an Elaboration", `ch05-.../5.4-5-3-the-basics-of-caches.md`) | **aligned-with-divergence** — the spec never cites this; kestrel exits the aligned-world assumption COD's cache chapter lives in. Worth one sentence in the kestrel book citing COD §5.3 |

### 2.2 merlin (5-stage pipeline RV32I) — "flow it"

| Decision | Plan | Book anchor | Verdict |
|---|---|---|---|
| IF/ID/EX/MEM/WB with pipeline registers | Spec rung 2 | COD §4.6 *An Overview of Pipelining* (`4.8-4-6-an-overview-of-pipelining.md` — five classic RISC-V steps, laundry analogy, speedup ≈ number of stages), §4.7 *Pipelined Datapath and Control* (`4.9-4-7-pipelined-datapath-and-control.md` — control signals created in ID and carried in pipeline registers, COD Fig 4.53) | **aligned** |
| Forwarding from EX/MEM and MEM/WB with explicit priority | Spec rung 2 ("forwarding matrix is Chapter 1 of merlin's book") | COD §4.8 *Data Hazards: Forwarding versus Stalling* (`4.10-4-8-data-hazards-forwarding-versus-stalling.md`) — hazard conditions 1a/1b/2a/2b, the `RegWrite` and `rd ≠ 0` guards (x0 must not be forwarded), and the MEM-stage-priority clause: "the result in the MEM stage is the more recent result" | **aligned** — "explicit priority" in the spec is exactly COD's `not(EX/MEM…)` priority clause |
| Load-use interlock, one bubble | Spec rung 2 | COD §4.8 hazard-detection unit condition (`ID/EX.MemRead` × register match in IF/ID), bubble insertion by zeroing the ID/EX control fields | **aligned** |
| Branches resolved in EX, predict-not-taken, flush on taken (2-instruction penalty) | Spec rung 2 | COD §4.9 *Control Hazards* (`4.11-4-9-control-hazards.md`) — predict-not-taken + flush; COD's base pipeline resolves in MEM (3 fetched behind); its discussed optimization moves the decision to ID (penalty 1, at the cost of new forwarding into the equality test and up to 2-cycle stalls for load→branch) | **aligned-with-divergence** — merlin's EX resolution sits between COD's two points and is never justified against them; the merlin book should state the 2-cycle penalty and cite §4.9's move-to-ID discussion as the road not taken (gap G2) |
| No branch prediction hardware at rung 2 | Spec rung 2 ("No prediction at this rung") | COD §4.6 (predict-not-taken as the first "Predict" great idea; dynamic predictors >90% accuracy motivate rung 3) | **aligned** — the deferral is the COD narrative |

### 2.3 peregrine (advanced in-order RV32IM) — "speed it up"

| Decision | Plan | Book anchor | Verdict |
|---|---|---|---|
| BTB + 2-bit bimodal predictor, mispredict recovery flush | Spec rung 3, open-decisions row | COD §4.9 (branch prediction buffer, 1-bit loop-mispredict example → 2-bit FSM COD Fig 4.65; BTB elaboration: "tells us whether a conditional branch is taken, but still requires the calculation of the branch target"); H&P §3.4 *Reducing Branch Costs with Dynamic Hardware Prediction* (`computer-architecture-a-quantitative-approach-th/ch02-exercises-161/2.4-3-4-reducing-branch-costs-with-dynamic-hardware.md` — saturating counters, "2-bit predictors do almost as well" as n-bit) | **aligned** — the 2-bit choice is the book-canonical teaching point (not 1-bit, not TAGE, per the spec's own rationale) |
| Iterative multicycle multiply/divide, busy scoreboard (structural-hazard lesson) | Spec rung 3 | COD §3.3 *Multiplication* (`ch03-.../3.4-3-3-multiplication.md` — sequential shift-add hardware, refined 1-cycle/bit version, "multiply can take several clock cycles without significantly affecting performance"), §3.4 *Division* (`3.5-3-4-division.md` — restoring algorithm, n+1 steps, nonrestoring elaboration, SRT); §4.6 structural-hazard definition | **aligned** |
| div/divu/rem/remu edge semantics | *Not specified in the spec* | COD §3.4: "RISC-V divide instructions ignore overflow, so software must determine whether the quotient is too large… RISC-V software must check the divisor to discover division by 0 as well as overflow" | **gap** — see G4 |
| Split blocking write-back I$/D$ (interim, cache-IP slot marked) | Spec rung 3; D$ write-back + dirty bit per open decisions | COD §5.3 (split vs combined caches and the bandwidth argument; write-back scheme and dirty bit; write-allocate vs no-write-allocate elaboration), §5.9 *Using a Finite-State Machine to Control a Simple Cache* (`ch05-.../5.10-5-9-using-a-finite-state-machine-to-control-a-si.md` — the four-state blocking controller Idle/Compare Tag/Write-Back/Allocate; the blocking design is named in the elaboration: "this simple design is called a blocking cache") | **aligned** — COD's §5.9 cache is amber/peregrine's skeleton minus associativity and coherence |
| AXI4 master onto the repo fabric with MonBus visibility | Spec rung 3 | COD §5.9's cache-memory interface is a generic valid/ready + Ready-signal handshake (128-bit data, "not a fixed number of cycles"); no SoC fabric appears in COD ch5 | **aligned-with-divergence** — AXI4 + MonBus are repo-integration constructs the books don't cover; the divergence is educational (bus protocol as a first-class lesson) and must be stated as such in the peregrine book |
| Machine-mode CSRs (mstatus/mie/mip/mtvec/mepc/mcause/mscratch), precise exceptions, CLINT-shaped interrupts precise at oldest | Spec rung 3 | COD §4.10 *Exceptions* (pipelined exceptions as control hazards; flush signals; precise vs imprecise elaboration — "RISC-V and the vast majority of computers today support precise interrupts"; prioritization: "the hardware sorts exceptions so that the earliest instruction is interrupted"); §5.14 lists CSR instructions, ecall/ebreak/sret/wfi at a glance (`ch05-.../5.15-5-14-real-stuff-the-rest-of-the-risc-v-system-an.md`) | **aligned-with-divergence** — COD's worked example uses supervisor names (SEPC/SCAUSE, "supervisor exception cause register") and a single entry point; peregrine implements machine mode per the RISC-V privileged spec, which COD does not cover. The precision *contract* is COD's; the CSR map is the privileged manual's (already the suite's cited ISA authority) |

### 2.4 gyrfalcon (OoO capstone, RV32IM) — "hide everything"

| Decision | Plan | Book anchor | Verdict |
|---|---|---|---|
| Out-of-order execution with rename, ROB, reservation stations | Spec rung 4 (dual issue; 32×64 rename; 32-entry ROB; 3 RS; 2 CDBs; checkpoint-restore rollback) | **Beyond COD's scope.** COD §4.6 routes readers: "Section 4.11 introduces advanced pipelining concepts, such as superscalar and dynamic scheduling" — an introduction only. The citable authority is H&P: §3.1 ILP concepts (`.../2.1-3-1-instruction-level-parallelism-concepts-and-c.md`), §3.2 *Overcoming Data Hazards with Dynamic Scheduling* (`2.2-3-2-...md` — in-order issue / out-of-order execution, WAR/WAW arise only from name dependences, "eliminated by register renaming", scoreboard vs Tomasulo), §3.4 (prediction), §3.6 multiple issue (`2.6-3-6-...md`), §3.7 *Hardware-Based Speculation* (`2.7-3-7-...md` — ROB four fields, the issue/execute/write-result/commit four-step sequence, commit only at ROB head, flush-and-restart on mispredicted branch) | **aligned-with-divergence (vs H&P)** — gyrfalcon's explicit rename map + free list (32 arch × 64 phys) is the register-alias-table variant H&P names in §3.7's alternative implementation ("extra registers for renaming and the ROB only to track when instructions can commit"). H&P's canonical recovery is ROB flush; gyrfalcon's per-branch rename checkpoint + free-list restore is a deliberate simplification — the spec says so ("simplest correct rollback") and the divergence must be cited, not hidden |
| Precise exceptions at commit; flush squashes ROB, rolls back rename | Spec rung 4 | H&P §3.7 ("prevent any irrevocable action (such as updating state or taking an exception) until an instruction commits"); H&P §3.2 on preserving exception behavior under dynamic scheduling; COD §4.10 precise-interrupt elaboration for the concept's origin | **aligned** (H&P) |
| Same ISA as peregrine so all batteries carry over | Spec rung 4 | — (suite doctrine, not a book topic) | n/a — verification doctrine |

Site citation rule: **gyrfalcon material must cite H&P, not COD.** Saying "COD covers this" for an OoO mechanism would be an unsourced claim; COD's own text defers to its §4.11 overview.

### 2.5 garuda (RV32IMF delta on gyrfalcon) — "float it"

| Decision | Plan | Book anchor | Verdict |
|---|---|---|---|
| Separate FP register file (32 arch × 48 phys) with its own rename | Spec rung 5 | COD §3.5 *Floating Point* (`ch03-.../3.6-3-5-floating-point.md` — "The RISC-V designers decided to add separate floating-point registers… f0…f31"; the Hardware/Software Interface box argues the separate-register tradeoff: more registers, more bandwidth, no extra instruction bits); H&P §3.2 renaming carries to FP registers | **aligned** |
| `fcsr` accrued flags (NV/DZ/OF/UF/NX) precise at commit via ROB OR-merge | Spec rung 5 | COD §3.5 states the architectural contract verbatim in spirit: "RISC-V computers do not raise an exception on overflow or underflow; instead, software can read the floating-point control and status register (fcsr) to check whether overflow or underflow has occurred" | **aligned-with-divergence** — the contract is COD's; the precise-at-commit OR-merge *mechanism* in an OoO core is beyond both books (H&P treats precise exceptions generally, not accrued FP flags). Cite COD §3.5 for the contract; present the merge mechanism as the repo's own, in H&P §3.7's commit framework |
| IEEE-754 fp32 units consumed from `rtl/math` | Spec rung 5; math family verified 2026-10-07 | COD §3.5 (IEEE 754 formats, hidden 1, bias 127, NaN/∞, FP addition Fig 3.14 and multiplication Fig 3.16 algorithms — align/normalize/round-with-renormalize) | **aligned** at the format/algorithm level |
| RNE hard-wired; requesting another RM raises NV | Spec open decisions | COD §3.5 presents the round step generically (Fig 3.14/3.16 step 4) and treats IEEE 754 as the standard; the RISC-V RM field with dynamic modes is privileged/unprivileged ISA territory the book does not detail | **aligned-with-divergence** — documented simplification, itself instructional, per the spec; cite COD §3.5 for the rounding step it implements |
| SUBNORMAL_SUPPORT=0 (FTZ) at the units for v1 | Spec open decisions | COD §3.5 covers denormalized numbers in an elaboration (Fig 3.13 caption: "Denormalized numbers are described in the Elaboration on page 233"); IEEE gradual underflow is the default COD describes | **aligned-with-divergence** — FTZ is a real divergence from IEEE 754 default behavior and from the COD treatment; must be cited as such in the garuda book (it is honest, build-time, and non-default, but it is a divergence) |
| Non-pipelined 9–11-cycle Goldschmidt FDIV / Newton-rsqrt FSQRT behind an FP reservation station; issue holds while busy | Spec rung 5 | COD §4.6 *Understanding Program Performance*: "For modern pipelines, structural hazards usually revolve around the floating-point unit, which may not be fully pipelined" — the exact teaching point | **aligned** at the pipeline level. **Gap at the algorithm level**: COD §3.4's fast-division content is integer SRT; neither COD §3.5 nor the converted H&P chapters cover Goldschmidt or Newton-Raphson square root — garuda needs a numerical-methods citation here (G9) |

### 2.6 hive-serv (1 VexRiscv + 16 SERV cluster) — adjacent, uses RISC-V rather than teaching it

| Decision | Plan | Book anchor | Verdict |
|---|---|---|---|
| Hierarchical control: 1 master core + 16 monitor cores, star control network, round-robin | hive PRD §3-4 | COD §6.5 *Multicore and Other Shared Memory Multiprocessors* (`ch06-.../6.7-6-5-multicore-and-other-shared-memory-multiproce.md` — classic SMP organization COD Fig 6.7, UMA/NUMA); COD §6.8 *Clusters… Message-Passing Multiprocessors* (title-level: separate address spaces, explicit sharing) | **aligned-with-divergence** — COD's §6.5 machine is symmetric shared-memory; hive is a heterogeneous master/agents system with **private** per-core memories and message passing, which is the §6.8 category with a control-plane hierarchy COD does not model. The hive book should cite §6.5 Fig 6.7 as the contrast figure ("why not SMP") and §6.8 as the bucket it occupies |
| Quiesce protocol + atomic context switch (<25 cycles) for network reconfiguration | hive PRD §4.3/§6.3 | Not covered by COD (no such construct in ch6 as converted) | **gap** — repo-original; present as such |
| Distributed monitoring (per-tile counters, threshold alerts, periodic reporting) | hive PRD §4.2 | COD ch6 has no observability/monitoring material | **gap** — beyond the books; the monitoring-literature citations in hive_spec ch1 §5 are the right authorities |
| No shared memory, hence no coherence protocol; synchronization is message-based | hive PRD | COD §2.11 *Parallelism and Instructions: Synchronization* (`ch02-.../2.13-2-11-parallelism-and-instructions-synchronizatio.md` — lr.w/sc.w, atomic exchange, locks) and §6.5 (synchronization via shared variables requires hardware primitives) | **aligned-with-divergence** — the falcon/hive ISAs have no A extension, so lr/sc locks are out of scope by construction; cite COD §2.11 once to say *why* hive passes messages instead |

---

## 3. Gaps in our plans the books expose

Numbered for tracking; "Action" is a concrete spec/doc edit.

- **G1 — No hazard taxonomy pinned to merlin's verification plan.** The spec names forwarding, load-use, and flush, but never states the structural/data/control classification (COD §4.6) nor forwards the exact forwarding conditions (COD §4.8's guarded equations, including the x0 guard and MEM-over-WB priority) as the RTL's contractual definition. *Action:* merlin PRD: "the forwarding unit shall implement COD §4.8 Fig 4.57 conditions verbatim, including `rd ≠ 0` guards"; the directed hazard suite's golden matrix derives from those equations.

- **G2 — Branch penalties are never quantified.** COD §4.9 makes penalty a function of the resolution stage (MEM → 3 fetched behind; ID → 1); merlin resolves in EX → 2, peregrine moves prediction to IF/ID. The spec never writes these numbers down, so the drill app has no predicted CPI curve. *Action:* state penalty per rung (kestrel 0 — resolved combinationally; merlin 2; peregrine = f(mispredict rate) with the 2-bit FSM's accuracy) and cite COD §4.6's CPI-1.10 worked example as the modeling pattern.

- **G3 — No cache performance model for peregrine/amber.** COD §5.4 gives the machinery (CPU time = (CPU exec cycles + memory-stall cycles) × cycle time; AMAT = hit time + miss rate × miss penalty) and a worked example (2%/4% I$/D$ miss rates, CPI 2, 100-cycle penalty → CPI 5.44; perfect-cache speedup 2.75×). The falcon spec and amber PRD carry no such model, so MonBus counters have no predicted values to deviate from. *Action:* one subsection in peregrine's PRD and amber's docs carrying a worked COD-style example with the suite's actual cache geometry (32 KiB/64 B/4-way) and an assumed DRAM latency; jet's J7 "measured claim" then has a predicted number to confirm or break.

- **G4 — Division edge cases unspecified.** COD §3.4: RISC-V divide ignores overflow and division-by-zero; software must check the divisor. The falcon spec is silent on what `div`/`rem` return for divisor 0 and for −2³¹/−1. *Action:* pin to spike lockstep behavior (the de facto contract) and cite COD §3.4 for the architectural intent; add the cases to the rv32um battery notes.

- **G5 — Memory-consistency model never stated.** COD §5.10 separates coherence (what value a read returns) from consistency (when a written value is seen) and gives the write-serialization assumptions. The suite never says which model a rung implements (a uniprocessor in-order rung has a trivial model; amber's pair rig does not). *Action:* suite doctrine note: uniprocessor rungs are sequentially consistent by construction; the amber pair rig documents its ordering assumptions against COD §5.10's elaboration (this also bounds what the pair rig may claim).

- **G6 — Physical vs virtual cache indexing never discussed.** Handy §2.2.1 (logical vs physical caches; aliasing; the R4000 war story in §4.2.2) is the classic treatment; COD §5.7 covers virtual memory properly. The suite's caches are physically indexed *by construction* (no MMU — an explicit non-goal), but no doc says so or says why it dodges the aliasing problem. *Action:* one paragraph each in amber's PRD and peregrine's book citing Handy §2.2.1; this pre-answers the "why doesn't the index use virtual bits" question students will ask.

- **G7 — Split-cache and write-policy rationale is one line.** COD §5.3's split-vs-combined tradeoff (combined has marginally better miss rate; split doubles bandwidth — "almost all processors today use split instruction and data caches") and write-back/write-allocate elaboration are the missing justification for peregrine's "split blocking write-back" and amber's D5. *Action:* cite in both docs; also Handy §2.2.4 for the dirty-bit motivation.

- **G8 — Exception/CSR naming divergence from COD is uncited.** COD §4.10's example uses supervisor names (SEPC/SCAUSE); peregrine implements machine mode (mepc/mcause). Correct, but the divergence should be one sentence in peregrine's book so students reconciling the book and the RTL aren't confused. COD §5.14 confirms the CSR instructions exist but does not document the privileged map — the RISC-V privileged manual remains the authority (already the suite's citation pattern).

- **G9 — Long-latency FP algorithm citations missing.** Goldschmidt division and Newton-Raphson rsqrt appear in no converted book chapter (COD §3.4 is integer SRT; COD §3.5 lists fdiv.s/fsqrt.s without algorithms; the converted H&P stops at ch4 — see G10). *Action:* garuda's book needs a primary citation for both algorithms (the math library's own docs/references are the natural source).

- **G10 — H&P quantitative conversion is truncated.** The calibre tree for H&P ends inside chapter 4; its memory-hierarchy chapter (the canonical MSHR / nonblocking-cache / multilevel quantitative treatment, H&P ch5) is not in the converted source. jet's MSHR decisions (J1–J5) therefore cannot cite H&P from this tree. *Action:* either extend the conversion or cite Kroft's MSHR paper (ISCA 1981) and H&P ch5 by print section only, flagged as outside the local conversion.

## 4. Improvements to the education framing (where book cross-links pay rent)

The site's thesis is "the diff between neighbors is the lesson." Each of these is a place where a COD/H&P figure or section number makes that diff explicit:

1. **kestrel book ch7 ↔ COD §4.4.** The chapter's "the critical path is the whole machine" argument is COD's closing subsection "Why a Single-Cycle Implementation is not Used Today" (load path through five units; CPI 1 but a long clock; "violates the great idea from Chapter 1 of making the common case fast"). Cite it: kestrel's cost chapter and COD's exit paragraph are the same paragraph; the student can check the authority.
2. **merlin book ↔ COD Figs 4.54–4.62.** The pipeline stage-viewer drill animates exactly COD's dependence diagrams and the forwarding/hazard-detection hardware. One figure-caption cross-link per drill mode ("this is COD Fig 4.56 with the muxes drawn as arrows") anchors the app to the canon.
3. **merlin teaser ↔ COD §4.6.** kestrel's book already draws "one kestrel cycle cut into merlin's stages" — cite COD's laundry analogy and the 800 ps → 200 ps worked example as the same cut with numbers.
4. **peregrine book ↔ COD Fig 4.65 + §5.9 Fig 5.38.** The 2-bit FSM is the predictor, verbatim; the four-state cache controller (Idle/Compare Tag/Write-Back/Allocate) is amber's skeleton. Students who can draw COD's two figures can read peregrine's RTL cold.
5. **cache_sim ↔ COD §5.4.** The app is AMAT made playable; cite the equation next to the policy knobs so a student can predict what flipping LRU→FIFO should do before running it (and amber D7's golden-model parity then tests the prediction).
6. **gyrfalcon book ↔ H&P §3.7 Fig 3.29.** The rename/ROB viewer animates H&P's four-step sequence. The book should state gyrfalcon's one-paragraph divergence: H&P's canonical recovery is ROB flush-and-restart; gyrfalcon checkpoints rename at each branch and restores (and why that is simpler and honest for a first OoO).
7. **garuda book ↔ COD §3.5.** Quote the fcsr sentence (architectural contract) and map Fig 3.14/3.16's steps onto the math library's adder/multiplier blocks — "consume a verified library" is COD's algorithm section realized as RTL.
8. **hive book ↔ COD Fig 6.7 vs §6.8.** Open the multicore chapter with the SMP organization figure, then show why a 17-core SMP on a Nexys A7 is the wrong lesson and hive's master/agents message passing is the §6.8 bucket scaled to a teaching board.
9. **Suite "further reading" block.** Each rung book's front matter gets a five-line Further Reading: COD ch4 (kestrel, merlin), COD ch4+5 (peregrine), H&P ch3 (gyrfalcon), COD §3.5 + H&P ch3 (garuda), COD ch6 (hive), COD §5.9-5.11 (amber). This memo's tables are the backing for those lists.

## 5. Cache-decision alignment appendix (amber D1–D11, jet J1–J7)

COD chapter 5 is the anchor canon; Handy and Przybylski supply the
decision-level depth COD deliberately omits (COD §5.3: "Readers already
familiar with cache basics may want to skip to Section 5.4").

### 5.1 amber-mesi-l1

| Decision | Plan | Book anchor | Verdict |
|---|---|---|---|
| D1 geometry 32 KiB / 64 B / 4-way (128 sets), parameterised + tiny 16-set/2-way formal config | amber PRD D1 | COD §5.4 (set-associative placement; the worked tag-bit example; "going from one-way to two-way associativity decreases the miss rate by about 15%", COD Fig 5.16); Przybylski §4.2 (`cache-and-memory-hierarchy-design-a-performance/ch05-4-performance-directed-cache-design/5.2-4-2-speed-set-size-tradeoffs-57.md` — confirms Hill's ~20% miss-ratio drop direct→2-way for caches up to ~256 KiB, and the tag-compare-before-data-gating hit-time cost [Jouppi 89]); Przybylski §4.1 (optimum total cache size "typically in the 32KB to 128KB range") | **aligned** — the 32 KiB/4-way center sits inside the books' optimum region; the parameterisation is education-first (DV matrix over board BRAM, per the PRD) |
| D2 CPU-side GAXI slave | amber PRD D2 | No book covers a house bus fabric; COD §5.9 assumes a bare valid/ready + address/data processor port | **aligned-with-divergence** — education-first divergence: the books' anonymous port is replaced by the repo's fabric so STREAM/cache_sim attach later without adapters; must be flagged as divergence in amber's docs |
| D3 memory-side AXI4 rd/wr masters + monlite | amber PRD D3 | COD §5.9's memory side: 128-bit data + Ready, "not a fixed number of cycles" — a handshake any burst protocol implements | **aligned-with-divergence** — AXI4 bursts are industry practice the books abstract away; divergence defended (real bus protocol as a learning objective) |
| D4 snoop transport ACE-shaped AC/CD/CR per onyx contract | amber PRD D4 | COD §5.10 (snooping: every cache "monitor[s] or snoop[s] on the medium"; broadcast limits scalability); COD §5.11 advanced material (invalidate protocol over a broadcast medium; write-back snoop intervention; the shared-state bit — "the processor with the sole copy of a cache block is normally called the owner"); Handy ch4 (`cache-memory-book-the-second-edition-the-morgan/ch06-.../6.3-4-2-multiple-processor-systems.md` — the full coherence-protocol taxonomy: write-through snooping, write-once, ownership, MESI, Futurebus+) | **aligned-with-divergence** — the *protocol family* is book-canonical; the ACE channel names are ARM-specific and beyond all four books (Handy's Futurebus+ §4.3.2 is the closest documented bus-level realization). Cite COD §5.10/§5.11 for the protocol, flag ACE as the transport choice |
| D5 write-back + write-allocate (write-through kept as bring-up mode) | amber PRD D5 | COD §5.3 (write-back definition; write-allocate vs no-write-allocate elaboration); Handy §2.2.4 (copy-back + dirty bit + eviction/victim terminology; and the state-encoding observation: "more than three states can be encoded by the two bits normally used for the Valid and Dirty bits"); Przybylski Appendix B (`ch11-.../11.1-appendix-b-modelling-write-strategy-effects.md` — the studied machine class is exactly "write-back, with write buffering… a write into a cache is assumed to take twice as long as a read, since the tags must be checked before the data array is written"); Handy §4.2.4 (bus-traffic arithmetic: converting write-through → copy-back drops bus demand from ~14.5% to ~5% of CPU cycles) | **aligned** — and the PRD's research rationale (write-through deletes the dirty-snoop traffic the pair rig exists to measure) is the Handy §4.2.4 argument turned into an experiment |
| D6 plain MESI on a 3-bit state field; MOESI headroom reserved | amber PRD D6 | COD §5.11 (the three-state invalid/shared/modified protocol as FSM transition tables, then: "The most common extension of this basic protocol is the addition of an exclusive state" — the book constructs MESI without naming it); Handy §4.3.1 *The MESI Protocol* (state semantics; "Exclusive must be entered before going to Modified. No cache line is allowed to go directly from either of the other states to the Modified state"; snoop read/write behavior; original Multibus MESI had no write-allocate and no direct intervention, Intel added write-allocate) | **aligned-with-divergence** — amber pairs MESI with write-allocate, i.e., the Intel/Futurebus+ evolution Handy documents, not the original Multibus form; the 3-bit field with reserved headroom is the Handy §2.2.4 state-encoding point. One line in amber's docs citing both closes this |
| D7 replacement {LRU, tree-PLRU, FIFO, RANDOM}, LRU default; tree-PLRU the timing fallback | amber PRD D7 | COD §5.4 (LRU "most commonly used"; the one-bit-per-set 2-way implementation); Handy §2.2.2 (true-LRU bit cost — 4-way needs 5 bits/line, 8-way 16 bits/line — and the pseudo-LRU tree: 3 bits/line, "implemented as write-only", "essentially double the speed… over a true LRU algorithm"; also Hill's ~20% and Agarwal's ~69% rules of thumb); Przybylski §4.2 Figs 4-7–4-9 (break-even cycle-time contours for associativity — the quantitative case that associativity costs hit time) | **aligned** — the "LRU default, tree-PLRU timing fallback" split is exactly Handy's argument; the FIFO/RANDOM additions exist for cache_sim golden-model parity, an education-first extension the books don't require but don't contradict |
| D8 observation via `*_monlite`, never `_mon` on measured paths | amber PRD D8 | COD §5.4 measures with counters/models, not non-intrusive observation fabrics; no book construct matches MonBus | **aligned-with-divergence (education-first)** — "the observer must not perturb what it measures" is the PRD's own principle; the books simply don't have instrumentation chapters. Defend as a teaching instrument: amber/jet exist to *produce* the miss-latency numbers COD §5.4 assumes |
| D9 verification: gem5 Ruby SLICC-derived FSM oracles, cache_sim parity (LRU/FIFO/RANDOM), SymbiYosys control-layer proofs, Pattern-B grids | amber PRD D9 | COD §5.9/§5.11 specify the FSM but no verification methodology; Handy/Przybylski predate executable protocol oracles | **aligned-with-divergence (modern practice)** — flag honestly: the protocol's *content* is book-derived (COD Fig 5.38's skeleton, Handy Table 4.1's MESI matrix, gem5's SLICC as the executable oracle), the *method* is the repo's rds-dv culture |
| D10 first consumer = TB masters; gated deliverable = two-amber pair rig; STREAM attach later | amber PRD D10 | Not covered by any book — no text proposes a coherence research rig as a teaching deliverable | **aligned-with-divergence (education-first)** — defended: the pair rig is the instrument that answers "what does lockup-freedom actually buy" with measured data, the quantitative question COD §5.4 and Przybylski ch4 both pose |
| D11 tag/data on `sdpram_core`, pending/fill queues on `gaxi_fifo_sync` (house no-bespoke-SRAM rule) | amber PRD D11 | Przybylski §4.2 (implementation/technology constraints shape organization — integrated vs discrete RAM cost arguments); COD §5.3 footnote-style SRAM/tag-array split (COD Fig 5.12 caption: separate large data RAM, smaller tag RAM) | **aligned-with-divergence** — the books' implementation-constraint reasoning supports the *pattern*; the house primitives themselves are repo constructs |

### 5.2 jet-mesi-l1 (the deltas)

| Decision | Plan | Book anchor | Verdict |
|---|---|---|---|
| J1–J4 MSHR organization, hit-under-miss scope, miss merging, ordering | jet PRD J1–J4 (all OPEN) | COD §5.9 names the category only: "this simple design is called a blocking cache… Section 5.12 describes the alternative, which is called a nonblocking cache" — the converted COD tree contains no §5.12 body. Handy §2.2.6 *Write buffers and line buffers* (`ch04-.../4.2-2-2-choosing-cache-policies.md`) covers the adjacent mechanisms: posted write buffers, and **concurrent/background (fly-by) line write-back** — hiding the eviction cycle from the processor, the victim-buffer idea in J5's seed form | **gap** — MSHRs as such are not in any converted book chapter (see G10: H&P ch5, the canonical MSHR/nonblocking treatment, is beyond the local conversion; Kroft ISCA 1981 is the primary). J1–J4's eventual decisions must cite outside this tree and say so |
| J5 dirty victim behind an outstanding fill; victim buffer depth 0–4 | jet PRD J5 | Handy §2.2.6 (concurrent line write-back; "the classic" deadlock-adjacent corner is the read-miss-behind-dirty-eviction ordering); COD §5.3 elaboration (write-back buffer halves the dirty-replace miss penalty) | **aligned** at the mechanism level; the deadlock-freedom proof target is beyond the books |
| J6 congestion/fairness when MSHRs full | jet PRD J6 | Not covered (queueing policy for miss structures postdates the books' scope) | **gap** — repo-original decision with a formal liveness target |
| J7 "the measured claim": same trace suite + board as amber, latency distribution/miss concurrency/MSHR occupancy from MonBus | jet PRD J7 | COD §5.4 (the performance model the measurement must confirm or refute — AMAT, memory-stall cycles); Przybylski ch3–4 (the analytical-model + measurement loop as method: "Two Complementary Approaches") | **aligned** as method — jet is the experimental half of a Przybylski-style two-approach study, with the pair rig as the apparatus |

### 5.3 Deliberately-divergent repo constructs (defense summary)

Marked here once so rung docs can inherit the verdict: **MonBus/monlite
observation** (D8), **GAXI** (D2) and the **AXI4 house fabric** (D3), the
**ACE-shaped snoop transport** (D4), the **pair rig** (D10), and the
**house-primitive SRAM/FIFO rule** (D11) are **education-first divergences**:
none appears in COD, Handy, or Przybylski; each exists to teach something the
books leave abstract (observation without perturbation; a real SoC fabric;
bus-level coherence transports; controlled experiment design; disciplined
implementation reuse). The memo's rule stands: these are cited as
divergences with this rationale — never as book-aligned.

## 6. Bibliography

Full citations with the local converted-source paths (calibre library). Cite by
print chapter/section on the site; the paths are for maintainers auditing a
claim.

1. **Patterson, David A., and John L. Hennessy.** *Computer Organization and Design: The Hardware/Software Interface, RISC-V Edition.* Morgan Kaufmann, 2018 (1st ed.). Local conversion: `/mnt/data/github/calibre/books/computer-organization-and-design-risc-v-edition/` — chapters as `chNN-<slug>/`, sections as numbered `.md` files; chapter TOC at `index.md`. Chapters cited here: 2 (§2.5, §2.11), 3 (§3.3, §3.4, §3.5), 4 (§4.3–§4.10), 5 (§5.3, §5.4, §5.9, §5.10, §5.11 advanced material, §5.14), 6 (§6.5, §6.8, §6.9), Appendix A.
2. **Hennessy, John L., and David A. Patterson.** *Computer Architecture: A Quantitative Approach,* 6th ed. Morgan Kaufmann, 2017. Local conversion: `/mnt/data/github/calibre/books/computer-architecture-a-quantitative-approach-th/` — **note: the conversion covers front matter and chapters 1–4 only** (chapter bodies live under `ch00-front-matter/`, `ch01-exercises-74/` [= book ch2], `ch02-exercises-161/` [= book ch3, the ILP chapter], `ch03-exercises-288/` [= book ch4]); chapters 5+ (memory hierarchy, MSHRs) are not in the tree — see G10. Sections cited here: §3.1, §3.2, §3.4, §3.6, §3.7.
3. **Handy, Jim.** *The Cache Memory Book,* 2nd ed. Morgan Kaufmann, 1998. Local conversion: `/mnt/data/github/calibre/books/cache-memory-book-the-second-edition-the-morgan/` — ch3 (cache basics), ch4 §2.2 (cache policies: §2.2.1 logical/physical, §2.2.2 associativity + replacement incl. pseudo-LRU, §2.2.4 write-through vs copy-back, §2.2.5 line size, §2.2.6 write/line buffers), ch6 (coherency: §4.2 multiprocessor, §4.3 protocols incl. §4.3.1 MESI, §4.3.2 Futurebus+).
4. **Przybylski, Steven A.** *Cache and Memory Hierarchy Design: A Performance-Directed Approach.* Morgan Kaufmann, 1990. Local conversion: `/mnt/data/github/calibre/books/cache-and-memory-hierarchy-design-a-performance/` — ch3 (background), ch4 (design problem, two complementary approaches), ch5 (performance-directed design: §4.1 speed–size, §4.2 speed–set size, §4.3 block size–memory speed, §4.4 global optimum), ch11 Appendix B (modelling write-strategy effects).

---

**Last Updated:** 2026-10-10
**Maintainer note:** re-run this memo's mapping when a new rung's PRD lands
(merlin first) or when the H&P conversion is extended past chapter 4 (unblocks
the jet MSHR citations, G10).

## Navigation

- **← Suite doctrine index:** [INDEX.md](INDEX.md)
- **Design spec:** [`docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`](../../../../docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md)
- **Suite README:** [../README.md](../README.md)
- **Cache-IP line:** [cache-ip amber PRD](../../cache-ip/amber-mesi-l1/PRD.md) · [jet PRD](../../cache-ip/jet-mesi-l1/PRD.md)
