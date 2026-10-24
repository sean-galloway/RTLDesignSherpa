# Microarchitecture Reading List

The research literature behind the falcon suite's design decisions. Each
entry names the decision it guides and the rung(s) it serves; cite these
in rung books and RTL comments the same way the ISA manual is cited (by
section/idea, not page). Reading order follows the ladder — foundations
first, OOO last; the barrel (gatling) sits beside the ladder, so its
sources come after.

Availability is noted honestly: most IEEE/ACM papers are paywalled, but
nearly all have free author or institutional mirrors worth finding.

## Foundations — kestrel & merlin

1. **D. Patterson and C. Séquin, "RISC I: A Reduced Instruction Set VLSI
   Computer," ISCA 1981.**
   *Guides:* kestrel's whole shape — the case for a register-file-centric
   datapath, single-cycle simplicity, and why the ISA should map 1:1 to
   hardware. The original "see everything" machine.

2. **M. Flynn, "Very High-Speed Computing Systems," Proceedings of the
   IEEE, 1966.**
   *Guides:* pipelining as a concept (the Flynn taxonomy ride-along);
   merlin's raison d'être — overlapping instruction stages for throughput
   rather than raw clock.

3. **J. Hennessy, N. Jouppi, et al., "MIPS: A Microprocessor
   Architecture," MICRO 1982.**
   *Guides:* merlin's stage partition (IF/ID/EX/MEM/WB) — the paper that
   established the five-stage RISC pipeline everyone still teaches.

## Prediction, traps, caches — peregrine

4. **J. E. Smith, "A Study of Branch Prediction Strategies," ISCA 1981.**
   *Guides:* peregrine's dynamic prediction choice — the original 1-bit
   counter and its aliasing/measurement methodology; the baseline our
   2-bit bimodal improves on.

5. **J. K. F. Lee and A. J. Smith, "Branch Prediction Strategies and
   Branch Target Buffer Design," IEEE Computer, 1984.**
   *Guides:* the BTB half of peregrine's frontend — sizing, organization,
   and the interaction between target caching and direction prediction.

6. **J. E. Smith and A. R. Pleszkun, "Implementing Precise Interrupts in
   Pipelined Processors," IEEE Transactions on Computers 37(5),
   May 1988, 562–573.**
   *Guides:* peregrine's precise-exception strategy — the classic
   taxonomy (freeze/history-buffer/future-file/reorder-buffer); the
   reason a simple in-order pipeline can present architecturally exact
   trap state.

7. **N. Jouppi, "Cache Write Policies and Performance," ISCA 1993.**
   *Guides:* peregrine's write-back-with-dirty-bit D$ decision — the
   write-through escape hatch in the spec exists because this paper
   quantifies when each policy wins.

## Out-of-order — gyrfalcon

8. **R. Tomasulo, "An Efficient Algorithm for Exploiting Multiple
   Arithmetic Units," IBM Journal of Research and Development 11(1),
   1967, 25–33.** (freely available from IBM)
   *Guides:* gyrfalcon's reservation stations and common data bus — the
   original OOO. Note what it *lacks* (precise exceptions), which sets up
   the next two papers.

9. **W. Hwu and Y. Patt, "Checkpoint Repair for High-Performance
   Out-of-Order Execution Machines," IEEE Transactions on Computers
   36(12), 1987, 1496–1514.**
   *Guides:* gyrfalcon's chosen mispredict recovery — checkpoint the
   rename state at each branch dispatch and restore on flush, instead of
   undoing history entry by entry. Our default rollback mechanism.

10. **V. Popescu, M. Schultz, J. Spracklen, et al., "The Metaflow
    Architecture," IEEE Micro, 1991.**
    *Guides:* speculative OOO with register renaming as a complete
    machine — the conceptual ancestor of every P6-style design, and the
    cleanest statement of "dispatch speculatively, commit in order."

11. **K. Yeager, "The MIPS R10000 Superscalar Microprocessor," IEEE
    Micro 16(2), April 1996, 28–41.** (free mirrors widely available)
    *Guides:* gyrfalcon's explicit rename map + active-list organization
    and branch checkpointing — the closest single reference for our rung
    4 design. Also the acknowledged inspiration for BOOM.

12. **R. Kessler, "The Alpha 21264 Microprocessor," IEEE Micro,
    March–April 1999.**
    *Guides:* an industrial-strength OOO RISC — clustered scheduling,
    the register file port problem, and what happens when gyrfalcon's
    teaching simplifications are removed. Read last.

13. **J. E. Smith and G. Sohi, "The Microarchitecture of Superscalar
    Processors," Proceedings of the IEEE 83(12), December 1995.**
    *Guides:* the survey that ties 8–12 together — use it as gyrfalcon's
    chapter skeleton and as the checklist that no OOO concept was
    silently dropped.

## ISA rationale & prior art — all rungs

14. **A. Waterman, "Design of the RISC-V Instruction Set Architecture,"
    PhD dissertation, UC Berkeley, 2016.** (free)
    *Guides:* why RV32I looks the way it does — the ISA-design rationale
    behind kestrel's decode table, and the cheapest way to answer "why
    does the spec do X?" without reading all 909 pages.

15. **C. Celio, "The Berkeley Out-of-Order Machine (BOOM)," UC Berkeley
    technical report, 2015.** (free)
    *Guides:* prior art and differentiation — the open-source OOO RISC-V
    baseline. gyrfalcon is deliberately *not* BOOM: SystemVerilog rather
    than Chisel, small enough to hold in your head, checkpoints rather
    than a unified physical register file. Know it so we don't
    accidentally reimplement its complexity.

## Interleaved multithreading — gatling

16. **J. E. Thornton, "Parallel Operation in the Control Data 6600,"
    Proc. AFIPS Fall Joint Computer Conference, Part II, 1964, 33–40.**
    *Guides:* the barrel itself. The 6600's ten peripheral processors
    shared one execution unit in strict rotation, each taking a slot
    every ten minor cycles, so no peripheral processor ever had two
    instructions in flight. gatling's four-context rotation is that
    organization at RV32I (barrel model §3). Thornton's 1970 book
    *Design of a Computer: The Control Data 6600* (Scott, Foresman) is
    the long form.

17. **B. J. Smith, "A Pipelined, Shared Resource MIMD Computer," Proc.
    International Conference on Parallel Processing (ICPP), 1978, 6–8.**
    *Guides:* the Denelcor HEP: fine-grained interleaving used to hide
    pipeline latency with no forwarding and no interlocks between a
    process's own instructions, because a process could issue only once
    its previous instruction had left the pipeline. gatling's "one
    instruction in flight per context" invariant (MAS 1.1) is the same
    rule, fixed by construction instead of by a queue.

18. **H. F. Jordan, "Performance Measurements on HEP — A Pipelined MIMD
    Computer," Proc. 10th International Symposium on Computer
    Architecture (ISCA), 1983, 207–212.**
    *Guides:* the measurement side of the trade: single-process speed
    is the cost of the interleave, and throughput arrives only as the
    process count fills the pipeline. Barrel model §5 and §6 make the
    same argument with kestrel's and gatling's board numbers.

19. **G. Alverson, R. Alverson, D. Callahan, B. Koblenz, A. Porterfield
    and B. Smith, "Exploiting Heterogeneous Parallelism on a
    Multithreaded Multiprocessor," Proc. Supercomputing '92, 1992,
    188–197.**
    *Guides:* the Tera MTA, the HEP idea taken to 128 streams per
    processor to cover memory latency without caches. Where gatling
    stops (four contexts, one block-RAM latency per stage) is read
    against where Tera went.

20. **P. Kongetira, K. Aingaran and K. Olukotun, "Niagara: A 32-Way
    Multithreaded Sparc Processor," IEEE Micro 25(2), March–April 2005,
    21–29.**
    *Guides:* the modern form: four-thread fine-grained cores with
    round-robin issue that skips a stalled thread. That skip is the
    textbook norm and the one thing gatling's rotation deliberately
    does not do (PRD 3.3; MAS chapter 4).

## Textbooks

The owner's textbook library (machine-local, one Markdown file per
section; `vault/handbook/book-library.md`) covers the same ground at
textbook depth. Cite by edition, chapter and section, never by page, with
the short key in the second column. The chapters the rung books lean on:

| Book | Key | Where it guides |
|---|---|---|
| J. L. Hennessy and D. A. Patterson, *Computer Architecture: A Quantitative Approach*, 6th ed., Morgan Kaufmann, 2019 | H&P6 §N | §3.11 fine-grained, coarse-grained and simultaneous multithreading (gatling); Appendix C pipelining and hazards (merlin; gatling's "why not one stream"); Appendix M.5 the lineage from the 6600 I/O processors through HEP, Tera and Niagara (gatling) |
| D. A. Patterson and J. L. Hennessy, *Computer Organization and Design, RISC-V Edition*, 2nd ed., Morgan Kaufmann, 2021 | P&H §N | §4.8-4.9 data and control hazards (kestrel to merlin); §6.4 hardware multithreading (gatling) |
| S. L. Harris and D. M. Harris, *Digital Design and Computer Architecture, RISC-V Edition*, Morgan Kaufmann, 2022 | H&H §N | ch. 6 the RV32I architecture and ch. 7 the single-cycle and pipelined RISC-V microarchitectures (kestrel, merlin); §7.7.7 multithreading as "replicate only the PC and register file" (gatling) |
| J. Ledin, *Modern Computer Architecture and Organization*, 2nd ed., Packt, 2022 | Ledin §N | §14.3 simultaneous multithreading, the contrast case for gatling's interleave; ch. 17 the RISC-V ISA |
| Z. Zhang, *RISC-V Architecture and DSP Processor Design*, Packt, 2026 | Zhang §N | ch. 6 arithmetic units (the ALU rungs); a second RISC-V core walk-through to read kestrel against |

: Textbooks cited by the rung books
