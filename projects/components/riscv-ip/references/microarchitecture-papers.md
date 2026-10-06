# Microarchitecture Reading List

The research literature behind the falcon suite's design decisions. Each
entry names the decision it guides and the rung(s) it serves; cite these
in rung books and RTL comments the same way the ISA manual is cited (by
section/idea, not page). Reading order follows the ladder — foundations
first, OOO last.

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
