# Simplified RV32IM: peregrine

**Source:** The RISC-V Instruction Set Manual, Volume I: Unprivileged
Architecture and Volume II: Privileged Architecture (chapter-cited; this
book cites chapters and sections, not pages), Patterson and Hennessy's
*Computer Organization and Design, RISC-V Edition* (COD), and the
falcon-suite design documentation
**Edition:** Simplified for the peregrine-rv32im core, rung 3 of the falcon
suite. Derived from the as-built RTL and its measurements; the peregrine
MAS is the reference for every signal-level detail.
**Version:** 0.1
**Last Updated:** 2026-11-25
**Status:** Draft. Personal study notes.

---

## Overview

peregrine is merlin's five-stage pipeline with four things added:
speculation (a branch target buffer and a 2-bit predictor), precise
machine-mode traps, the M extension on an iterative multiply/divide unit,
and a memory hierarchy (split instruction and data caches behind an AXI4
fabric). Each addition is a lesson, and each lesson has a cost the core
measured: cycles per instruction, clock period, or verification effort.

This book teaches those four additions in that order (Chapters 2 to 5),
then how the core was checked (Chapter 6) and what it all cost (Chapter
7). Where kestrel's book teaches a datapath you can trace by hand, this
one teaches decisions: why a counter is installed at 01 and not 10, why
an M instruction holds EX instead of using a scoreboard, why an
interrupt skips an M instruction, and why the clock target came down
from 100 MHz to 54.1 MHz instead of the cache's hit time going up.

## Document Structure

### Chapter 1: Introduction

- [01_introduction.md](ch01_introduction/01_introduction.md) - What this book is, what peregrine adds over merlin, how to read it
- [02_rung_three.md](ch01_introduction/02_rung_three.md) - Where peregrine sits on the falcon ladder and what it hands on
- [03_conventions.md](ch01_introduction/03_conventions.md) - Notation, cycle labels, machine-mode names versus COD's supervisor names

### Chapter 2: Speculation

- [01_btb_and_bht.md](ch02_speculation/01_btb_and_bht.md) - Lookup in IF, resolve in EX, the 0-versus-2 bubble lesson
- [02_the_install_value.md](ch02_speculation/02_the_install_value.md) - Why a new counter starts at 01: a 4-state bug and a performance trap
- [03_what_prediction_buys.md](ch02_speculation/03_what_prediction_buys.md) - The BP_EN A/B: speedups per stream, and where prediction cannot help
- [04_checking_a_predictor.md](ch02_speculation/04_checking_a_predictor.md) - Why passing programs prove nothing, and the retire-stream check

### Chapter 3: Precise Traps

- [01_commit_at_mem.md](ch03_precise_traps/01_commit_at_mem.md) - Exceptions ride to MEM; one commit point; trap entry cycle by cycle
- [02_interrupts.md](ch03_precise_traps/02_interrupts.md) - Sampling at MEM, the livelock that made M instructions uninterruptible
- [03_mret_and_csrs.md](ch03_precise_traps/03_mret_and_csrs.md) - mret, CSR read in EX and write in MEM, the serialization interlock

### Chapter 4: The M Unit

- [01_hold_in_ex.md](ch04_m_unit/01_hold_in_ex.md) - Hold-in-EX versus a busy scoreboard, and why RVFI decided it
- [02_radix2_versus_dsp.md](ch04_m_unit/02_radix2_versus_dsp.md) - 33 cycles or 2: the structural hazard priced

### Chapter 5: The Memory Hierarchy

- [01_split_caches_and_fence_i.md](ch05_memory_hierarchy/01_split_caches_and_fence_i.md) - I\$ and D\$, the address map, fence.i as real work
- [02_hit_latency.md](ch05_memory_hierarchy/02_hit_latency.md) - amber's hit time from 4 cycles to 1, and the performance model
- [03_the_timing_story.md](ch05_memory_hierarchy/03_the_timing_story.md) - What did not close at 100 MHz, the options, and the clock decision

### Chapter 6: Verification

- [01_what_was_checked.md](ch06_verification/01_what_was_checked.md) - Batteries, lockstep, formal, and what each one can and cannot see
- [02_mutation_lessons.md](ch06_verification/02_mutation_lessons.md) - Bugs the suites missed until a check was written for each

### Chapter 7: What peregrine Costs

- [01_what_peregrine_costs.md](ch07_costs_and_the_next_rung/01_what_peregrine_costs.md) - CPI terms, area, clock: the bill for rung 3
- [02_gyrfalcon_teaser.md](ch07_costs_and_the_next_rung/02_gyrfalcon_teaser.md) - What carries over to the out-of-order capstone and what does not

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-11-25 | First draft: peregrine as built through riscv-ip/peregrine-rv32im TASK-001 (predictor, machine-mode traps, hold-in-EX M unit, I\$ and amber D\$, 18.5 ns on xc7a100t-1), with the measured numbers from the TASK-001 record. |

: Version history
