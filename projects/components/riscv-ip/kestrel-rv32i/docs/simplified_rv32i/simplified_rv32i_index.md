# Simplified RV32I: kestrel

**Source:** The RISC-V Instruction Set Manual, Volume I: Unprivileged
Architecture (riscv-spec.pdf, chapter-cited; this book cites chapters and
sections, not pages) and the falcon-suite design documentation
**Edition:** Simplified for the kestrel-rv32i single-cycle core, rung 1 of
the falcon suite. Derived from condensed study notes; emphasis is on what
the as-built kestrel core actually does and verifies, with the RISC-V
specification cited as the authority.
**Version:** 0.1
**Last Updated:** 2026-10-06
**Status:** Draft. Personal study notes.

---

## Overview

RV32I is the RISC-V base integer instruction set: thirty-seven
instructions, six instruction formats, thirty-one general-purpose
registers plus the hard-wired zero register, and a program counter. It is
small enough to hold in your head and rich enough to run real compiled
code. That combination makes it the canonical teaching ISA — and the
foundation rung of the falcon suite.

kestrel is the suite's rung-1 core: a single-cycle RV32I implementation in
which one instruction retires per clock and the whole machine — fetch,
decode, register read, execute, memory access, writeback — completes
inside that clock. There is no pipeline, no hazard logic, no trap
machinery, and almost no control state. What there is, is a datapath you
can trace by hand and a decode truth table you can read top to bottom.

This book condenses RV32I into the material needed to understand kestrel:
the instruction set itself (Chapter 2), the datapath (Chapter 3), the
control truth table (Chapter 4), the memory contract including the
hardware-misaligned policy (Chapter 5), the verification story — the
rv32ui battery, spike lockstep, and the riscv-formal proof that caught a
bug forty-two directed tests missed (Chapter 6) — and what the
single-cycle discipline costs, which is exactly what motivates rung 2,
merlin (Chapter 7).

## Document Structure

### Chapter 1: Introduction

- [01_introduction.md](ch01_introduction/01_introduction.md) - What this book is, what kestrel is, how to read the as-built core
- [02_the_falcon_ladder.md](ch01_introduction/02_the_falcon_ladder.md) - The four-rung suite, why kestrel is rung 1, what each rung teaches
- [03_conventions.md](ch01_introduction/03_conventions.md) - Notation, register names, halt-versus-trap terminology, citations

### Chapter 2: The RV32I ISA Quick Reference

- [01_formats.md](ch02_isa_quick_reference/01_formats.md) - The six instruction formats and how immediates are assembled
- [02_the_instruction_set.md](ch02_isa_quick_reference/02_the_instruction_set.md) - The thirty-seven base instructions, group by group
- [03_system_layer.md](ch02_isa_quick_reference/03_system_layer.md) - What kestrel does with FENCE, ECALL/EBREAK, MRET, and the CSR class

### Chapter 3: The kestrel Datapath

- [01_overview.md](ch03_datapath/01_overview.md) - Block-level tour, the module list, the complete state inventory
- [02_a_cycle_in_detail.md](ch03_datapath/02_a_cycle_in_detail.md) - One clock, end to end: fetch, decode, execute, writeback
- [03_control_state.md](ch03_datapath/03_control_state.md) - The five state elements and why there is no FSM
- [04_rvfi.md](ch03_datapath/04_rvfi.md) - The RVFI retire interface and how kestrel aggregates it

### Chapter 4: The Control Truth Table

- [01_the_control_bundle.md](ch04_control_truth_table/01_the_control_bundle.md) - The thirteen decode outputs and the default bundle
- [02_the_decode_table.md](ch04_control_truth_table/02_the_decode_table.md) - The full decode case as a table, every row

### Chapter 5: The Memory Contract

- [01_the_contract.md](ch05_memory_contract/01_the_contract.md) - The Harvard interface, word-wide buses, combinational reads
- [02_misaligned_data.md](ch05_memory_contract/02_misaligned_data.md) - The hardware-misaligned decision: rotation, the retry cycle, RVFI encoding
- [03_ialign_and_halt.md](ch05_memory_contract/03_ialign_and_halt.md) - IALIGN=32, the instruction-side misaligned halt, the four halt causes

### Chapter 6: Verification

- [01_testbench_and_golden.md](ch06_verification/01_testbench_and_golden.md) - The cocotb testbench, sampling contract, golden interpreter lockstep
- [02_rv32ui_battery.md](ch06_verification/02_rv32ui_battery.md) - The 42-test rv32ui-p-* battery, results table, verdict protocol
- [03_spike_lockstep.md](ch06_verification/03_spike_lockstep.md) - Spike 1.1.0 lockstep, the misaligned-build note, stream-diff details
- [04_riscv_formal.md](ch06_verification/04_riscv_formal.md) - The riscv-formal flow: wrapper, checks, depths, 42/42
- [05_the_cex_story.md](ch06_verification/05_the_cex_story.md) - The misaligned-jump counterexample: a real bug the battery missed

### Chapter 7: What kestrel Costs

- [01_what_kestrel_costs.md](ch07_costs_and_the_next_rung/01_what_kestrel_costs.md) - CPI 1 and its price: the whole machine on the critical path
- [02_merlin_teaser.md](ch07_costs_and_the_next_rung/02_merlin_teaser.md) - The five-stage answer and what carries over unchanged

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-06 | First draft |

: Version history
