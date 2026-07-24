---
name: uart-harness
description: The UART characterization-harness methodology - one host program running identically against cocotb sim and the FPGA. Sim transport, regmap-by-name, board bring-up gotchas (JTAG serials, ttyUSB). Use for any board characterization flow.
---

# uart-harness

READ FIRST: vault/handbook/fpga/uart-harness.md (the handbook is the repo's memory; this skill is the
signpost). One host program, sim + silicon; registers by name only. Board mechanics: vault/handbook/fpga/boards.md.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
