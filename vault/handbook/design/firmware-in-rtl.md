---
title: Firmware images inside RTL
summary: An RV32 image baked into a ROM is RTL; three traps from rapids-g - linker relaxation rewriting a jalr base, unreachable policy found by mutation, and poll phase in perf A/Bs.
---

# Firmware images inside RTL

When a design runs firmware from a ROM it builds itself (rapids-g's
`sched_g.S` on gatling, generated into `sched_g_fw.svh` by
`bin/gen_rapids_g_fw.py`), the image is part of the RTL: it is built by a
generator ([[generated-rtl-discipline]]), it goes through the same regression,
and a mutant in it must fail a test like a mutant in the .sv. Three traps
from rapids TASK-037 (2026-10-23):

**1. Linker relaxation rewrites a lone `%lo` off a register.** A jump table
reached as `jalr zero, t3, %lo(ptab)` (index in t3, table below 2 KB of an
image linked at 0, so no base register) assembled correctly, then the
linker's relaxation pass treated the `%lo` as the second half of a `lui`
pair and rewrote the base register to x0 - every dispatch jumped to the
table's first entry. `objdump` of the `.o` showed `jr t3` with
`R_RISCV_LO12_I` + `R_RISCV_RELAX`; the `.elf` showed `jr 344(zero)`.
Fix: `.option norelax` in the source (the image does not need relaxation),
and have the generator check the table's end symbol is below 0x800, so a
growing image fails the build instead of mis-jumping. Read the LINKED
disassembly of any hand-addressed jump, not the object's.

**2. Mutation finds policy no state can reach - make it a fault, not a
handler.** The firmware kept a "hand path" (arm a descriptor in XFER, route
it out of COMPLETE, start it from FETCH) from before pre-validation. A mutant
in each survived every test; tracing why showed nothing can reach them:
every valid head is staged armed, and the firmware takes a head itself only
when it declined it, which the latch also calls invalid. Unreachable policy
cannot be tested, so it rots; replacing it with one fail-safe (`fw_fault`:
an error packet carrying STATUS, then CH_ERROR) turns "impossible" into
"visible". The other survivor of that run was a mutant live only in a
configuration the bench never built (two channels per hart) - the fix there
was a bench axis, not a code change. Ask which of the two a survivor is
before touching code.

**3. A firmware perf A/B must start both images from the same cycle.** A
poll loop samples events once per pass, so when an earlier scenario in the
same simulation finishes sooner, every later scenario starts at a different
phase of the barrel and its time moves by up to a poll pass with no code
change (+23 clocks on an 84,000-clock point). Run the point alone in both
images (rapids-g's `PERF_ONLY`); identical cycle counts there settle it.
