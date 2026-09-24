# TASK-002: gate the monitor regfile on a parameter (present + decoded)
> **Was `STREAM-MONREGS` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** open 2026-08-06

`stream_regs.rdl` includes and instantiates the monitor regfile unconditionally:

```
line  22:  `include "stream_mon_regs.rdl"
line 758:  stream_mon_regs MON @ 0x1000;
```

There is no parameter deciding whether that block is PRESENT or DECODED, while
`USE_AXI_MONITORS` already decides whether the monitors it configures exist.
The two must move together.

**Why it matters more than area.** On a `USE_AXI_MONITORS=0` build the monitor
registers still accept writes and read back the written value -- driving
nothing. A host arms `RDMON_TIMEOUT`, reads it back correctly, and concludes the
monitor is configured. There is no monitor. Read-back success is normally the
strongest evidence a host has that configuration took, and here it is
affirmatively misleading.

This is live: `build-perf` ships `USE_AXI_MONITORS=0` today, with the whole MON
window responding.

**Wanted:**
- A parameter (`USE_MON_REGS`, defaulting to `USE_AXI_MONITORS`) that gates both
  the regfile instantiation and its address decode.
- With it 0, accesses to 0x1000+ should return the bus error / no-response the
  decode already produces for unmapped space -- so "not built" is
  DISTINGUISHABLE from "built and set to zero". Silence is the honest answer.
- RAPIDS already has the hookup-parameter shape for this
  ([[project_rapids_beats_resync]]: monitors relocated to 0x1000 in a separate
  `include`d regfile under one APB slave with a USE_AXI_MONITORS hookup param).
  Follow it rather than inventing a second pattern.

**Test that should exist alongside it:** the monitors-off build must FAIL to
read the MON window. `dv/tests/top/test_stream_top_mon_cfg.py` covers the
monitors-on direction (register field -> cfg port); the negative direction needs
the parameter first.

Found while writing that test: with monitors ON, the MON window at 0x1000+ needs
`APB_ADDR_WIDTH=13`. At the 12-bit default every monitor register returns
0xDEADBEEF, which is indistinguishable from a hookup failure until you read back
-- see [[TASK-001]] item 1 for the same class of problem in map form.

---
