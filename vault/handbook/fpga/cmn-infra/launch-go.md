---
title: Launch with one GO
summary: Every FPGA environment starts all its engines with ONE register write; a UART write takes >= 16 ms, so two start writes never overlap two engines.
---

# Launch with one GO

**Rule (owner, 2026-11-27): every FPGA environment has a GO bit.** The host
stages every engine's configuration, then ONE register write starts all the
engines a measurement runs, in the same harness cycle. An engine's own start
bit is never how a multi-engine measurement launches.

## Why

A register write over the UART bridge is a round trip. Measured on the
Genesys2 (2026-11-26, 115200 baud): 15.9 ms at best, 216 ms mean over 20
writes; a read is 16.0 ms. At a 100 MHz harness clock that is >= 1.6M cycles
between two writes, and most runs finish in fewer. Two start writes therefore
run two engines one after the other, never together.

The failure it caused: the cache-ip rigs (jet, amber, the reference rig)
started their two cycle injectors with `start_ci("ci0")` then
`start_ci("ci1")`. Every "dual" board sweep from bin 1 on was injector 0
alone, then injector 1 alone on a warm peer -- no contention, no snoop of a
line in flight, nothing the coherence fabric exists for (cache-ip common-ip
BUG-001). Nothing flagged it: the runs completed, the CRCs were stable from
bin to bin, and the per-bin cycle identities held, because the sequential
runs were themselves deterministic. It surfaced only when a hot-set cell
built to reach a coherence corner reached it in sim (12,380 lines supplied)
and not on the board (8); the sim with injector 1 started after injector 0
reproduced the board's 22,874 transactions exactly.

The sim cannot show this on its own: its AXI-Lite driver issues the two
writes tens of cycles apart, so both engines overlap and the sim looks
right. A sim test of the launch has to check the start CYCLE (below), not
the result.

## The pattern

- A write-only GO register in the harness CSR, one single-cycle pulse bit
  per engine, so one write starts any subset. The best-documented instance
  is chargen's `GO` (`projects/fpga-systems/rtl/mem_char_framework/rtl/chargen_regs.rdl`,
  "LAUNCH IS GLOBAL"; fan-out in `char_engine_block.sv`). Others: rapids
  `CSR_GO`, bridge-stress `CTRL.GO`, STREAM's `KICK_ENABLE` (in the DUT),
  gatling's run mask, the cache-ip harnesses' `GO` at 0x064 (bit k pulses
  injector k).
- Engines stage on their CSRs and do nothing until GO. Where an engine keeps
  its own start bit (the cache-ip `amber_cycle_injector` keeps CTRL.run for
  its unit tests), the host never uses it to launch a measurement.
- The host's launch call is the GO write and nothing else
  (`JetDriver.start_all`, `ddr2_char.go`).
- A sim test per environment proves the launch: stage, check nothing
  started, GO, and require every engine's run state to rise on ONE clock
  edge; a GO naming one engine starts only that one. Mutation: delay one
  engine's GO by a flop and the test must fail (the cache-ip test reports
  "started the injectors in different cycles: 345 vs 346").

## Related

[[uart-harness]], [[host-stack]], [[board-vs-rtl]].
