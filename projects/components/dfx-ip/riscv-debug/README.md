# riscv-debug

**Status:** Scaffold (2026-10-11) — spec pending (HAS ch03/ch04)
**Plane:** core override — "riscv needs override control deep down"

Per the RISC-V Debug Specification (the authoritative document; cite it
by section):

- `dfx_dtm` — debug transport module: JTAG → DMI request/response.
- `dfx_dm` — debug module: halt/resume/step control, abstract commands
  against core registers, program buffer, the `dcsr`/`dpc`/`dscratch`
  surface.
- Core-side debug mode integration per falcon rung (EBREAK/DRET entry/
  exit, precise halt) — a per-core MAS/MAS-erratum concern; this
  component owns the shared DTM/DM and the integration contract.

Consumers: falcon rungs (kestrel → garuda) and hive-serv (VexRiscv +
SERV carry core-native debug mode; the house DTM/DM is their transport).

Reference design: Zhang, *RISC-V Architecture and DSP Processor Design*
ch8 (DTM/DM structure walkthrough); the RISC-V Debug Specification
remains the wire-and-CSR authority.
