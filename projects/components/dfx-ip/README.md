# DFX-IP — Design-for-X Infrastructure (Debug First)

**Status:** Scaffold (2026-10-11) — HAS started, no RTL yet
**Family role:** Debug and test infrastructure shared by every component line

DFX-IP houses the house-wide debug port: the pieces that let a developer
(or an agent) see into and reach into any system from outside, without
modifying the cores or blocks being observed.

The design is built on three planes, two of which live here (the third
already exists house-wide):

| Plane | Mechanism | Lives here? |
|---|---|---|
| **Observation** | `*_monlite` drop-and-count taps on measured paths (never stalls the port) | No — house-wide already (amber D8 principle: the observer must not perturb what it measures) |
| **Config poke** | JTAG → `jtag-axil-agent` → AXIL4 master → any component's CSRs | **Yes — `jtag-axil-agent/`** |
| **Core override** | JTAG → `riscv-debug` (RISC-V Debug Spec DM) → halt/resume/step + register access deep in the cores | **Yes — `riscv-debug/`** |

Owner ruling (2026-10-11), the access-model seed: **riscv needs override
control deep down; most other IP only needs access to their configs.**
The config plane is therefore the common case; the override plane exists
for the falcon rungs and hive-serv cores.

Components:

- [`jtag-tap/`](jtag-tap/) — IEEE 1149.1 TAP (TCK domain): FSM, IR/DR
  chains; dedicated-pin and `BSCANE2` (7-series shared JTAG) wrappers.
- [`jtag-axil-agent/`](jtag-axil-agent/) — config-plane agent: TCK-domain
  command register file + AXIL4 master FSM; one poke per command.
- [`riscv-debug/`](riscv-debug/) — override-plane debug module per the
  RISC-V Debug Specification: DTM/DM, abstract commands, program buffer,
  core debug mode (EBREAK/DRET, dcsr/dpc/dscratch).

Overarching spec: [`docs/dfx_has/`](docs/dfx_has/dfx_has_index.md)
(hardware architecture specification — started 2026-10-11).

Future scope (not started): the test plane — scan/BIST — chapters reserved
in the HAS index.
