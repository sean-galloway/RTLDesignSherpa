<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Product Requirements Document (PRD)
## scoria — DDR3/LPDDR3 Family Memory Controller

**Version:** 1.0
**Date:** 2026-10-03
**Status:** Active development — RTL verified in simulation; board bring-up in progress
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

scoria is a unified, parameterized memory controller for DDR3 SDRAM and
LPDDR3 SDRAM, presenting an AXI4 slave and APB CSR interface to the host and
a DFI v3.1 master to the PHY. It is the second member of the repository's
memory-controller family: pumice (DDR2/LPDDR2) is the architecture it is
derived from and the evidence base it inherits.

The controller RTL is complete and verified in simulation against a DFI bus
functional model. The target board — Digilent Genesys 2 with a Kintex-7 and
two MT41J256M16 devices at DDR3-800 — has a build flow with passing lint, but
no bitstream yet: the first out-of-context synthesis found the 100 MHz design
point missing timing by ~2 ns (BUG-003, the current P1).

### 1.1 Status Snapshot (measured 2026-10-01)

| Item | State |
|---|---|
| HAS | v0.8, reconciled against the RTL |
| RTL | Complete: 26 FUBs + `scoria_core`/`scoria_top`/`scoria_top_geared` |
| Verification | 221 tests passing, 9 formal blocks, top tier AXI-in/DFI-out |
| Board | Build flow + harness exist, lint passing; no bitstream; 100 MHz timing open (BUG-003) |
| LPDDR3 | Specified; the exercised design point is DDR3-only so far |

## 2. Documentation Structure

This PRD is the product overview. The technical specifications live beside
it, and the work ledger lives in the vault:

| Document | Where | Role |
|---|---|---|
| HAS (v0.8) | [docs/scoria_has/scoria_has_index.md](docs/scoria_has/scoria_has_index.md) | **Architecture specification** — binding; the PRD cites it |
| Design requirements | [docs/design-requirements.md](docs/design-requirements.md) | Binding delta analysis against JESD79-3F / JESD209-3C / DFI v3.1 |
| Published HAS book | [docs/DDR3_LPDDR3_HAS_v0.8.pdf](docs/DDR3_LPDDR3_HAS_v0.8.pdf) | Styled PDF of the HAS |
| CSR documentation | [regs/generated/docs/scoria_csr.md](regs/generated/docs/scoria_csr.md) | Generated from `rtl/macro/scoria_csr.rdl` |
| Work items | [vault/Tasks/scoria-ddr3-lpddr3/](../../../../vault/Tasks/scoria-ddr3-lpddr3/INDEX.md) | Tasks and bugs, one file per item |

## 3. Target Design Point

Fixed by HAS Chapter 2.4 (v0.5, Sean: "assume k7ddrphy on genesys2 if it
helps"); the parameters the DUT is verified with:

| Item | Value |
|---|---|
| Board / FPGA | Digilent Genesys 2 / Kintex-7 (xc7k325t) |
| PHY | LiteDRAM `s7ddrphy` K7DDRPHY, 4 phases |
| DRAM | 2 x MT41J256M16, 32-bit bus, single rank |
| Geometry | 8 banks, 32768 rows, 1024 columns |
| Clocks | 100 MHz system, 400 MHz DRAM CK (1:4 gearing) |
| Data rate | DDR3-800 — 3200 MB/s theoretical peak |

**Bandwidth reporting rule:** any measured bandwidth is quoted beside the
3200 MB/s peak; a percentage without the peak is not a result (HAS Ch 2.4).

## 4. Architecture Overview

scoria mirrors pumice's three-tier shape (FUBs under macros under a top).
Every block is marked **INHERITED**, **MODIFIED** or **NEW** against pumice
in the HAS; the summary:

- **Inherited (21 of 24 FUBs):** the AXI4 front end, FR-FCFS arbiter, bank
  and global timers, the CAM/intake/ring data paths, refresh (with its
  `REFpb` bank rotor), power-down, and the DFI datapath CDC.
- **Modified:** the init sequencer (DDR3 `RESET#`, MR0-MR3, JEDEC order),
  the mode-register block, the DFI command formatter (`ZQCL`, `ZQCS`,
  `PREA`), the DFI layer (the v3.1 control surface), the command scheduler
  (admits ZQ maintenance demand), and the CSR block.
- **New:** `scoria_zq_ctrl` (periodic `ZQCS` as request/grant maintenance
  traffic) and `scoria_wrlvl_ifc` (the write-leveling interface — handshake,
  timing windows and telemetry, **no search loop**; the search is firmware,
  decision D2).

Two inherited FUBs (`powerdown_ctrl`, `dfi_signal_pack`) are retained
uninstantiated on the measured DDR3 parity argument recorded in the HAS
(Ch 3.1) and TASK-003; they become load-bearing for LPDDR3 Deep Power Down.

## 5. Interfaces

| Interface | Direction | Notes |
|---|---|---|
| AXI4 slave | host → controller | 1:1 read/write intakes, in-order commit; width-geared variant via `scoria_top_geared` |
| APB slave | host → controller | PeakRDL-generated CSR block (`scoria_csr.rdl`); registers accessed by name through the generated regmap |
| DFI v3.1 master | controller → PHY | 4 phases, `DFI_RATE = 4`; presents `dfi_reset_n` and both v3.1 data-phase chip selects (constant at `NUM_RANKS = 1`) |

Deliberately unimplemented: DFI v3.1's DDR4/LPDDR4 surface (ACT_n, bank
groups, CA parity, DBI, CA training) — absence is a decision on the record
(HAS Ch 4).

## 6. Verification Status

**Boundary:** the DV repository's DFI bus functional model in cocotb,
configured to the target geometry (8 banks, 32768 rows, 1024 columns,
32-bit bus, four phases). No board is required to verify scoria.

**Measured 2026-10-01** (quoted as evidence in BUG-003): **221 tests
passing, 9 formal blocks**, top tier running AXI in and DFI out with data
through the whole datapath. Suites live in `dv/tests/`:

| Tier | Where | Covers |
|---|---|---|
| fub | `dv/tests/fub/` | individual blocks |
| macro | `dv/tests/macro/` | multi-block composition (e.g. scheduler, DRAM config consistency) |
| top | `dv/tests/top/` | `scoria_core` against the DFI BFM |

**Coverage plan still open** (HAS Ch 6): init-order assertion, ODT during
init, write leveling as a protocol including the `tWLMRD` timeout path, and
per-bank refresh retention re-established for `REFpb`. **Formal debt:**
two proofs are weak (dfi_cdc 2/7 live assertions; wr_data_cam's
data-integrity property guarded off) — TASK-006.

## 7. Known Issues

| ID | Summary | Priority |
|---|---|---|
| [BUG-003](../../../../vault/Tasks/scoria-ddr3-lpddr3/bug/open/BUG-003.md) | 100 MHz design point misses by ~2 ns out-of-context (WNS −2.022 ns; 85% route, 31 logic levels across the arbiter/CAM boundary). Indicated first move: floorplan the arbiter with its CAMs; the RTL cone-break is the risky second lever | P1 for the board |

Full ledger: [vault/Tasks/scoria-ddr3-lpddr3/](../../../../vault/Tasks/scoria-ddr3-lpddr3/INDEX.md).

## 8. Development Status and Roadmap

**Now:** BUG-003 timing closure (floorplanning experiment), then a Genesys 2
bitstream and bring-up against the LiteDRAM reference behavior.

**Next:** HAS → 1.0 (the three items in HAS Ch 6: `tWLMRD` maximum policy
value; block-by-block INHERITED/MODIFIED confirmation against the RTL; CSR
map finalized from the RDL — TASK-008), formal debt (TASK-006), and the
standing no-assertions-in-RTL decision for four input-contract checks
(TASK-007).

**Later:** bounded tranche (elastic refresh / TCR / ZQ placement) landed behind
CSRs; survey and deferred conditions in `design-requirements.md` §6; deferred
tranche filed as TASK-009; LPDDR3 bring-up (the second memtype; makes the dormant
power-down FUBs load-bearing); and multi-rank (the v3.1 data-phase chip selects
stop being constants).

## 9. Success Criteria

- A Genesys 2 bitstream meets timing at the 100 MHz design point (BUG-003
  closed or the design point restated by the owner).
- The board passes a memory test against the LiteDRAM DDR3 reference on the
  same hardware.
- Measured bandwidth published with the 3200 MB/s peak beside it.
- HAS reaches 1.0 with every marking confirmed or corrected.

---

**Document Version:** 1.0
**Last Updated:** 2026-10-03
**Owner:** RTL Design Sherpa Project

## Navigation

- **← Back to Root:** `/PRD.md`
- **Architecture spec:** [docs/scoria_has/scoria_has_index.md](docs/scoria_has/scoria_has_index.md)
- **Work items:** [vault/Tasks/scoria-ddr3-lpddr3/](../../../../vault/Tasks/scoria-ddr3-lpddr3/INDEX.md)
