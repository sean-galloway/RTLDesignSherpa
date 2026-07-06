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

# Definitions and Acronyms

## Acronyms

| Acronym | Expansion                                              |
|---------|--------------------------------------------------------|
| AHB     | Advanced High-performance Bus (ARM AMBA)               |
| APB     | Advanced Peripheral Bus (ARM AMBA)                     |
| AP      | Auto-Precharge (DRAM column command modifier)          |
| APD     | Active Power Down                                      |
| AXI     | Advanced eXtensible Interface (ARM AMBA)               |
| BL      | Burst Length                                           |
| CA      | Command/Address (LPDDR2/3/4 multiplexed bus)           |
| CDC     | Clock Domain Crossing                                  |
| CL      | CAS Latency                                            |
| CMD     | Command                                                |
| CSR     | Control/Status Register                                |
| CWL     | CAS Write Latency                                      |
| DARP    | Dynamic Access Refresh Parallelization                 |
| DBI     | Data Bus Inversion                                     |
| DDR     | Double Data Rate                                       |
| DDR2    | Double Data Rate 2 (JESD79-2)                          |
| DFI     | DDR PHY Interface                                      |
| DPD     | Deep Power Down (LPDDR2)                               |
| FSM     | Finite State Machine                                   |
| FR-FCFS | First-Ready, First-Come-First-Served                   |
| HAPPY   | Hybrid Address-based Page Policy in DRAMs              |
| HAS     | Hardware Architecture Specification                    |
| LPDDR2  | Low Power DDR 2 (JESD209-2)                            |
| MAS     | Micro-Architecture Specification                       |
| MC      | Memory Controller                                      |
| MR / MRS | Mode Register / Mode Register Set command             |
| EMR / EMRS | Extended Mode Register / Extended MRS               |
| NOP     | No Operation                                           |
| ODT     | On-Die Termination                                     |
| OOO     | Out-of-Order                                           |
| PASR    | Partial Array Self-Refresh (LPDDR2 feature)            |
| PHY     | Physical Layer (DRAM electrical interface)             |
| PRE     | Precharge command                                      |
| PREA    | Precharge All Banks                                    |
| RD      | Read column command                                    |
| RDA     | Read with Auto-Precharge                               |
| REF     | Refresh command                                        |
| REFab   | All-Bank Refresh (LPDDR2)                              |
| REFpb   | Per-Bank Refresh (LPDDR2)                              |
| SDRAM   | Synchronous Dynamic RAM                                |
| SoC     | System on Chip                                         |
| SR      | Self-Refresh                                           |
| TCSR    | Temperature-Compensated Self-Refresh (LPDDR2)          |
| WR      | Write column command                                   |
| WRA     | Write with Auto-Precharge                              |
| ZQ      | Impedance Calibration (ZQ Calibration)                 |

---

## Defined Terms

**Bank Machine** — A finite state machine instance dedicated to one DRAM bank that enforces JEDEC timing constraints locally and tracks open-row state.

**Characterization Knob** — A build-time or runtime parameter intentionally exposed for performance sweeping during system characterization. Page policy and refresh policy are the two principal knobs in this controller.

**Command Encoder** — The module that translates the controller's internal generic command record into DFI wire signals. Two implementations: `ddr2_encoder` and `lpddr2_encoder`. Selected at elaboration time via `MEMTYPE`.

**FR-FCFS** — First-Ready, First-Come-First-Served. The baseline DRAM scheduling policy: ready commands beat unready, row-hits beat row-misses, older entries beat younger on ties. Established by Rixner et al. (ISCA 2000).

**Gear Output Stage** — The module that replicates a 1-phase internal command bus into `N_PHASES` parallel DFI output phases.

**Microprogram Engine** — The init sequencer: a small instruction-decoded FSM that reads a memtype-specific ROM (step table) and issues the corresponding control bits, MR loads, and commands.

**Page Hit / Row Hit** — An access whose target row matches the currently open row in the target bank. Avoids the tRP + tRCD penalty.

**Page Conflict / Row Miss** — An access whose target row differs from the currently open row in the target bank. Pays tRP + tRCD before the access can begin.

**Page Policy** — The strategy for when to close an open row. See `PAGE_POLICY` parameter.

**Row-Hit Caching** — Storing the row-hit / row-miss decision on each transaction at queue insertion time, rather than recomputing each scheduler tick.

**Transaction Queue** — The pending-request buffer between the AXI frontend and the scheduler.
