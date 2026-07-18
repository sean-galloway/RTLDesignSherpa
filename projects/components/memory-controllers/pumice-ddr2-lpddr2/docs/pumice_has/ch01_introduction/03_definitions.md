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

**Bank Timer** — A per-bank JEDEC "safe" timing tracker (`bank_timer`). It is *not* a finite state machine: it is a set of preset/decrement countdown timers (tRCD, tRAS, tRC, tRP, precharge-block) plus a small open-row register and a single auto-precharge bit. The per-command `safe_*` outputs are combinational off the timers (one register stage). `pumice_bank_timers` stamps one instance per (rank, bank).

**Characterization Knob** — A build-time or runtime CSR field intentionally exposed for performance sweeping during system characterization. Page policy, refresh policy, and address map are the principal knobs in this controller.

**Command Formatter** — `dfi_cmd_formatter`: the module that translates the controller's abstract command record into DFI wire signals. A single module with a memtype branch — DDR2 drives ras/cas/we; LPDDR2 packs the 10-bit CA bus (two edges) onto `dfi_address`. `dfi_signal_pack` performs the final per-phase wire packing.

**Command Arbiter** — `pumice_cmd_arbiter`: the single command-pick core. It scans CAM readiness against the bank and global timers, applies the page policy (the open-page decision is inline here), and emits one abstract DRAM command per cycle.

**FR-FCFS** — First-Ready, First-Come-First-Served. The baseline DRAM scheduling policy: ready commands beat unready, row-hits beat row-misses, older entries beat younger on ties. Established by Rixner et al. (ISCA 2000).

**Gearing (two senses)** — (1) The internal DFI-rate split: one AXI/DFI word is spread across `DFI_RATE` DRAM beats and packed to per-phase buses in `dfi_signal_pack` / the DFI layer. (2) Host-width gearing: `pumice_top_geared` inserts formally-verified AXI data-width converters so the host AXI data width can differ from the core width.

**Init Sequencer** — `init_sequencer`: the cold-boot engine that issues the memtype-specific JEDEC MR/init sequence, driving MR loads and commands and holding off traffic until init completes.

**Page Hit / Row Hit** — An access whose target row matches the currently open row in the target bank. Avoids the tRP + tRCD penalty.

**Page Conflict / Row Miss** — An access whose target row differs from the currently open row in the target bank. Pays tRP + tRCD before the access can begin.

**Page Policy** — The strategy for when to close an open row. Programmed via `REFRESH_TUNING.page_policy_or` (OPEN / CLOSE / HAPPY_HYBRID); the decision is inline in `pumice_cmd_arbiter`.

**Command CAMs** — The two content-addressable buffers that hold in-flight requests between the AXI interface and the scheduler: `pumice_wr_data_cam` (write data buffer + snarf source) and `pumice_rd_cmd_cam` (read reorder buffer). Both store burst data in an SRAM with FIFO-fed / oldest-pick streaming read engines and no active-slot state latch.
