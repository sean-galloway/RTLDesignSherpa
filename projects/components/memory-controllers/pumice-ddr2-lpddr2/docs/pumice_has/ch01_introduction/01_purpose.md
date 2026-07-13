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

# Purpose and Scope

## Document Purpose

This Hardware Architecture Specification (HAS) defines the high-level architecture of the DDR2 / LPDDR2 Family Memory Controller. It serves as the primary reference for:

- **System Integration** — understanding the controller's external interfaces and system-level requirements
- **RTL Implementation Planning** — module decomposition, interface contracts, and parameter sweeps
- **Verification Planning** — system-level test scenarios and the characterization sweep matrix
- **Driver Development** — programming model and APB register interface

This document complements the upcoming Micro-Architecture Specification (MAS), which will provide detailed block-level implementation specifics, signal-level pinouts, and timing diagrams.

---

## Scope

This HAS covers a single unified controller that supports both DDR2 and LPDDR2 memory. The memory type is a runtime CSR selection (`PHY_TIMING.memtype`: 0 = DDR2, 1 = LPDDR2). The controller is built as three layers under `pumice_core`:

- **`pumice_axi4_ifc`** — AXI4 slave host interface: dumb write/read intakes, an address mapper, a write-data CAM (write buffer + read-your-write snarf source), and a read-command CAM (read reorder buffer).
- **`pumice_mem_cmd_scheduler`** — the command-scheduling layer: a single command arbiter (`pumice_cmd_arbiter`, open-page decision inline), per-(rank,bank) FSM-free JEDEC "safe" timers (`pumice_bank_timers` / `bank_timer`), global turnaround timers (tFAW / tRRD / tWTR / tRTW / tCCD), a refresh controller, an init sequencer (DDR2 and LPDDR2 JEDEC MR init), and a mode-register shadow (CL / CWL / BL / AL decode).
- **`pumice_dfi_layer`** — a single controller-to-PHY clock crossing (`pumice_dfi_cdc`, async FIFOs) plus the DFI-domain command path (`dfi_cmd_formatter` / `dfi_signal_pack`), write serializer, and read aligner, presenting the DFI v2.1 pin bus.

Configuration (timings, phases, page policy, address map, memtype) is delivered by name from a PeakRDL-generated CSR register block (`pumice_csr`) instantiated in `pumice_top`. An optional outer wrapper, `pumice_top_geared`, gives the host a free AXI data width by inserting the repository's formally-verified `axi4_dwidth_converter_wr` / `_rd` between a host-width slave and the fixed-width core.

The differences between DDR2 and LPDDR2 are the command encoding (DDR2 ras/cas/we vs the LPDDR2 10-bit CA bus, both in `dfi_cmd_formatter`), the init MR sequence in `init_sequencer`, and a small number of mode-register decode differences. Both memtypes pass the full simulation suite; everything else is shared.

---

## Design Philosophy

This controller is intended as a **characterization-first** design. Algorithmic choices that have meaningful research-backed alternatives — page policy, refresh policy, refresh deferral depth, address mapping — are exposed as CSR fields rather than hardcoded. The verification plan includes a benchmark sweep over representative AXI traffic patterns to pick defaults from data, not assumption.

The principal characterization knobs, all programmed by name through the CSR block, are:

- **Page policy** (`REFRESH_TUNING.page_policy_or`: OPEN / CLOSE / HAPPY_HYBRID) — where HAPPY_HYBRID is the address-bit-based page-closure predictor from Ghasempour et al. (2015). The open-page decision itself is inline in `pumice_cmd_arbiter`.
- **Refresh policy** (`REFRESH_TUNING.refpb_policy_or`: ROUND_ROBIN / OLDEST_FIRST / DARP) — where DARP is the dynamic access refresh parallelization scheme from Chang et al. (HPCA 2014).
- **Address map** (`ADDR_MAP.bank_lsb`, `hash_en`, `hash_seed`) — a single knob that slides the bank field within the word address, subsuming the classic ROW_MAJOR / BANK_INTERLEAVE schemes, with an optional bank XOR-hash.

These are described in detail in Chapter 5.

---

## Audience

This document assumes the reader is familiar with:

- AXI4 protocol semantics (handshakes, burst types, ID-based ordering)
- DFI v2.1 specification (control / write-data / read-data sub-interfaces)
- JEDEC DDR2 (JESD79-2F) and LPDDR2 (JESD209-2F) command tables
- Basic memory-controller concepts (open vs closed page policy, refresh deadlines, bank state machines)

Readers new to these topics should first consult the companion `paging-refresh-notes.md` in the family working area for an entry-point bibliography.
