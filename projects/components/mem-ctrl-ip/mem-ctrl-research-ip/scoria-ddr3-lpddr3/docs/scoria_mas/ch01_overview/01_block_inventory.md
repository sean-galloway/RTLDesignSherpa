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

# Block Inventory

The controller is a three-tier tree — FUBs under macro layers under a top —
mirroring pumice's shape with the `scoria_` prefix. `scoria_top` wraps
`scoria_core` (the three layers) plus the PeakRDL-generated `scoria_csr`
register block; configuration reaches the core **by name from `hwif_out.*`**,
so there are no config ports on the core.

## Top and macro tier

| Module | Location | Function | Status |
|---|---|---|---|
| `scoria_top` | `rtl/top/` | core + CSR block wrapper; presents host AXI4 and the DFI pin bus | complete, board-exercised in simulation |
| `scoria_top_geared` | `rtl/top/` | width-gearing wrapper: formally verified AXI data-width converters around `scoria_top`; bypassed (`g_direct`) when host width equals the DFI word width | complete |
| `scoria_core` | `rtl/top/` | the three-layer assembly, wired bottom-up | complete |
| `scoria_axi4_layer` | `rtl/macro/` | host front-end: burst chopping, intakes, write/read CAMs, read-return ring, snarf | complete (was `scoria_axi4_ifc` pre-MC-001) |
| `scoria_scheduler_layer` | `rtl/macro/` | the command brain: arbiter, timers, page policy, refresh/ZQ, init/leveling, output FIFO | complete (was `scoria_mem_cmd_scheduler` pre-MC-001) |
| `scoria_dfi_layer` | `rtl/macro/` | the PHY side: the single CDC, command path, write serializer, read aligner | complete |

: Table 1.1: Top and macro tier

## FUB tier

Every active FUB gets its own page in Chapter 2, in datapath order. The
Parent column is the instantiating layer — the page to read for the wiring
around it.

| Module | Parent | Function (one line) | Page |
|---|---|---|---|
| `scoria_axi_burst_chopper` | `scoria_axi4_layer` | FSM-free AXI address-channel burst splitter | 2.4 |
| `scoria_wr_splitter` | `scoria_axi4_layer` | write-side AW chop + WLAST reframing with zero-strobe padding | 2.5 |
| `scoria_wr_intake` | `scoria_axi4_layer` | skid buffers, decoded CAM push, ragged-burst reject | 2.6 |
| `scoria_wr_data_cam` | `scoria_axi4_layer` | write scheduling window + data SRAM + snarf source | 2.7 |
| `scoria_rd_intake` | `scoria_axi4_layer` | AR snarf probe, two-stage admit, AR-order merge back to R | 2.8 |
| `scoria_rd_cmd_cam` | `scoria_axi4_layer` | read scheduling window, carries the return-ring ticket | 2.9 |
| `scoria_rd_return_ring` | `scoria_axi4_layer` | AR-order tickets over in-flight read data | 2.10 |
| `scoria_addr_mapper` | `scoria_axi4_layer` (via the intakes) | byte offset to {rank, bank, row, col}, optional bank XOR-hash | 2.11 |
| `scoria_page_policy` | `scoria_scheduler_layer` | auto-precharge decisions, idle-timeout close, page telemetry | 2.12 |
| `scoria_bank_timer` / `scoria_bank_timers` | `scoria_scheduler_layer` | per-(rank,bank) JEDEC countdown timers, no FSM | 2.13 |
| `scoria_global_timers` | `scoria_scheduler_layer` | rank-global tFAW/tRRD and shared tWTR/tRTW/tCCD, in the fixed form | 2.14 |
| `scoria_cmd_arbiter` | `scoria_scheduler_layer` | FR-FCFS pick with maintenance preemption and a final safety gate | 2.15 |
| `scoria_refresh_ctrl` | `scoria_scheduler_layer` | tREFI credit machine: REFab/REFpb, elastic and TCR modes | 2.16 |
| `scoria_zq_ctrl` | `scoria_scheduler_layer` | periodic ZQCS as maintenance traffic, deferral policy | 2.17 |
| `scoria_init_sequencer` | `scoria_scheduler_layer` | RESET#/MR order for DDR3 and LPDDR3, ZQCL closes init | 2.18 |
| `scoria_mode_register` | `scoria_scheduler_layer` | per-rank MR shadows with live decode of CL/CWL/BL/AL/WR | 2.19 |
| `scoria_wrlvl_ifc` | `scoria_scheduler_layer` | firmware-driven write-leveling interface — no search loop | 2.20 |
| `scoria_dfi_cmd_path` | `scoria_dfi_layer` | abstract commands to DFI phases; does not pace | 2.21 |
| `scoria_dfi_cmd_formatter` | `scoria_dfi_layer` | op to DFI pins: DDR3 truth table, LPDDR3 CA bus | 2.22 |
| `scoria_dfi_wr_serializer` | `scoria_dfi_layer` | t_phy_wrlat delay line to `dfi_wrdata_en` | 2.23 |
| `scoria_dfi_rd_aligner` | `scoria_dfi_layer` | `rddata_en` windows, capture credits, return push | 2.24 |
| `scoria_dfi_cdc` | `scoria_dfi_layer` | the only ctl↔phy boundary: five async FIFOs | 2.25 |
| `scoria_powerdown_ctrl` | — (dormant) | idle-detect → PDE/SR state machine | 2.26 |
| `scoria_dfi_signal_pack` | — (dormant) | registered DFI pack stage owning `dfi_dram_clk_disable` | 2.26 |

: Table 1.2: The FUB tier with layer assignments

## The three blocks that are not ordinary FUBs

**`scoria_csr`** is generated from `rtl/macro/scoria_csr.rdl` by PeakRDL. It
is not designed, it is compiled; the register truth lives in
`regs/generated/docs/scoria_csr.md` and the address-map summary is in Chapter
3. TASK-001's mode-select fields (elastic refresh, TCR derate, ZQ placement)
are ordinary fields in it.

**`scoria_cmd_history_checker`** is a verification-side block that
re-derives JEDEC spacing from the issued command stream and fatals on a
violation. It is generate-gated inside the scheduler layer behind
`CMD_HISTORY_EN` (default off) and exists in both scheduler-layer and DFI-wire
variants. It is documented with its host on the scheduler-layer page, not
given a page of its own — its mechanism is inherited from pumice, and andesite
carries its DDR4 growth.

**The dormant pair** (`scoria_powerdown_ctrl`, `scoria_dfi_signal_pack`) is
real, lint-closed RTL that nothing instantiates — deliberately, and the
reasoning is on their shared page (2.26). They are the starting point for
LPDDR3 power-down work, and they stay in the tree for that reason.

## How to read Chapter 2

The pages run in dataflow order: the three layer assemblies first (2.1-2.3,
the structural map), then the request path from AXI to CAMs (2.4-2.10), the
scheduling support blocks (2.11-2.15), the maintenance and init/training
blocks (2.16-2.20), the DFI blocks (2.21-2.25), and the dormant pair last
(2.26). Every page stands alone; the layer pages are the ones to read first
if the question is "who talks to whom."
