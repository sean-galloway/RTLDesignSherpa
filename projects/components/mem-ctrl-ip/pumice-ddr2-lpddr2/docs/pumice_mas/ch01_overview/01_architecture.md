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

# Architecture and Datapath

This chapter is the implementation-level architectural orientation: the live
three-layer hierarchy, the read/write datapath flow, and the clocking
topology. Per-macro detail is in section 2; per-interface detail is in
section 3.

## Layer Hierarchy

The controller is a **three-layer core** wrapped by a top that adds the
PeakRDL-generated register block. The top-of-tree is `pumice_top`
(`rtl/top/pumice_top.sv`), with an optional host-width wrapper
`pumice_top_geared` above it:

```
pumice_top_geared (rtl/top/pumice_top_geared.sv)   -- OPTIONAL host-width wrapper
  |- axi4_dwidth_converter_wr/_rd (formal IP; only when HOST_AXI_DATA_WIDTH != DW)
  |- pumice_top (rtl/top/pumice_top.sv)
       |- pumice_csr (regs/generated/rtl/, PeakRDL passthrough cpuif)
       |- pumice_core (rtl/top/pumice_core.sv)
            |- pumice_axi4_ifc          (rtl/macro/pumice_axi4_ifc.sv)
            |- pumice_mem_cmd_scheduler (rtl/macro/pumice_mem_cmd_scheduler.sv)
            |- pumice_dfi_layer         (rtl/macro/pumice_dfi_layer.sv)
```

`pumice_core` wires the three macros, built bottom-up:

| Macro (module)             | Role                                                          | Chapter |
|----------------------------|---------------------------------------------------------------|---------|
| `pumice_axi4_ifc`          | Host AXI4 slave + burst splitters + write/read CAMs + snarf    | 2.1     |
| `pumice_mem_cmd_scheduler` | Arbiter + per-bank/global timers + refresh + init + mode reg   | 2.2     |
| `pumice_dfi_layer`         | Single async-FIFO CDC + DFI-clock command/write/read datapath  | 2.4     |

The data path is **not** a standalone macro. Write and read burst buffers live
in the CAMs inside `pumice_axi4_ifc` (SRAM-backed, de-FSM'd streaming readers);
the DFI-clock serializer / aligner live in `pumice_dfi_layer`. Section 2.3
documents this split in place of the old `data_path_macro`.

Configuration (timings, DFI phases, page policy, address map) is delivered to
`pumice_core` on ports, driven **by name** from the CSR `hwif_out.*` fields in
`pumice_top`. There are no config ports on `pumice_top` other than the register
cpuif -- software programs every timing/phase/policy through the register bus.

## Read / Write Datapath: AXI -> split -> intake -> CAM

The host AXI4 face is `pumice_axi4_ifc`. Each host burst is first split at
DRAM-burst-byte boundaries by the shared `axi_master_wr_splitter` /
`axi_master_rd_splitter` (one DRAM burst per split command), then handed to the
dumb 1:1 intakes:

- `pumice_wr_intake` (`axi4_slave_wr` + AW-meta FIFO + wr-data FIFO + `addr_mapper`)
  pushes `(bank, row, col, id)` plus write data into `pumice_wr_data_cam`.
- `pumice_rd_intake` (`axi4_slave_rd` + `addr_mapper` + snarf probe) pushes
  `(bank, row, col, id)` into `pumice_rd_cmd_cam`, and probes the write CAM for
  read-your-write forwarding.

The salient property: there is exactly **one** stage where AXI-layer concepts
(burst, ID, write strobe) cross into DRAM-layer concepts (rank, bank, row,
column). That stage is `addr_mapper` inside each intake. Upstream everything is
AXI; downstream of the CAMs everything is DRAM.

### Why Two CAMs, Not One

The CAM split is between the write and read paths because the two CAMs hold
**different metadata**, carry **different data**, and have **different
lifetimes**:

| CAM                  | Key         | Data / storage                                                          | Retired on           |
|----------------------|-------------|-------------------------------------------------------------------------|----------------------|
| `pumice_wr_data_cam` | (bank, row) | (col, id, age, slot) + write-data SRAM; fill/commit-drain/snarf movers  | commit-done (B push) |
| `pumice_rd_cmd_cam`  | (bank, row) | (col, id, age, slot) + read-return SRAM; return-fill/drain movers       | last drained R beat  |

A single unified CAM would either carry both data sets (the write CAM needs a
write-data SRAM the read CAM does not) or force an awkward "is_write" predicate
on every scheduler lookup. Keeping them separate lets the read and write paths
size independently.

Both CAMs are **de-FSM'd**: each stores burst data in an SRAM and exposes a
streaming read engine that is FIFO-fed / oldest-pick beat-counter driven -- no
active/slot state latch. The `r_fdone` fill-complete flag gates schedulability
(and, on the write side, snarf).

### Snarf (read-your-write forwarding)

`pumice_rd_intake` probes the write CAM before scheduling a read. On a hit the
read is streamed directly from the write CAM's SRAM via the **snarf mover** in
`pumice_wr_data_cam` -- there is no standalone `wr2rd_forward` block in the live
path. Snarf is limited to unscheduled writes with the same id and same burst
length.

## Scheduler and Command Stream

`pumice_mem_cmd_scheduler` queries both CAMs in the (bank, row) dimension via
`N_LU = NUM_BANKS` parallel lookup ports, picks one command with
`pumice_cmd_arbiter` (the open-page decision is **inline** in the arbiter --
there is no separate `page_predictor` in the issue path), and emits a single
abstract DRAM command `{op, rank, bank, row, col, ap}` into an output command
FIFO. The scheduler is single-issue, PHY/nphases-agnostic, and runs entirely on
`aclk`. Per-bank JEDEC readiness is stamped by `pumice_bank_timers` (wrapping
the FSM-free `bank_timer`); cross-bank turnaround windows
(tFAW/tRRD/tWTR/tRTW/tCCD) come from `global_timers`.

## Clocking Topology

Two external clocks; exactly one CDC.

| Clock     | Domain members                                                          |
|-----------|-------------------------------------------------------------------------|
| `aclk`    | Host AXI, burst splitters, both CAMs, and the whole command scheduler   |
| `dfi_clk` | DFI command path, write serializer, read aligner, DFI 2.1 pin bus       |

The single CDC lives inside `pumice_dfi_layer` (`pumice_dfi_cdc`) and is built
from **async gaxi FIFOs only** -- the command, write-data, and read-data streams
plus the init handshake cross there. No other clock crossing exists in the
controller. If the SoC's AXI master is on a different clock than `aclk`, an
external clock converter is required upstream. See section 1.3 for the reset
topology.

## DFI Phase / Rate Topology

The internal data unit is the **DFI word**: `DW = DRAM_BEAT_WIDTH * DFI_RATE`
(128 by default). One AXI beat == one DFI word == `DFI_RATE` DRAM beats; one AXI
burst (`BL/DFI_RATE` beats) == one DRAM burst (`BL` beats). The DFI command path
in `pumice_dfi_layer` phase-packs the abstract command onto the `DFI_RATE`
phases, placing the command and CS/ODT on `wr_phase` / `rd_phase` as programmed
by the `DFI_PHASE` CSR; `pumice_dfi_wr_serializer` and `pumice_dfi_rd_aligner`
handle the DFI-word to per-phase data split. The scheduler never sees the phase
dimension -- its issue rate is one command per `aclk`.

The old "AXI_DATA_WIDTH == DRAM_BEAT_WIDTH" coupling is gone. Host-width freedom
is a separate concern handled by the optional `pumice_top_geared` wrapper, which
inserts the formally-verified `axi4_dwidth_converter_wr/_rd` between a
host-width AXI slave and the fixed-`DW` core (HOST == DW is a bit-identical
generate bypass). See `docs/AXI_DRAM_GEARING_SCOPE.md`.
