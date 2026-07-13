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

# AXI4 Slave Protocol

> This chapter is the **wire-level contract** of the controller's host AXI4
> slave face -- what's supported, what's relaxed, what's omitted, and the
> timing / ordering / backpressure semantics the integrator can rely on.
>
> The interface is implemented by `pumice_axi4_ifc` (section 2.1): a pair of
> AMBA burst splitters feed the dumb `pumice_wr_intake` / `pumice_rd_intake`
> blocks (each wrapping `axi4_slave_wr` / `axi4_slave_rd`), which push into the
> write / read CAMs.

---

## Compliance Profile

| Aspect                          | Support level                                              |
|---------------------------------|------------------------------------------------------------|
| AXI4 (ARM IHI 0022) signal set  | Full AW/W/B/AR/R                                            |
| AXI4-Lite                       | Not supported (use the register cpuif for control)         |
| AXI4-Stream                     | Not applicable                                              |
| AXI5                            | Not supported                                              |

## Data Width

The core's AXI data width is the **DFI word**: `DW = DRAM_BEAT_WIDTH * DFI_RATE`
(128 by default). One AXI beat == one DFI word == `DFI_RATE` DRAM beats. If the
SoC master runs a different width, wrap the core in `pumice_top_geared`, which
inserts the formally-verified `axi4_dwidth_converter_wr/_rd` between a
host-width AXI slave and the fixed-`DW` core (`HOST_AXI_DATA_WIDTH == DW` is a
bit-identical generate bypass). See `docs/AXI_DRAM_GEARING_SCOPE.md`.

## Burst Splitting

Each host burst is split at DRAM-burst-byte boundaries by
`axi_master_wr_splitter` / `axi_master_rd_splitter`
(`ALIGN_MASK = BL*(DRAM_BEAT_WIDTH/8) - 1`), so every command handed to an
intake is exactly one DRAM burst. This is how an arbitrary AXI `awlen`/`arlen`
maps onto the fixed DRAM burst length.

## Supported Features

- INCR burst type (mandatory)
- Arbitrary INCR burst length (split into DRAM-burst commands as above)
- ID-carried requests; per-ID in-order completion (AXI4 mandate)
- Cross-ID reordering at the DRAM layer, with AXI response ordering honored at
  the response side (per HAS 3.1)
- `awqos`/`arqos`/`awregion`/`arregion` carried through the splitters (observed,
  not yet used for scheduler priority)
- Single-bit `awuser`/`aruser`/`wuser` ports carried through the front-end
  (echoed on B/R `buser`/`ruser`)

## Unsupported / Ignored

- AXI4 exclusive accesses (`awlock`, `arlock` observed but ignored; treated as
  normal accesses)
- AXI4 cache-coherent behavior (`awcache`/`arcache` observed, no behavior)
- FIXED / WRAP burst types are not a design target; the front-end is built for
  INCR traffic

## Backpressure Semantics

The slave asserts backpressure via the standard AXI handshake. Backpressure
originates in the intake FIFOs and CAM fill:

| Channel | Backpressure reason                                                            |
|---------|--------------------------------------------------------------------------------|
| AW      | AW-meta FIFO full in `pumice_wr_intake`, or `pumice_wr_data_cam` has no free slot |
| W       | Write-data FIFO / write-data SRAM full in the write path                        |
| AR      | `pumice_rd_cmd_cam` has no free slot                                            |
| B       | Standard `bready` handshake                                                     |
| R       | Standard `rready` handshake; the drain mover in `pumice_rd_cmd_cam` stalls until `rready` |

Total in-flight depth per direction is set by `NUM_ENTRIES` (CAM depth) with
`N_SRAM_SLOTS` burst-data SRAM slots per CAM.

## Response Ordering

1. **Per-ID in-order** -- always enforced. Two accesses with the same ID
   complete in issue order.
2. **Cross-ID** -- reordering is allowed at the DRAM layer (the scheduler picks
   by bank/row/age), but the CAMs drain and the intakes emit responses so that
   the AXI-visible ordering rules hold.

## Read-Your-Write Forwarding (snarf)

`pumice_rd_intake` probes `pumice_wr_data_cam` before a read is scheduled. On a
hit against an unscheduled write with the same id and same burst length, the
read is streamed straight from the write CAM's SRAM (the **snarf mover**) with
no DRAM round-trip. On a miss the read goes through the normal DRAM path.

## Timing Contract

| Path                                       | Behavior                                          |
|--------------------------------------------|---------------------------------------------------|
| `awvalid` -> `awready`                      | <= 1 cycle when the AW-meta FIFO has space         |
| `awready` accept -> CAM push                | 1 cycle                                            |
| CAM push -> DRAM issue                      | scheduler / refresh dependent (typically 0 to ~256 cycles) |
| Last W beat -> B response                   | commit + write-recovery window + scheduler backlog  |
| `arvalid` -> first R beat                   | DRAM access latency (typically 30-100 ns) + bus rounding, or ~0 on a snarf hit |
| Successive R beats (same burst)            | 1 per `aclk` cycle (sustained streaming)           |

The slave does not embed an AXI register slice. If a target needs one for
closure, add an external `axi_register_slice` from the AMBA library, or use
`pumice_top_geared` (whose dwidth converters register the boundary).

## Error Responses

| Condition                                              | Response       | Notes                               |
|--------------------------------------------------------|----------------|-------------------------------------|
| Traffic before `init_done_o`                           | held / SLVERR  | Poll `STATUS.init_done` (or the `init_done_o` pin) before issuing traffic |
| DFI read return flagged bad by the aligner             | `SLVERR`       | Propagated on the affected R beats  |

DECERR is never returned -- the address space is monolithic.

## Open Questions / Future Work

- **QoS-driven priority.** `awqos`/`arqos` are carried but not yet consumed by
  `pumice_cmd_arbiter`. A future revision would fold them into the pick.
- **Wider USER signals.** The front-end carries single-bit user today; wider
  sideband would need a `USER_WIDTH` parameter threaded through the intakes and
  CAMs.
- **AXI register-slice option.** Currently external / via the geared wrapper; a
  build-time embed could be added for very-high-frequency targets.
