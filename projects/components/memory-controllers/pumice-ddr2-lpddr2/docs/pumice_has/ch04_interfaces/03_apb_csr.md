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

# CSR Register Interface (PeakRDL cpuif)

Configuration and observation registers are exposed through a
**PeakRDL-generated register block** (`pumice_csr`), not a hand-written APB
slave. The register map is authored in `rtl/macro/pumice_csr.rdl` and generated
with the passthrough cpuif (`bin/peakrdl_generate.py`); `pumice_top`
instantiates the generated `pumice_csr` and drives the core by name from
`hwif_out.*` (see §6.3 for the full map). The DV mirror used for by-name access
is `dv/tbclasses/pumice_regmap.py`.

The SoC-facing bus is therefore the PeakRDL **passthrough cpuif**, a simple
request/ack register interface. An SoC that natively speaks APB / AXI-Lite
places a thin protocol adapter in front of this cpuif; the controller itself
does not embed one in this generation.

## cpuif Signals

`CSR_ADDR_W = 12` (4 KB, 32-bit registers). The block runs on `aclk` / `~aresetn`
(the controller clock/reset — see below).

| Signal                   | Width | Direction | Notes                                        |
|--------------------------|-------|-----------|----------------------------------------------|
| `s_cpuif_req`            | 1     | input     | Request valid                                |
| `s_cpuif_req_is_wr`      | 1     | input     | 1 = write, 0 = read                          |
| `s_cpuif_addr`           | 12    | input     | Register byte address (4 KB space)           |
| `s_cpuif_wr_data`        | 32    | input     | Write data                                   |
| `s_cpuif_wr_biten`       | 32    | input     | Per-bit write enable                         |
| `s_cpuif_req_stall_wr`   | 1     | output    | Back-pressure a write request                |
| `s_cpuif_req_stall_rd`   | 1     | output    | Back-pressure a read request                 |
| `s_cpuif_rd_ack`         | 1     | output    | Read data valid                              |
| `s_cpuif_rd_err`         | 1     | output    | Read error (e.g. unmapped address)           |
| `s_cpuif_rd_data`        | 32    | output    | Read data                                    |
| `s_cpuif_wr_ack`         | 1     | output    | Write accepted                               |
| `s_cpuif_wr_err`         | 1     | output    | Write error                                  |

## Access Semantics

Standard PeakRDL passthrough behavior:

- Single-cycle accepts for the typical case; the `*_stall_*` outputs allow the
  block to hold a request when needed.
- `s_cpuif_rd_err` / `s_cpuif_wr_err` are raised for unmapped addresses; the
  error terminates the access and does not disturb controller state.
- Read-only fields ignore writes; write-only / self-modifying fields (e.g.
  `CTRL.init_start`, `CTRL.soft_reset`) pulse `swmod`.

## Clock Domain

The register block is clocked by `aclk` (the controller / host-AXI clock) and
reset by `~aresetn`. It is **not** on a separate management clock in this
generation — there is no independent `apb_pclk`. Config fields (`hwif_out.*`,
`hw = r`) are read combinationally by `pumice_top` and fanned out to the core;
the single clock-domain crossing to the PHY side (`dfi_clk`) lives inside
`pumice_dfi_layer` (async gaxi FIFOs), not in the register block. Observation
fields (`hwif_in.*`, `hw = w`) are written from the core clock domain.

## Register Map

The full address map is documented in §6.3, reconciled against
`rtl/macro/pumice_csr.rdl` and `dv/tbclasses/pumice_regmap.py`.

## Configuration Sequencing

Recommended bring-up order (see §6.1 for reset details):

1. Hold `aresetn` asserted.
2. Program timing parameters (`TIMINGS_*`), MR overrides, and `PHY_TIMING`
   (including `memtype` and `t_phy_wrlat` / `t_rddata_en`).
3. Program `ADDR_MAP` (`bank_lsb` / `hash_en` / `hash_seed`) and `DFI_PHASE`.
4. Configure PASR mask (LPDDR2 only).
5. Release `aresetn`.
6. Wait for `STATUS.init_done`.
7. Begin AXI traffic.

Runtime tuning writes (scheduler / refresh / page policy) take effect at the
next configuration quiet point; the SoC owns the drain — see §5.4.
