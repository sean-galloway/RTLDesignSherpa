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

# Clocks and Reset

## Clock Domains

The controller has exactly two clock domains. Everything from the host AXI face
through the command scheduler runs on `aclk`; the DFI datapath and PHY pin bus
run on `dfi_clk`. The register block `pumice_csr` runs on `aclk` (there is no
separate APB CSR clock).

| Clock       | Polarity | Domain members                                                                 |
|-------------|----------|--------------------------------------------------------------------------------|
| `aclk`      | Posedge  | `pumice_csr`, `pumice_axi4_ifc` (AXI slave, burst splitters, both CAMs), `pumice_mem_cmd_scheduler` (arbiter, bank/global timers, refresh, init, mode register) |
| `dfi_clk`   | Posedge  | `pumice_dfi_layer` command path, write serializer, read aligner; the DFI 2.1 pin bus |

`aclk` and `dfi_clk` are independent. The DFI-word datapath unit means one FIFO
word equals one `dfi_clk` cycle, so the crossing is bubble-free at rate.

## Reset Topology

| Reset       | Polarity   | Type                         | Domain    |
|-------------|------------|------------------------------|-----------|
| `aresetn`   | Active-low | Async assert                 | `aclk`    |
| `dfi_rstn`  | Active-low | Async assert                 | `dfi_clk` |

Each domain has its own reset. `pumice_csr` takes `rst = ~aresetn` (the PeakRDL
block uses active-high internally). All flops use the repo reset macros
(`reset_defs.svh`); SRAMs inside the CAMs have no reset port. The SoC's PMU is
expected to drive clean, de-glitched resets -- there is no reset-glitch filter
in the controller.

## CDC

There is exactly **one** clock-domain crossing in the whole controller, and it
lives in `pumice_dfi_cdc` inside `pumice_dfi_layer`. It is built from **async
gaxi FIFOs only** (`N_FLOP_CROSS` = 2 by default). Four things cross it:

| Stream               | Direction            | Payload                                  |
|----------------------|----------------------|------------------------------------------|
| Command              | `aclk` -> `dfi_clk`  | `{op, rank, bank, row, col, ap}` (`CMD_DW`) |
| Write data           | `aclk` -> `dfi_clk`  | `{last, strb, data}` DFI-word (`WD_DW`)   |
| Read data            | `dfi_clk` -> `aclk`  | `{last, resp, data}` DFI-word (`RD_DW`)   |
| Init handshake       | both                 | `init_start` out, `init_complete` back    |

There is **no** APB-to-MC CSR crossing, no quiet-point override-staging
crossing, and no CDC in the AXI4 datapath -- `pumice_axi4_ifc` runs entirely on
`aclk`. If the SoC's AXI master is on a different clock, an external clock
converter is required upstream. The register block also runs on `aclk`, so CSR
writes take effect combinationally through `hwif_out.*` into the config ports of
`pumice_core` (no staging register). Timing/phase/policy fields should be
programmed while the controller is idle (before `init_start`, or at a quiet
point) since they feed the timers and phase-packers directly.

## Reset / Init Sequence

On power-on:

1. `aresetn` and `dfi_rstn` are asserted (both low). The PHY drives
   `dfi_init_complete_i = 0`.
2. The SoC deasserts both resets. `pumice_csr` becomes R/W-able on `aclk`;
   software programs the timing, DFI-phase, page-policy, and address-map fields
   by name (never by hardcoded offset -- see `dv/tbclasses/pumice_regmap.py`).
   The controller idles with `init_done_o = 0`; AXI traffic is held off.
3. The `init_sequencer` (inside `pumice_mem_cmd_scheduler`) drives
   `dfi_init_start_o` and walks the per-memtype JEDEC MRS init sequence,
   emitting init commands into the same arbiter path as normal traffic and
   waiting on the programmed init timings (`t_init_wait`, `t_dll_wait`,
   `t_mrd_wait`, `t_rp_wait`, `t_rfc_wait`) plus `dfi_init_complete_i` from the
   PHY. The `mode_register` shadow captures the MRS writes and exposes
   CL/CWL/BL to the DFI layer.
4. On completion the sequencer asserts `init_done_o`; the controller begins
   honoring host AXI traffic and the refresh controller is enabled.

Because the CSR block and the scheduler share `aclk`, no inter-clock handshake
gates step 2; software only needs both resets released and the register bus
alive.
