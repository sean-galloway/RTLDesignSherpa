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

The controller uses two independent clocks. The register block is a PeakRDL
passthrough `cpuif` clocked by `aclk` — there is no separate management clock.

### `aclk`

Controller clock. All host-AXI4 logic, the scheduler, the bank timers, the
write/read CAMs, and the register block (`pumice_csr`) run on `aclk`. The
controller-side of the command / write-data / read-data streams into the DFI
layer is on `aclk`.

Typical frequency: 100 – 200 MHz on FPGA SoCs; higher on silicon.

### `dfi_clk`

PHY / DFI-side clock. The DFI 2.1 command bus, write serializer, and read
aligner run on `dfi_clk`; the PHY consumes and drives the DFI pin bus on this
clock. The gear ratio (`DFI_RATE`) sets how many DRAM phases each `dfi_clk`
cycle carries.

`aclk` and `dfi_clk` are asynchronous to each other. The single crossing
between them lives inside `pumice_dfi_layer` (see the CDC summary below).

## Reset Signals

Both resets are active-low.

### `aresetn` (active low, controller / AXI domain)

Controller reset, tied to the `aclk` domain. The register block resets on
`~aresetn` (`pumice_csr` `.rst(~aresetn)`). Resets:

- Host AXI4 interface state (`pumice_axi4_ifc`)
- Write-data and read-command CAMs
- Command scheduler and bank timers (`pumice_mem_cmd_scheduler`)
- Refresh manager and init sequencer
- Register block (`pumice_csr`) and observation state

### `dfi_rstn` (active low, DFI / PHY domain)

DFI-domain reset, tied to the `dfi_clk` domain. Resets the DFI command path,
the write serializer, the read aligner, and the DFI-side of the CDC FIFOs
inside `pumice_dfi_layer`.

> Note: `init_sequencer` names its ports `mc_clk` / `mc_rst_n` internally, but
> the top level (`pumice_top` → `pumice_core`) ties these to `aclk` / `aresetn`.

## Reset Sequencing

### Cold Boot

1. Both resets asserted (`aresetn`, `dfi_rstn`)
2. Clocks stable
3. `dfi_rstn` deasserted; `aresetn` deasserted (software programs the CSR
   timings/phases/policy via the register `cpuif`, or defaults are used)
4. The init sequencer asserts `dfi_init_start_o` and waits on
   `dfi_init_complete_i` (the PHY runs its own DLL-lock / IO training)
5. The init sequencer walks the JEDEC MRS / precharge / refresh sequence
   (see the Init Sequences chapter)
6. On `init_done_o`, the controller begins servicing AXI traffic

### Warm Reset (Clock-Gated)

The SoC can warm-reset the controller without losing DRAM content:

1. SoC requests self-refresh entry (via `powerdown_ctrl`, optional)
2. Controller acknowledges; DRAM is in self-refresh
3. SoC asserts `aresetn`; clocks may be gated
4. SoC deasserts `aresetn`; clocks resume
5. Controller re-runs the init sequence
6. Controller resumes normal operation

## Clock Domain Crossing Summary

There is exactly one clock-domain crossing in the design: the `aclk` ↔
`dfi_clk` crossing inside `pumice_dfi_layer` (`pumice_dfi_cdc.sv`). It is built
from asynchronous `gaxi` FIFOs only — command, write-data, and read-data each
get their own async FIFO, plus the `init_start` / `init_complete` handshake.
The register `cpuif` shares the `aclk` domain, so there is no CSR-clock CDC.

| Crossing              | Mechanism                                          | Latency                     |
|-----------------------|----------------------------------------------------|-----------------------------|
| `aclk` → `dfi_clk`    | Async `gaxi` FIFOs (cmd / wrdata) in `pumice_dfi_cdc` | FIFO + `N_FLOP_CROSS`-flop sync |
| `dfi_clk` → `aclk`    | Async `gaxi` FIFO (rddata) in `pumice_dfi_cdc`     | FIFO + `N_FLOP_CROSS`-flop sync |

## Reset and Power Considerations

DFI v2.1 requires `dfi_init_start` to be asserted by the controller as part of
init; the init sequencer drives `dfi_init_start_o` out of reset (once it leaves
`S_RESET`) and waits on the PHY's `dfi_init_complete_i` before proceeding to
the MRS / precharge / refresh walk. The `init_start` / `init_complete` handshake
crosses the `aclk` ↔ `dfi_clk` boundary through the same CDC as the command and
data streams.
