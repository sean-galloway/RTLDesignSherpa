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

The controller uses three independent clocks.

### `mc_clk`

Primary controller clock. All scheduler, bank machines, command pipeline, and AXI4-side logic run on `mc_clk`. The DFI master output stage launches its signals on `mc_clk`.

Typical frequency: 100 – 200 MHz on FPGA SoCs; up to 533 MHz on silicon for DDR2-1066 / LPDDR2-800.

### `phy_clk`

PHY-side clock. Runs at `N_PHASES × mc_clk` rate. The PHY consumes DFI signals on `phy_clk`.

For `N_PHASES = 4`, `phy_clk` = 4 × `mc_clk`. For `N_PHASES = 2`, `phy_clk` = 2 × `mc_clk`. For `N_PHASES = 1`, `phy_clk` = `mc_clk` (they may be the same signal in this case).

The relationship is asynchronous from the controller's perspective — the PHY handles the rate conversion. The DFI v2.1 specification's frequency-ratio scheme is what makes this work without explicit FIFO crossings.

### `apb_pclk`

APB CSR bus clock. Independent of `mc_clk` — typically a slower SoC management clock. CDC inside `csr_slave` transfers configuration writes into the `mc_clk` domain via 2-flop synchronizer plus handshake.

## Reset Signals

### `mc_rstn` (active low)

Primary controller reset. Synchronously deasserted on `mc_clk`. Resets:

- AXI4 slave state machines
- Transaction queue
- Scheduler and bank machines
- Cross-bank timers
- Refresh manager (clears tREFI counter and `refresh_pending`)
- Power-state FSM (transitions to RESET state)
- Init engine (resets to step 0)
- All observation counters

### `phy_rstn` (active low)

Controlled by `init_engine` during the reset-release phase of the init sequence. Asserted at startup; deasserted as the first step of the init step table.

### `dfi_rstn` (active low, MC → PHY)

DFI reset signal driven to the PHY. Controlled by `init_engine` per the init step table; allows the PHY to perform its own reset sequence during DRAM init.

### `apb_presetn` (active low)

APB CSR bus reset. Synchronously deasserted on `apb_pclk`. Resets the CSR slave state machine.

## Reset Sequencing

### Cold Boot

1. All resets asserted (`mc_rstn`, `phy_rstn`, `dfi_rstn`, `apb_presetn`)
2. Clocks stable
3. `apb_presetn` deasserted (SoC programs CSR if needed; otherwise defaults)
4. `mc_rstn` deasserted
5. Init engine starts; runs step table; drives `phy_rstn` and `dfi_rstn` per the sequence
6. On `init_done`, power-state FSM transitions to ACTIVE
7. Controller services AXI traffic

### Warm Reset (Clock-Gated)

The SoC can warm-reset the controller without losing DRAM content:

1. SoC requests self-refresh entry via CSR
2. Controller acknowledges; DRAM is in self-refresh
3. SoC asserts `mc_rstn`; clocks may be gated
4. SoC deasserts `mc_rstn`; clocks resume
5. Controller re-runs init from the table (the table is idempotent — it does not corrupt DRAM in self-refresh)
6. Controller resumes normal operation

The init step table is designed to be cold-boot-correct **and** warm-boot-safe. The step list for LPDDR2 includes a check on MR4 for the current temperature; if the temperature changed during the warm reset, the controller updates its tREFI scale accordingly.

## Clock Domain Crossing Summary

| Crossing                | Mechanism                                    | Latency                       |
|-------------------------|----------------------------------------------|-------------------------------|
| `apb_pclk` → `mc_clk`   | 2-flop sync + handshake                      | ~3-4 `mc_clk` cycles          |
| `mc_clk` → `apb_pclk`   | 2-flop sync (observation reads)              | ~3-4 `apb_pclk` cycles        |
| `mc_clk` → `phy_clk`    | DFI frequency-ratio scheme (no explicit CDC) | 0 (combinational replication) |

## Reset and Power Considerations

Note that DFI v2.1 §4.1 requires `dfi_init_start` to be asserted by the controller as part of init; the controller does this during the reset-release step. The PHY's `dfi_init_complete` signal indicates that the PHY has finished its own initialization; the controller's init engine waits on this before proceeding to MRS loads.
