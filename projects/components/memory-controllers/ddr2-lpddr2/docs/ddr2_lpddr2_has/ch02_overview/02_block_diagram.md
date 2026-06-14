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

# Block Diagram

## Top-Level Block Diagram

The controller's top-level data and control flow is shown below. AXI4 traffic enters at top-left, flows through the address mapper and transaction queue into the scheduler, gets converted to per-bank commands and routed through the encoder and gear stage out to the DFI PHY interface. The APB CSR slave (bottom) provides configuration and observation in parallel.

![Top-Level Block Diagram](../assets/mermaid/01_block_diagram.png)

**Source:** [01_block_diagram.mmd](../assets/mermaid/01_block_diagram.mmd)

## Data Flow Summary

**Write path:**
1. AXI master issues an AW transaction; AXI4 slave accepts and queues.
2. The address mapper translates the flat AXI address into (bank, row, column) coordinates.
3. The transaction queue caches the request with row-hit metadata determined from the bank machines' current state.
4. The scheduler picks the next eligible transaction; consults the page predictor if enabled.
5. The scheduler issues ACT, then WR (or WRA) through the command encoder.
6. The gear output stage replicates the 1-phase command onto N parallel DFI phases.
7. CWL cycles after the WR command, the write data path pulls W-channel beats and drives them onto DFI wrdata.
8. A B-response is generated to the AXI master after the WR is scheduled (posted-write semantics).

**Read path:**
1. AXI master issues an AR transaction; AXI4 slave accepts and queues.
2. Address mapping and queue caching identical to write path.
3. The scheduler issues ACT, then RD (or RDA) through the command encoder.
4. CL cycles after the RD command, the read data path samples DFI rddata for the burst duration.
5. Read beats are tagged with the original AXI ID and streamed back on the R channel.

**Refresh path:**
1. The refresh manager's tREFI counter elapses, incrementing `refresh_pending`.
2. When `refresh_pending` exceeds the soft threshold, a refresh request enters the scheduler queue.
3. For DDR2 or LPDDR2 REFab: scheduler waits for all banks to be idle, then issues REF; all bank machines enter REFRESHING state.
4. For LPDDR2 REFpb under DARP: scheduler picks the idle bank with the oldest last-refresh timestamp; issues REFpb to that bank only; other banks remain available for column commands.

**Init / power path:**
1. On cold reset, the power-state FSM transitions to INIT and starts the init engine.
2. The init engine executes the memtype-specific step table, driving CKE/ODT/RESET_N and issuing MRS commands via the command encoder.
3. On completion (`init_done`), the FSM transitions to ACTIVE and the scheduler begins servicing AXI traffic.
4. Power-down / self-refresh entry is requested by the SoC via CSR and orchestrated by the FSM.

Detailed per-module behavior follows in Chapter 3.
