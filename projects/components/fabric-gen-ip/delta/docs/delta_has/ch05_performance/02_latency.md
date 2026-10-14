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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Latency Analysis

## Cycle Breakdown

The generated flat crossbar has a fixed two-cycle latency from master input to slave output:

| Cycle | Action |
|-------|--------|
| 0 | Master asserts `s_axis_tvalid` and `s_axis_tdest`. |
| 1 | TDEST decode produces `request_matrix`; arbiter registers the grant. |
| 2 | Crossbar mux drives `m_axis_tdata`, `m_axis_tvalid`, etc. to the slave. |

: Latency Cycle Breakdown

## Arbitration Delay

If the target slave is idle when the request arrives, the grant is registered on the next rising edge of `aclk`. If the slave is busy serving another packet, the new request waits until the current packet's `TLAST` is accepted.

## Backpressure Latency

`m_axis_tready[s]` propagates combinationally through the TREADY steering logic to `s_axis_tready[m]`. There is no additional registered delay on the backpressure path.

## Latency Targets

| Configuration | Latency | Notes |
|---------------|---------|-------|
| Flat crossbar, idle slave | 2 cycles | Arbitration + registered grant. |
| Flat crossbar, contended slave | 2 + wait cycles | Wait depends on current packet length. |

: Latency Targets

## Frequency Target

The flat crossbar is intended to run at **≥ 300 MHz** on Xilinx UltraScale+ devices for typical configurations (e.g., 4×16 @ 64-bit). Actual Fmax depends on device, tool settings, and floorplanning.
