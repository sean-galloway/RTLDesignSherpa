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

# Resources

## Estimates from the Performance Model

The `bin/delta_performance_model.py` script provides empirical resource estimates based on the flat topology. Values below are planning estimates, not synthesis results.

| Configuration | LUTs | FFs | Notes |
|---------------|------|-----|-------|
| 4×16 @ 64-bit | ~1,536 | ~1,536 | Base flavor, with counters. |
| 2×4 @ 32-bit | ~200 | ~150 | Small test configuration. |
| 4×16 @ 64-bit, no counters | ~1,400 | ~1,200 | `--no-counters` saves FF area. |

: Table 5.4: Resource Estimates

## Scaling Laws

- **LUTs:** Grow roughly as `NUM_MASTERS × NUM_SLAVES` for arbitration plus `NUM_SLAVES × DATA_WIDTH` for the data mux.
- **FFs:** Grow roughly as `NUM_MASTERS × NUM_SLAVES` for the grant matrix and `last_grant` storage, plus `NUM_MASTERS + NUM_SLAVES` for packet counters when enabled.
- **BRAM:** None. Delta is a pure-logic implementation.

## Area Optimization Knobs

| Knob | Effect |
|------|--------|
| `--no-counters` | Removes `pkt_count_master` and `pkt_count_slave` arrays. |
| Smaller `NUM_MASTERS`/`NUM_SLAVES` | Linear reduction in control logic. |
| Smaller `DATA_WIDTH` | Linear reduction in data mux area. |
| Disable richness options | Removes `TSTRB` muxing, and with `--amba5` off removes the `TWAKEUP` decode, the check-signal mux and the per-port `dataint_parity` checkers. |

: Table 5.5: Area Optimization Options
