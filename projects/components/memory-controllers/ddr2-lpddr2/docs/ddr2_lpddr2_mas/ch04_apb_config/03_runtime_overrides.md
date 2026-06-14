<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Runtime Overrides and Quiet Points

**Status:** Skeleton — to be authored during MAS week


This section documents the runtime override mechanism — how a CSR write becomes a live datapath change without rebuilding or resetting.

## Override Categories

Three flavors of override exist:

1. **Synthesized-MAX, runtime-active** — the silicon includes the maximum-capability logic; runtime CSR selects how much of it is active. Examples: `SCHED_TUNING.lookahead_active`, `REFRESH_TUNING.refresh_defer_active`.
2. **Synthesized-set, runtime-mux** — the silicon includes a discrete set of variants; runtime CSR picks one. Examples: `ADDR_MAP_TUNING.scheme_or`, `REFRESH_TUNING.refpb_policy_or`.
3. **Pure runtime** — no silicon-area cost beyond the register itself. Examples: `REFRESH_TUNING.zqcs_freq_hz`, `INIT_TUNING.zq_retries`.

## Quiet-Point Sequence

1. Software writes the staging field via APB.
2. Software writes `CTRL.config_apply = 1`.
3. Controller drives `txn_queue` to drain, blocks new AXI accepts, completes any in-flight refresh.
4. `power_state_fub` asserts `quiet_point` for one cycle.
5. `csr_apb_fub` copies staging → live for every R/W field.
6. `STATUS.config_settled` rises.
7. Software reads `STATUS.config_settled`, clears `CTRL.config_apply`, and resumes traffic.

The drain phase is bounded — typically < 256 MC cycles for a healthy queue — and is the only operational disruption from a runtime override.

## TODO

- Worst-case drain latency analysis
- Override propagation timing for each category
- Multi-write coalescing (if multiple staging writes are queued, commit them all at one quiet point)
- Software examples (init-time vs. runtime override patterns)

