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

# Error Handling

> The controller's error-reporting paths and the recommended software response model. Register accesses are the PeakRDL cpuif (`csr_write`/`csr_read`); config fields drive the core live with no apply/commit step (see §4.3).

---

## Error Categories

| Category                       | Detection                                | Reporting                                          |
|--------------------------------|------------------------------------------|----------------------------------------------------|
| Init failure                   | `init_sequencer` timeout / ZQ retries exhausted | `STATUS.init_error = 1`; `STATUS.init_step_dbg` shows where |
| DFI rddata-valid timeout       | RD issued, no rddata in the expected window | `SLVERR` on the AXI R (bring-up: check DFI phase / `t_rddata_en`) |
| AXI burst boundary violation   | Per §3.1 (one AXI burst == one DRAM burst) | `SLVERR` on B/R                                   |
| ZQ calibration failure (silicon) | DFI signal-integrity, caught at PHY layer | Not this controller                              |
| Multi-bit DRAM error           | Out of scope (no inline ECC)              | Would need ECC sideband                            |

Note: `STATUS` is currently a declared RO register whose `hwif_in` is tied off in `pumice_top` (see §4.1). `init_done` is exposed directly as the top-level `init_done_o` port. There is no dedicated IRQ port list wired in this build; software polls `STATUS`/`init_done_o`. A queue-overflow / refresh-miss IRQ is a possible follow-up.

## Software Response Patterns

### Init Failure

```c
void handle_init_error(void) {
    uint32_t s = csr_read(STATUS);
    uint8_t step = STATUS_INIT_STEP_DBG(s);

    log_error("DRAM init failed at step %d", step);

    // init_sequencer step encodings (r_state), for reference:
    //   S_DFI_INIT  -> PHY init did not complete (check PHY config)
    //   S_EMR*/S_MR0* / S_L_* -> MRS/MRW issue phase (verify MR values, CA-bus)
    //   S_REF1/S_REF2 -> refresh phase
    // Force re-init (config CSRs are preserved)
    csr_write(CTRL, CTRL_INIT_FORCE_RESTART);
}
```

### DFI Read-Data Timeout (board bring-up)

A read that returns no data almost always means the DFI read window is misaligned for the attached PHY. The knobs are `DFI_PHASE.rd_phase`, `PHY_TIMING.t_rddata_en`, and `PHY_TIMING.t_phy_wrlat`:

```c
// Nexys A7 a7ddrphy known-good: rd_phase=0, t_rddata_en=6, t_phy_wrlat=0
csr_write(DFI_PHASE,   RD_PHASE(0) | WR_PHASE(0));
csr_write(PHY_TIMING,  MEMTYPE(DDR2) | T_RDDATA_EN(6) | T_PHY_WRLAT(0) | REFRESH_BURST(1));
```

Set these during bring-up before triggering init; they take effect immediately (config-drive, no commit step).

### Refresh Pressure

Watch `OBS_REFRESH_PENDING_MAX` (0x108). If it approaches the deferral budget, reduce batching:

```c
uint32_t v = csr_read(REFRESH_TUNING);
v = (v & ~REFRESH_DEFER_ACTIVE_MASK) | REFRESH_DEFER_ACTIVE(1);  // no batching
csr_write(REFRESH_TUNING, v);   // live on the next refresh event boundary
```

## STATUS_HISTORY for Bring-Up

The `STATUS_HISTORY` register (0x008) captures the last 8 power-state transitions (4 bits each, most recent in [3:0]). Useful when the controller oscillates between power states:

```c
void dump_state_history(void) {
    uint32_t hist = csr_read(STATUS_HISTORY);
    for (int i = 0; i < 8; i++)
        log_info("State[-%d]: %s", i, power_state_name((hist >> (i*4)) & 0xF));
}
```

(As with `STATUS`, this readback depends on `hwif_in` being wired — a follow-up per §4.1.)

## Diagnostic Sequence for Suspected Bug

```
1. Read STATUS.init_done (or the init_done_o port) — must be 1
2. Read STATUS.power_state — should be ACTIVE
3. Read STATUS_HISTORY — look for oscillation
4. Read OBS_TXN_QUEUE_DEPTH_MAX / OBS_REFRESH_PENDING_MAX — check for backlog
5. Read OBS_AXI_R_LATENCY_P99 — tail latency telemetry
6. Read OBS_ROW_HIT[bank] — per-bank traffic distribution
7. Read OBS_REF_LATENCY[bank] — per-bank refresh fairness
```

This is the bring-up team's first-pass diagnostic flow.

## Soft Reset vs. Re-Init

`CTRL.soft_reset` (bit 31, self-clearing) requests an internal soft reset that re-clears datapath state without disturbing the CSR contents. Use it when the controller is in an inconsistent state but the software's config is correct:

```c
void soft_reset(void) {
    csr_write(CTRL, CTRL_SOFT_RESET);
    for (int i = 0; i < 16; i++) asm volatile("nop");  // self-clearing
    csr_write(CTRL, CTRL_INIT_START);                  // CSRs preserved
}
```

For hard cases (silicon bug, persistent failure), the SoC PMU drives the asynchronous reset and software re-brings-up from scratch.

## Open Questions / Future Work

- **IRQ port.** This build polls `STATUS`/`init_done_o`. A latched error/IRQ output (init error, refresh miss, rddata timeout) is a candidate feature.
- **Observation readback wiring.** The `STATUS`/`OBS_*` diagnostics assume `hwif_in` is connected; it is tied off today (§4.1).
- **Per-rank error reporting.** When multi-rank lands, localizing a fault to a rank would help board bring-up.
