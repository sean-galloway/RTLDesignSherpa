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

# Initialization Sequence

> Per HAS §6.2 for the architectural sequence and §2.12 (`init_engine_fub`) for the FUB-level detail. This chapter is the **software-side cookbook** — what bring-up firmware actually does to get from power-on to "DRAM ready for AXI traffic."

---

## Pre-Reset Setup

Before `mc_rst_n` deasserts, the SoC's PMU should:

1. Apply DRAM power rails (VDD, VDDQ; LPDDR2 also VDD1/VDD2/VDDCA)
2. Wait for power rails to be stable (typically 10–100 µs per JEDEC)
3. Deassert `apb_presetn` (APB slave comes out of reset; CSRs are R/W-able but init_engine is still in IDLE)
4. Load expected timing values into CSRs (TIMINGS_*, MR0..MR3, PASR if LPDDR2 multi-rank)
5. Set `POWER_TUNING` thresholds if auto-APD/SRF behavior is wanted post-init
6. Deassert `mc_rst_n` (controller comes out of reset; sits in POST_RESET; init_engine IDLE)

The pre-loading lets the init engine pick up the values when it runs. If software skips pre-loading, the init engine uses the ROM defaults (which may not match the actual silicon).

## Init Trigger

```c
void start_dram_init(void) {
    // Load timings (example values for DDR2-800)
    apb_write(TIMINGS_RC_RCD_RP, TIMING_PACK(60, 5, 5, 18));   // tRC, tRCD, tRP, tRAS
    apb_write(TIMINGS_RAS_RFC_REFI, REFI_PACK(35, 0xC30));      // tRFC, tREFI
    apb_write(TIMINGS_RRD_FAW_WTR, RRD_PACK(5, 18, 4, 2));      // tRRD, tFAW, tWTR, tCCD
    apb_write(TIMINGS_CL_CWL_WR, CL_PACK(5, 5, 6, 0));          // CL, CWL, tWR, (tRFCpb 0=N/A)

    // Load MR0..MR3 from the board's DRAM datasheet
    apb_write(MR0, mr0_value_for_this_part);
    apb_write(MR1, mr1_value_for_this_part);
    apb_write(MR2, mr2_value_for_this_part);
    apb_write(MR3, mr3_value_for_this_part);

    // (LPDDR2 multi-rank) Per-rank PASR if needed
    for (int r = 0; r < num_ranks; r++) {
        apb_write(PASR_BANK_MASK_RANK0 + r*4, pasr_mask_for_rank[r]);
    }

    // Optional: ZQ retry count
    apb_write(INIT_TUNING, INIT_TUNING_PACK(3, 10));  // 3 retries, 10ms timeout

    // Optional: configure refresh tuning
    apb_write(REFRESH_TUNING, REFRESH_DEFER_ACTIVE(8) | ZQCS_FREQ_HZ(1));

    // Trigger init
    apb_write(CTRL, CTRL_INIT_START);

    // Poll for completion
    while (1) {
        uint32_t s = apb_read(STATUS);
        if (s & STATUS_INIT_DONE) {
            break;       // DRAM ready
        }
        if (s & STATUS_INIT_ERROR) {
            // Diagnostic; STATUS.init_step_dbg shows where it failed
            uint8_t step = STATUS_INIT_STEP_DBG(s);
            log_error("DRAM init failed at step %d", step);
            return -EIO;
        }
    }
}
```

## Init Sequence Details

The actual step-by-step JEDEC sequence is driven by the init engine's microprogram ROM (§2.12). Software does not interleave commands during init — the init engine has exclusive control until `STATUS.init_done` rises. Major phases:

1. **Power-up settling** — `tINIT0` ≈ 200 µs (DDR2) or `tINIT1` ≈ 100 µs (LPDDR2)
2. **CKE wiggle / RESET_N pulse** — sequence per memtype
3. **MR0..MR3 loads** — Per-rank when `NUM_RANKS > 1`
4. **ZQ calibration** — DDR2 uses OCD; LPDDR2 uses MR10 ZQ Init
5. **Initial refresh batches** — Drives DRAM into a stable refresh schedule
6. **Final settling delay** — A few hundred cycles to ensure all per-rank state is consistent
7. **`init_done` assertion** — Controller transitions out of POST_RESET

For sim runs, set `SIM_INIT_SCALE = 10000` at elaboration to compress the multi-hundred-µs delays into a few cycles. Silicon always uses `SIM_INIT_SCALE = 1`.

## Multi-Rank Init Differences

For `NUM_RANKS > 1`:

- MRS_LOAD steps iterate over ranks; the init engine's `rank_iter` counter (§2.12) advances one rank per MC clock during the step
- ZQ calibration is per-rank (each rank has its own ZQ resistor reference; calibration happens N times serially)
- Each rank's PASR mask is loaded individually
- Init time grows by ~NR × per-rank steps; typically minimal compared to the multi-hundred-µs delays

Software is **rank-blind** during init programming — the same code works at NR=1, 2, or 4. The differences are absorbed by the per-rank YAML repeat in the CSR map (per §4.2) and the rank_iter loop in the init engine.

## ZQ Retry

If ZQ calibration times out (per `INIT_TUNING.zq_retries`), the init engine retries `zq_retries` times before raising `INIT_ERROR`. Default is 3 retries; raise it if signal-integrity issues cause occasional failures.

## Post-Init Power-State

After `init_done`, the controller is in ACTIVE for all ranks with CKE high. The refresh manager starts its tREFI counter and begins normal refresh scheduling. The scheduler is unblocked and any AXI bursts that accumulated during init begin issuing.

## Software Wait Times

| Phase                                       | Wait (real silicon, 200 MHz MC clock) |
|---------------------------------------------|---------------------------------------|
| Power-up settling                            | 200 µs                                 |
| MRS loads + per-rank iteration               | ~10 cycles × NR × 4 MRs ≈ 160 cycles  |
| ZQ calibration                               | ~1 µs                                  |
| Initial refresh batches                      | ~10 µs                                 |
| Total init duration                          | ~250 µs (single-rank), ~280 µs (4-rank) |

The init duration scales weakly with rank count — the per-rank serialization is dwarfed by the fixed settling delays.

## Reset Recovery

If init fails (`STATUS.init_error = 1`):

```c
void recover_init_failure(void) {
    uint8_t step = STATUS_INIT_STEP_DBG(apb_read(STATUS));
    log_error("Init failed at step %d", step);

    // Inspect step-specific telemetry (per step table)
    // ...

    // Soft reset and retry
    apb_write(CTRL, CTRL_INIT_FORCE_RESTART);

    // Wait a few cycles for FSM to settle to IDLE
    for (int i = 0; i < 10; i++) asm volatile("nop");

    // Re-init
    start_dram_init();
}
```

A hard fault (e.g., persistent ZQ calibration failure) requires SoC-level intervention — typically a power-cycle and re-bring-up.

## Open Questions / Future Work

- **Init telemetry capture.** When init fails, telemetry beyond `init_step_dbg` would help (DFI signal trace, per-rank fault detection). The current debug surface is sparse; expand if bring-up calls it out.
- **Init via JTAG.** Some platforms init via a JTAG side-band rather than CPU+APB. The CSR map supports this through any APB-attached transport; no controller changes needed.
- **Partial init for warm reset.** Coming out of self-refresh doesn't require full init. The current init engine doesn't have a "warm reset" path. Add when DDR3+ needs it for frequency change.
