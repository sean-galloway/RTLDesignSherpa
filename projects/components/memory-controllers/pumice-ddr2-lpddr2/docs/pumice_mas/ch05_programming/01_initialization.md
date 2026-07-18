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

> Per HAS §6.2 for the architectural sequence and §2.12 for the FUB-level detail. This chapter is the **software-side cookbook** — what bring-up firmware actually does to get from power-on to "DRAM ready for AXI traffic." The sequence is driven by `rtl/fub/init_sequencer.sv`.

---

## Pre-Reset Setup

Before `aresetn` (the MC-domain reset) deasserts, the SoC's PMU should:

1. Apply DRAM power rails (VDD, VDDQ; LPDDR2 also VDD1/VDD2/VDDCA)
2. Wait for power rails to be stable (typically 10–100 µs per JEDEC)
3. Bring the register transport out of reset (the PeakRDL cpuif is R/W-able; the init sequencer sits in `S_RESET`/`S_DFI_INIT`)
4. Program the family selector and address map: `PHY_TIMING.memtype`, `ADDR_MAP.bank_lsb`/`hash_*` (these must be set before init — see §4.3)
5. Load timing values (`TIMINGS_*`, `INIT_TIMING0/1`, `MR0..MR3`, PASR if LPDDR2)
6. Release the datapath reset

Because config is driven by name into the core (see §4.3), the values are already live at the core boundary when init runs — there is no staging/commit step.

## Init Trigger

```c
void start_dram_init(void) {
    // Family + address map first (must be set before init)
    csr_write(PHY_TIMING, MEMTYPE(DDR2) | T_RDDATA_EN(6) | T_PHY_WRLAT(0) | REFRESH_BURST(1));
    csr_write(ADDR_MAP,   BANK_LSB(COL_WIDTH));   // ROW_MAJOR; add HASH_EN|HASH_SEED if wanted

    // Load timings (example values for DDR2-800)
    csr_write(TIMINGS_RC_RCD_RP_RAS,   TIMING_PACK(60, 15, 15, 40)); // tRC, tRCD, tRP, tRAS
    csr_write(TIMINGS_RFC_REFI,        REFI_PACK(200, 1950));        // tRFC, tREFI
    csr_write(TIMINGS_RRD_FAW_WTR_CCD, RRD_PACK(6, 35, 4, 4));       // tRRD, tFAW, tWTR, tCCD
    csr_write(TIMINGS_CL_CWL_WR,       CL_PACK(6, 4, 15, 70));       // CL, CWL, tWR, tRFCpb
    csr_write(TIMINGS_RTP_RTW,         RTP_PACK(4, 6));              // tRTP, tRTW

    // JEDEC init-sequence waits (or leave RDL defaults 512/256/8/8/16)
    csr_write(INIT_TIMING0, INIT_T0_PACK(512, 256));                 // tINIT, tDLLK
    csr_write(INIT_TIMING1, INIT_T1_PACK(8, 8, 16));                 // tMRD, tRP, tRFC

    // MR values: for DDR2 the sequencer uses its own JEDEC-correct MR words
    // (0x0532/0x0432/0x0380/0x0000); the MR0..MR3 CSRs are the software-visible
    // shadow. For LPDDR2 the sequencer drives the MRW OP values internally.
    csr_write(MR0, mr0_value); csr_write(MR1, mr1_value);
    csr_write(MR2, mr2_value); csr_write(MR3, mr3_value);

    // (LPDDR2) PASR if needed
    csr_write(PASR_BANK_MASK_RANK0, pasr_bank_mask);

    // Optional: ZQ retry count / timeout
    csr_write(INIT_TUNING, INIT_TUNING_PACK(3, 10));  // 3 retries, 10ms timeout

    // Trigger init
    csr_write(CTRL, CTRL_INIT_START);

    // Poll for completion
    while (1) {
        uint32_t s = csr_read(STATUS);
        if (s & STATUS_INIT_DONE)  break;             // DRAM ready
        if (s & STATUS_INIT_ERROR) {                  // STATUS.init_step_dbg shows where
            log_error("DRAM init failed at step %d", STATUS_INIT_STEP_DBG(s));
            return -EIO;
        }
    }
}
```

Note (this build): `STATUS` readback (`hwif_in`) is currently tied off in `pumice_top` (see §4.1); `init_done` is also exposed directly as the top-level `init_done_o` port. Poll whichever is wired on the platform.

## Init Sequence Details

The step-by-step JEDEC sequence is a hardware FSM in `init_sequencer.sv` (`r_state`); software does not interleave commands during init. The sequencer both **issues** the commands to the DRAM (through the scheduler to `dfi_cmd_formatter`) and updates the mode-register shadow so the live CL/CWL/BL decode tracks what was programmed. The `memtype_i` input selects the DDR2 or LPDDR2 chain.

### DDR2 chain (mirrors LiteDRAM's proven Nexys A7 sequence)

1. Assert `dfi_init_start_o`; wait `dfi_init_complete_i` (PHY DLL-lock / IO training), then wait tINIT (`t_init_wait`, CKE settle)
2. **Precharge All** (wait tRP)
3. **EMRS(2)** = 0, **EMRS(3)** = 0, **EMRS(1)** = 0 — JEDEC MRS order EMR2 -> EMR3 -> EMR1, each followed by tMRD
4. **MRS(0) + DLL reset** (0x0532: BL4/CL3/tWR3/DLL_RESET); wait tDLLK (DLL lock)
5. **Precharge All** (wait tRP)
6. **Auto Refresh x2** (each followed by tRFC)
7. **MRS(0)** without DLL-reset (0x0432 — clears the reset bit); wait tMRD
8. **EMRS(1) + OCD Default** (0x0380) -> **EMRS(1) + OCD Exit** (0x0000)
9. `init_done_o = 1`

### LPDDR2 chain (JESD209-2F power-up + MR configuration)

1. Assert `dfi_init_start_o`; wait `dfi_init_complete_i`; tINIT settle
2. **MRW(MR63)** = Reset (wait tINIT4, reuses `t_init_wait`)
3. **MRW(MR10)** = 0xFF ZQ Init Calibration (wait tZQINIT, reuses `t_dll_wait`)
4. **MRW(MR1)** = BL8/nWR3 (0x23), **MRW(MR2)** = RL3/WL1 (0x01), **MRW(MR3)** = DS 40ohm (0x02) — each followed by tMRW (reuses `t_mrd_wait`)
5. `init_done_o = 1`

The MR index (MA, up to MR63) and data (OP) are packed as `{MA[5:0], OP[7:0]}` into the row request field; `dfi_cmd_formatter` unpacks it for the LPDDR2 CA-bus MRW word (a 3-bit bank port cannot reach MR10/MR63). Only MR1/MR2/MR3 update the CL/CWL/BL decode shadow; MR63/MR10 are issued but not shadowed.

The init waits are the `INIT_TIMING0/1` CSR fields (`t_init_wait`, `t_dll_wait`, `t_mrd_wait`, `t_rp_wait`, `t_rfc_wait`); RDL defaults (512/256/8/8/16 MC cycles) comfortably cover the JEDEC minimums at the board frequency. For fast sim, program small values before triggering init.

## Multi-Rank Init Differences

The current `init_sequencer.sv` targets a single rank (the board build is `NUM_RANKS = 1`). For a `NUM_RANKS > 1` build the intended extension is:

- MRS/MRW steps iterate over ranks (one rank per step iteration)
- ZQ calibration is per-rank (each rank has its own reference)
- Each rank's PASR mask is programmed via its own `PASR_*_RANK{N}` register (see §4.2 open items)

Software programs the MR values once; per-rank iteration is absorbed by the sequencer. Per-rank register generation is a follow-up (the RDL declares only `*_RANK0` today).

## ZQ Retry

The `INIT_TUNING.zq_retries` field (default 3) is exposed for the retry count; DDR2 uses OCD calibration during init (no ZQCL) and LPDDR2 uses the MR10 ZQ Init step. Raise the retry budget if signal-integrity issues cause occasional failures.

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
    uint8_t step = STATUS_INIT_STEP_DBG(csr_read(STATUS));
    log_error("Init failed at step %d", step);

    // Inspect step-specific telemetry (per step table)
    // ...

    // Force re-init
    csr_write(CTRL, CTRL_INIT_FORCE_RESTART);

    // Wait a few cycles for FSM to settle
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
