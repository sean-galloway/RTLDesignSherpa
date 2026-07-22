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

# Refresh Controller

`refresh_ctrl` (`rtl/fub/refresh_ctrl.sv`) owns tREFI timing and refresh request accounting. It does not issue commands itself — it raises a request to the command arbiter, which serializes the precharge-then-REF sequence and pulses a grant once `REF` reaches the DFI bus.

## `refresh_ctrl`

### Purpose

Track the interval between mandatory refreshes and tell the scheduler when refresh is owed. JEDEC permits up to 8 postponed refreshes; `refresh_ctrl` uses an 8-deep accumulator plus a drain-quota mechanism so a batch of owed refreshes can be granted back-to-back.

### Interface

| Signal                    | Direction | Purpose                                              |
|---------------------------|-----------|------------------------------------------------------|
| `t_refi_i[15:0]`          | input     | Refresh interval in MC cycles (CSR-backed)           |
| `refresh_burst_i[3:0]`    | input     | 1..8 REFs to drain per request cycle (CSR-backed)    |
| `refpb_mode_i`            | input     | 0 = REFab, 1 = REFpb (LPDDR2) bank-rotor select      |
| `enable_i`                | input     | Gates tREFI counting; driven by `init_done`          |
| `refresh_req_o`           | output    | High while pending refreshes remain                  |
| `refresh_grant_i`         | input     | Pulsed by the arbiter when REF issues on the bus     |
| `refresh_drain_active_o`  | output    | High during a back-to-back drain burst               |
| `refresh_kind_o`          | output    | Registered REFab/REFpb selector                      |
| `refresh_bank_o`          | output    | Bank rotor value (valid in REFpb mode)               |
| `pending_refreshes_o`     | output    | Current accumulator value                            |
| `obs_*`                   | output    | Internal state harvested for CSR readout             |

### tREFI Counter and Pending Accumulator

`r_refi_cnt` counts down from `t_refi_i`. It only ticks while `enable_i` is high (i.e. after init completes); before that it is held reloaded at `t_refi_i`. On expiry it reloads and the pending accumulator `r_pending` increments by 1 (saturating at the JEDEC maximum of 8). Each accepted grant decrements `r_pending`. A simultaneous expiry and grant is a net-zero change. `refresh_req_o` stays high whenever `r_pending > 0`.

Saturating at 8 is JEDEC-conformant: the controller is expected to keep at most 8 postponed refreshes outstanding before it must catch up. If the system stays bandwidth-starved past 8 x tREFI, the counter saturates (a DRAM retention violation looming) rather than growing unbounded.

### Drain Quota

`r_burst_remaining` implements back-to-back draining. When the previous burst is fully drained and pending work exists, it (re)loads `min(refresh_burst_i, r_pending)`. Each grant decrements it. While `r_burst_remaining > 0` and `r_pending > 0`, `refresh_drain_active_o` is asserted, which the arbiter reads as "keep granting REF back-to-back without yielding to reads/writes". Setting `refresh_burst_i = 1` disables batching (one REF per tREFI).

### REFpb Bank Rotor

When `refpb_mode_i` is set (LPDDR2 per-bank refresh), `r_bank_rotor` advances 0..`NUM_BANKS-1` on each grant and is exposed on `refresh_bank_o`. In REFab mode it stays at 0. The current default build wires `refpb_mode_i = 0` (REFab) in the scheduler.

## Arbiter-Side Refresh Sequence

`refresh_ctrl` only raises `refresh_req` / `refresh_drain`. The precharge-then-REF sequence is performed by `pumice_cmd_arbiter` at refresh priority (second only to init):

1. While any bank on the target rank has an open row, precharge the active banks one per cycle (lowest ready bank first, honoring the ACT/PRE guard).
2. Once no bank has an open row **and `w_ref_safe` holds** — nothing
   row-affecting in flight or inside its 2-cycle guard window (the registered
   bank view alone is 2-3 cycles stale, which once let a REFab collide with a
   just-issued ACT), and the previous REF's tRFC recovery elapsed — issue
   `OP_REF` and assert `refresh_grant_o` to `refresh_ctrl`, decrementing the
   accumulator / drain quota. On each fired REF the arbiter loads a **tRFC
   down-counter** from `TIMINGS_RFC_REFI.tRFC` (`t_rfc_i`); while non-zero,
   ACT picks and further REFs are blocked (mission-mode refresh recovery —
   init-time refreshes wait `INIT_TIMING1.t_rfc_wait` separately).
3. Repeat back-to-back while `refresh_drain_active` is high (each REF spaced
   by tRFC), until the accumulator is drained.

This "wait until all banks are precharged" behavior is implicit in the arbiter's readiness gating rather than an explicit bank-grant handshake.

## Notes and Scope

- **Self-refresh / power-down** are handled by the separate `powerdown_ctrl` block (see `05_init_power.md`), not by `refresh_ctrl`.
- **PASR, DARP idle-bank-first selection, temperature-compensated tREFI, and periodic ZQCS** are not part of the current `refresh_ctrl` RTL. REFpb selection is a simple bank rotor; the richer selection policies remain future work.
- **REFab vs REFpb** for LPDDR2 is selectable via `refpb_mode_i` and the bank rotor, but the default build uses REFab.
