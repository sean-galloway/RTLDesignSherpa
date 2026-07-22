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

# Runtime CSR Fields (Config-Drive Model)

> Per HAS §5.1 for the build-time-vs-runtime principle and §4.2 for the field-level register map. This MAS chapter is the **implementation protocol** for how runtime CSR fields reach the live datapath.
>
> In the rearchitected controller, `pumice_top` wires the register block's `hwif_out.*` fields **by name** directly into `pumice_core` (see `rtl/top/pumice_top.sv`). There is **no** staging/commit two-cell architecture, **no** `CTRL.config_apply`, **no** `STATUS.config_settled`, and **no** quiet-point drain FSM. A CSR write updates the field's storage and the corresponding core input tracks it combinationally.

---

## What "Runtime" Means Here

Most of the controller's behavior is programmed at runtime by CSR fields, not fixed by parameters. The following are all live CSR-driven core inputs (see the `u_core` port map in `rtl/top/pumice_top.sv`):

| Domain            | CSR field(s)                                                        | Core input                              |
|-------------------|---------------------------------------------------------------------|-----------------------------------------|
| Memory type       | `PHY_TIMING.memtype`                                                 | `memtype_i` (0=DDR2, 1=LPDDR2)          |
| Page policy       | `REFRESH_TUNING.page_policy_or`                                     | `page_policy_i`                         |
| Address mapping   | `ADDR_MAP.bank_lsb` / `.hash_en` / `.hash_seed`                     | `bank_lsb_i` / `hash_en_i` / `hash_seed_i` |
| Core JEDEC timing | `TIMINGS_RC_RCD_RP_RAS`, `TIMINGS_CL_CWL_WR.tWR`, `TIMINGS_RTP_RTW`, `TIMINGS_RRD_FAW_WTR_CCD`, `TIMINGS_RFC_REFI.tREFI` | `t_rcd_i`/`t_rp_i`/`t_ras_i`/`t_rc_i`/`t_wr_i`/`t_rtp_i`/`t_rtw_i`/`t_faw_i`/`t_rrd_i`/`t_wtr_i`/`t_ccd_i`/`t_refi_i` |
| Refresh burst     | `PHY_TIMING.refresh_burst`                                          | `refresh_burst_i`                       |
| Init waits        | `INIT_TIMING0` / `INIT_TIMING1`                                     | `t_init_wait_i`/`t_dll_wait_i`/`t_mrd_wait_i`/`t_rp_wait_i`/`t_rfc_wait_i` |
| DFI phase         | `DFI_PHASE.rd_phase` / `.wr_phase`                                  | `rd_phase_i`/`wr_phase_i` (sliced to `clog2(DFI_RATE)`) |
| PHY data timing   | `PHY_TIMING.t_phy_wrlat` / `.t_rddata_en`                          | `t_phy_wrlat_i`/`t_rddata_en_i`         |

CL/CWL/BL are **not** driven from the timing CSRs at the core boundary — they are decoded from the mode-register shadow inside the scheduler layer (`mode_register.sv`) as the init sequencer programs MR0..MR3 (see §5.1). The `TIMINGS_CL_CWL_WR.CL`/`.CWL` fields are informational in this build.

## Commit Semantics

Because the fields drive the core directly, a write takes effect as soon as it lands in the register storage. There is no explicit apply step. Two practical timing classes:

| Class                         | Fields                                                       | When it takes effect                          |
|-------------------------------|--------------------------------------------------------------|-----------------------------------------------|
| Sampled at an event boundary  | JEDEC timings, refresh interval/burst, page policy, scheduler knobs | On the next counter reload / arbiter decision that consumes the value |
| Sampled continuously          | `memtype`, `bank_lsb`/`hash_*`, DFI phase, PHY data timing    | Combinationally; affects the next command that uses the mapper/formatter |

## Safe-Change Guidance

The controller does not enforce a quiet point, so **software** is responsible for not changing a field mid-transaction when that would corrupt in-flight state:

- **Timings, page policy, scheduler knobs, refresh interval**: safe to change during light traffic; the new value is picked up at the next event boundary. For a clean swap, quiesce AXI traffic first (stop issuing, let outstanding responses drain) then write.
- **`memtype`, address-map (`bank_lsb`/`hash_*`)**: these define how addresses decode and how commands are encoded. Change them **only before init** (or with the datapath fully idle). Changing address mapping under traffic re-decodes in-flight addresses inconsistently.
- **DFI phase / PHY data timing**: board bring-up knobs; set once during bring-up and leave fixed. `rd_phase`/`t_rddata_en`/`t_phy_wrlat` are matched to the attached PHY (the Nexys A7 a7ddrphy bring-up tuple, board-validated 2026-07-21: `rd_phase=0`, `t_rddata_en=6`, `t_phy_wrlat=1`, plus harness `DFI_TUNING.rddata_delay=7`).

## Recommended Programming Order

For a clean bring-up the register writes happen while init is still gated (before `CTRL.init_start`):

```c
// 1. Select memory type and address mapping (must be set before init)
csr_write(PHY_TIMING, memtype_field | t_rddata_en_field | t_phy_wrlat_field | refresh_burst_field);
csr_write(ADDR_MAP,   bank_lsb_field | hash_en_field | hash_seed_field);

// 2. Program JEDEC timings for the attached part
csr_write(TIMINGS_RC_RCD_RP_RAS, ...);
csr_write(TIMINGS_RFC_REFI,      ...);
csr_write(TIMINGS_RRD_FAW_WTR_CCD, ...);
csr_write(TIMINGS_CL_CWL_WR,     ...);
csr_write(TIMINGS_RTP_RTW,       ...);
csr_write(INIT_TIMING0, ...);  csr_write(INIT_TIMING1, ...);

// 3. Program MR0..MR3 and (LPDDR2) PASR
csr_write(MR0, ...); csr_write(MR1, ...); csr_write(MR2, ...); csr_write(MR3, ...);

// 4. Trigger init — the values above are already live at the core boundary
csr_write(CTRL, CTRL_INIT_START);
```

There is no apply/poll handshake between the writes — each write is already visible to the core.

## Open Questions / Future Work

- **Mid-traffic re-tuning guard.** A future revision could add an optional per-field commit gate (re-introducing a lightweight quiet point) for fields that software wants to change under load. Not present in this build.
- **CL/CWL CSR coupling.** The `TIMINGS_CL_CWL_WR.CL`/`.CWL` fields are currently informational; the live decode comes from the MR shadow. Deciding whether the CSR or the MR shadow is authoritative is a cleanup item.
- **Observation readback.** `STATUS`/`OBS_*` are declared but `hwif_in` is tied off in `pumice_top` (see §4.1); wiring them back is a follow-up.
