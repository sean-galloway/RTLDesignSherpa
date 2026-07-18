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

# Register Access Interface (PeakRDL cpuif)

> Per HAS §2.4 §3 for the per-signal port list and HAS §4.3 for the architectural view. This chapter is the **wire-level contract** for the controller's register access interface.
>
> The register block is a PeakRDL-generated module (`pumice_csr`, from `rtl/macro/pumice_csr.rdl`) instantiated directly in `pumice_top`. It exposes a **PeakRDL passthrough CPU interface** (`s_cpuif_*`), not a hand-written APB slave. Any APB (or AXI-Lite) bridge is **external/optional** — the SoC attaches whatever register transport it uses and drives the cpuif. All register storage lives in the `aclk` (MC) domain; there is no separate `apb_pclk` domain and no on-die CDC inside the register block.

---

## The cpuif Contract

`pumice_top` presents the PeakRDL passthrough interface on `aclk`/`aresetn`:

| Direction | Signal                    | Meaning                                             |
|-----------|---------------------------|-----------------------------------------------------|
| in        | `s_cpuif_req`             | Request strobe                                      |
| in        | `s_cpuif_req_is_wr`       | 1 = write, 0 = read                                 |
| in        | `s_cpuif_addr[11:0]`      | Byte address (12-bit, 4 KB region)                  |
| in        | `s_cpuif_wr_data[31:0]`   | Write data                                          |
| in        | `s_cpuif_wr_biten[31:0]`  | Per-bit write-enable (bit strobe)                   |
| out       | `s_cpuif_req_stall_wr`    | Back-pressure a write request                       |
| out       | `s_cpuif_req_stall_rd`    | Back-pressure a read request                        |
| out       | `s_cpuif_rd_ack`          | Read response valid                                 |
| out       | `s_cpuif_rd_err`          | Read decode error (unmapped address)                |
| out       | `s_cpuif_rd_data[31:0]`   | Read data                                           |
| out       | `s_cpuif_wr_ack`          | Write response valid                                |
| out       | `s_cpuif_wr_err`          | Write decode error (unmapped address)               |

The interface is single-request/single-response with a stall handshake. Registers are 32-bit, naturally aligned on 4-byte boundaries. Sub-word writes use `s_cpuif_wr_biten` (per-bit granularity); a full-word write drives all 32 biten bits.

## Attaching an APB / AXI-Lite Bridge

Because the interface is a generic passthrough cpuif, the register transport is an integration choice made **outside** this controller:

- An APB3/APB4 slave bridge translates `psel`/`penable`/`pwrite`/`paddr`/`pwdata`/`prdata`/`pslverr` to the cpuif and back. `pslverr` maps from `s_cpuif_rd_err`/`s_cpuif_wr_err`.
- An AXI-Lite slave bridge is equally valid; the cpuif does not assume APB.
- If the register bus is in a different clock domain than `aclk`, the CDC lives in that external bridge — not in `pumice_csr`.

No `pumice_top` parameter selects the transport; the bridge is a separate module in the SoC's register fabric.

## Address Space

The register block decodes a 4 KB region (12-bit address). Layout, matching `rtl/macro/pumice_csr.rdl`:

| Address range  | Region                                                   |
|----------------|----------------------------------------------------------|
| 0x000 – 0x008  | Control / Status / Status-history                        |
| 0x010 – 0x01C  | Timing parameters (RC/RCD/RP/RAS, RFC/REFI, RRD/FAW/WTR/CCD, CL/CWL/WR) |
| 0x020 – 0x02C  | Mode Register values (MR0..MR3)                          |
| 0x030 – 0x038  | LPDDR2-specific (PASR bank/segment masks, temp derate)   |
| 0x040 – 0x05C  | Scheduler / Page / Refresh / Addr-map / Init tuning + init timing |
| 0x054, 0x060, 0x064 | tRTP/tRTW, DFI command phase, PHY/DFI data timing    |
| 0x080 – 0x09C  | Per-bank row-hit observation (NUM_BANKS = 8)             |
| 0x0C0 – 0x0DC  | Per-bank refresh-latency observation                     |
| 0x100 – 0x138  | System observation / telemetry                           |
| 0x1C0 – 0x1E0  | Packed observation-word harvest (9 words)                |
| 0xFF0 – 0xFF4  | Module identification + build hash                        |

The complete register/field table is in §4.2; it is generated from the RDL and must match it exactly.

## Behavior

### Access Cycles

Each request drives `s_cpuif_req` with `s_cpuif_req_is_wr`, `s_cpuif_addr`, and (for writes) `s_cpuif_wr_data`/`s_cpuif_wr_biten`. The block responds with `s_cpuif_rd_ack`/`s_cpuif_wr_ack` (and optionally asserts a stall while it is busy). Reads return `s_cpuif_rd_data`; unmapped accesses assert `s_cpuif_rd_err`/`s_cpuif_wr_err`.

### Sub-Word Accesses

`s_cpuif_wr_biten` carries a per-bit write mask, so byte- or field-level writes are supported natively. A bridge that lacks byte strobes simply drives all biten bits on every write.

### Error Conditions

The block asserts a decode error (`s_cpuif_rd_err` / `s_cpuif_wr_err`) for:

| Condition                                        | Notes                                       |
|--------------------------------------------------|---------------------------------------------|
| Access to an unmapped address (gaps / RSVD)      | `rd_err`/`wr_err`; read data is 0            |
| Write to a read-only register/field              | Write is dropped; field unchanged           |

Writes to reserved (`sw = r`) fields inside an otherwise-writable register are ignored per the RDL field access; the register keeps its value. There is no scheme/rule sub-decode error (the old `ADDR_MAP_TUNING` scheme decode is retired — address mapping is now the plain `ADDR_MAP.bank_lsb` field, see §4.2/§4.4).

## Config-Drive Model

`pumice_top` wires the register block's `hwif_out.*` outputs **by name** directly into `pumice_core` (see the top-level instantiation in `rtl/top/pumice_top.sv`). Configuration is therefore live combinational drive from the register storage into the datapath — software writes a field and the corresponding core input tracks it. There is no staging/commit or quiet-point protocol in this architecture (see §4.3). Status/observation readback (`hwif_in.*`) is currently tied off in `pumice_top`.

## Open Questions / Future Work

- **Observation readback.** `hwif_in` is presently tied to 0; wiring the live status/telemetry counters back into the read path is a follow-up.
- **Bridge selection.** The passthrough cpuif is transport-agnostic. A packaged APB and AXI-Lite bridge pair (with the CDC option) would simplify SoC integration.
- **Quiet-point commit.** The old two-cell staging/commit model was removed with the config-drive refactor. If a future field must not change mid-transaction, a per-field commit gate can be reintroduced.
