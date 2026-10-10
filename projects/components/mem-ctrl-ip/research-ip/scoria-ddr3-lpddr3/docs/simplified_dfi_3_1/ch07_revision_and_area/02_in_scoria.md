# DFI 3.1 in the Scoria Controller

This chapter connects the DFI 3.1 specification to the scoria DDR3/LPDDR3
memory controller as documented in
`projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/scoria_has/ch04_interfaces/01_dfi_v31.md`.

## Why scoria chose v3.1

Scoria targets DDR3 and LPDDR3. Its predecessor pumice used DFI v2.1.1.
The upgrade to v3.1 was driven by DDR3 write leveling: v3.1's per-chip-
select leveling scheme is what future DDR4 work will also need, so paying
for it once in scoria is cheaper than re-implementing it later.

## What scoria inherits

The datapath is inherited almost unchanged from pumice:

- One async-FIFO clock-domain crossing, bubble-free.
- The unit of transfer is a DFI word.
- `DFI_RATE = 4`.

A naive signal-name diff between v2.1.1 and v3.1 might claim that phase
variants such as `dfi_address_p2` were removed. They were not. v2.1.1
listed them explicitly; v3.1 generalized the notation to `_pN`. The 1:4
frequency ratio remains a defined mode.

## What scoria implements from v3.1

| Feature | Scoria implementation |
| --- | --- |
| Write leveling | `scoria_wrlvl_ifc` drives `dfi_wrlvl_*`; firmware-driven search, not a hard-coded state machine. |
| Data path chip select | `dfi_wrdata_cs_n` and `dfi_rddata_cs_n` are driven; at `NUM_RANKS = 1` the value is constant rank 0. |
| `dfi_reset_n` | Driven from the init sequencer and presented as `dfi_reset_n_o` at the DFI boundary. |
| Low power requests | Exposed for spec compliance, but not consumed by the target PHY. |
| Error interface | `dfi_error` is used as a generic flag; DDR4-specific `dfi_error_info` encodings are ignored. |

: Scoria DFI 3.1 implementation highlights

## What scoria does not implement

| Group | Signals | Reason |
| --- | --- | --- |
| DDR4 command encoding | `dfi_act_n*`, `dfi_bg*`, `dfi_cid*` | DDR3 has no dedicated ACT pin, bank groups or chip ID. |
| CA parity, CRC, alert | `dfi_alert_n*`, `dfi_parity_in_p*` | DDR4-era features. |
| Data bus inversion | `dfi_rddata_dbi*` | DDR4/LPDDR4 feature. |
| CA training | `dfi_calvl_*`, `dfi_ca_capture`, `dfi_phy_calvl_cs_n` | LPDDR3 CA training is treated as LPDDR4-era for this controller. |

: DFI 3.1 features deliberately unimplemented in scoria

## Known documentation corrections

The scoria tie-in document notes a few spec-related traps:

- The v2.1.1 -> v3.1 signal diff must not be trusted blindly; phase
  signals are renamed, not removed.
- `dfi_reset_n` is gated on memory type, not DFI version, so any scoria
  DFI claim implies this signal.
- `dfi_wrdata_cs_n` / `dfi_rddata_cs_n` are genuinely v3.1-only and are
  driven even in single-rank mode.

## Study corrections carried into this book

The caveats in the DFI 3.1 inventory are worth remembering:

- Section 3.6 refers to a `dfi_ca_capture` pulse; the actual signal is
  `dfi_calvl_capture`.
- Section 4.11 contains typo variants such as `dfi_phlvl_ack_cs_n`; the
  defined names are `dfi_phylvl_req_cs_n` and `dfi_phylvl_ack_cs_n`.
- `dfi_rdlvl_edge` and timer-based signals such as `dfi_rdlvl_delay_x`
  appear only in revision-history text, not in the v3.1 signal tables.

**Source:** `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/scoria_has/ch04_interfaces/01_dfi_v31.md`; DFI Specification v3.1 sections 3.6, 4.11
