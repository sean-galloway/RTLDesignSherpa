# mc_ras_layer — knob inventory and CSR surface

Skeleton created 2026-10-10 as part of the mem-ctrl-ip layer-stack extraction
(Phase 2b). The layer is **not yet instantiated into any research controller**;
it exists so future ECC work has a defined seam and so the parameter/CSR
surface can be reviewed before a customer is wired in.

## Layer boundary

`mc_ras_layer` sits on the two data seams:

- **Write-data forward**: upstream write-data stream -> downstream.
- **Read-return backward**: downstream read-return stream -> upstream.

At `HAS_ECC = ECC_OFF` (the default) both seams are straight assigns with no
extra logic. This is the zero-cost baseline for controllers that do not enable
RAS features.

## Parameters

| Parameter | Type / default | Meaning |
|---|---|---|
| `HAS_ECC` | `int` `0` | `ECC_OFF` (0): passthrough only. `ECC_DETECT` (1): detect errors (reserved). `ECC_CORRECT` (2): correct errors (reserved). |
| `ECC_MODE` | `int` `0` | Reserved knob for in-band vs. side-band ECC code placement. Not yet implemented; documented so the CSR surface does not need to change when the feature lands. |
| `ECC_CODE_WIDTH` | `int` `8` | Reserved knob for the width of the ECC code word. Not yet implemented. |
| `DATA_WIDTH` | `int` `64` | Width of the data beat on both seams. |
| `STRB_WIDTH` | `int` `DATA_WIDTH/8` | Byte-strobe width on the write-data seam. |

## Reserved CSR surface

The following register fields are reserved in the layer header so a future
CSR integration can adopt them without re-plumbing the module boundary.

| Field | Width | Access | Description |
|---|---|---|---|
| `CTRL.ECC_EN` | 1 | rw | Master ECC enable. Reads 0 and has no effect when `HAS_ECC = ECC_OFF`. |
| `CTRL.ECC_MODE` | 2 | rw | ECC operating mode (maps to `ECC_MODE` parameter values). Reserved. |
| `STAT.CORR_CNT` | 16 | ro | Corrected-error counter. Reserved. |
| `STAT.UNCORR_CNT` | 16 | ro | Uncorrectable-error counter. Reserved. |

No hardware interface to a CSR generator is wired yet; the module exposes the
above as ports (`csr_ecc_en_i`, `csr_ecc_mode_i`, `csr_ecc_stat_o`) and drives
them to zero when ECC is off.

## Deferrals

- ECC encoder/decoder logic is intentionally absent. The skeleton proves the
  seam and parameter surface; implementation waits for a real enabling customer.
- Scrubber design is deferred to the scheduler-merge task. When added, the
  scrubber will be a maintenance-class client of the scheduler/prospect pool
  (peer of refresh and training), injecting read descriptors that inherit the
  existing read-snoop hazard rules.
