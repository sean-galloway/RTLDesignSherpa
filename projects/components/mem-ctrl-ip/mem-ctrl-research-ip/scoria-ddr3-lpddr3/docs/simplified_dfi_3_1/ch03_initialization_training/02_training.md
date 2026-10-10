# Training in DFI 3.1

DFI 3.1 supports four training operations. A system does not have to use
them all; the DRAM class and the PHY capabilities determine which are
required.

## Which training is used where

| Training | DDR3 | LPDDR3 | Notes |
| --- | --- | --- | --- |
| Gate training | Yes | Yes | Centers read DQS gate in preamble. |
| Read data eye training | Yes | Yes | Centers read DQS in DQ eye. |
| Write leveling | Yes | Yes | Aligns write DQS to DRAM clock. |
| CA training | No | Yes | LPDDR3 only; optimizes CA timing. |

: Training operations by memory type

For DFI compliance the MC must support the training operations that apply
to the DRAM types it supports. The PHY may optionally support each
operation.

## DFI training mode

In DFI training mode the MC sets the DRAM into the appropriate training
mode, issues the necessary read commands or write strobes, and lets the PHY
adjust its own delays. The PHY signals completion by asserting
`dfi_rdlvl_resp`, `dfi_wrlvl_resp` or `dfi_calvl_resp`. The MC then de-
asserts the enable and returns to normal operation.

The MC must finish all normal traffic before starting training. During
training the only timing parameters that matter are:

- `trdlvl_rr`: minimum spacing between read training reads.
- `twrlvl_ww`: minimum spacing between write leveling strobes.
- `tcalvl_cc`: minimum spacing between CA calibration commands.

## Read training sequence

1. The PHY asserts `dfi_rdlvl_req` (data eye) or `dfi_rdlvl_gate_req`
   (gate). It may indicate the target chip select on
   `dfi_phy_rdlvl_cs_n` or `dfi_phy_rdlvl_gate_cs_n`.
2. The MC responds with `dfi_rdlvl_en` or `dfi_rdlvl_gate_en` within
   `trdlvl_resp` cycles.
3. The MC issues training reads at least `trdlvl_rr` cycles apart. For
   DDR3 these are normal reads; for LPDDR3 they are mode-register reads.
4. The PHY completes its delay search and asserts `dfi_rdlvl_resp`.
5. The MC de-asserts the enable.

## Write leveling sequence

1. The PHY asserts `dfi_wrlvl_req`, optionally with `dfi_phy_wrlvl_cs_n`.
2. The MC responds with `dfi_wrlvl_en` within `twrlvl_resp` cycles.
3. The MC issues MRS commands to enter and exit write leveling mode in the
   DRAM.
4. The MC issues `dfi_wrlvl_strobe` pulses at least `twrlvl_ww` cycles
   apart; the PHY captures the DQ response after each strobe.
5. The PHY asserts `dfi_wrlvl_resp` when complete.
6. The MC de-asserts `dfi_wrlvl_en`.

## CA training sequence (LPDDR3)

1. The PHY may assert `dfi_calvl_req` with `dfi_phy_calvl_cs_n`.
2. The MC responds with `dfi_calvl_en` within `tcalvl_resp` cycles.
3. The MC drives calibration patterns on `dfi_address` and calibration
   commands on `dfi_cs_n`, with `dfi_cke` used to enable DRAM outputs.
4. The MC asserts `dfi_calvl_capture` `tcalvl_capture` cycles after a
   calibration command so the PHY captures the returned DQ value.
5. The PHY reports progress on `dfi_calvl_resp`.
6. The MC de-asserts `dfi_calvl_en` when `dfi_calvl_resp` indicates
   completion.

## Periodic vs full training

`dfi_lvl_periodic` selects the training length:

- `0`: full training, used at initialization, self-refresh restart or after
  large delay changes.
- `1`: periodic training, a shorter tuning pass during normal operation.

## Non-DFI training mode and PHY-requested training

If the PHY supports non-DFI training, it may request the DRAM bus with
`dfi_phylvl_req_cs_n`. The MC grants it with `dfi_phylvl_ack_cs_n` only
when the bus is idle and all pages are closed. The PHY then trains on its
own and returns control when done. This is new in v3.1 and is separate
from the DFI training sequences above.

**Source:** DFI Specification v3.1 sections 3.6, 4.11, Table 16, Table 17, Table 18
