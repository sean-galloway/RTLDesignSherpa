# Training Operations

DFI 4.0 training moves the calibration of read gates, data eyes, write DQS/DQ timing, and CA
alignment from the MC into a cooperative MC/PHY protocol. The PHY evaluates DRAM responses
and adjusts delay settings; the MC sets up the DRAM, issues training commands, and responds to
PHY requests.

## Training modes

Two modes exist:

- **DFI Training Mode:** MC and PHY cooperate through the DFI training handshake. This is the
  mode described in this book.
- **PHY Independent Mode:** PHY runs training autonomously after initialization. The MC does not
  participate beyond enabling the capability.

The andesite controller implements DFI Training Mode for the training operations it supports.

## Gate training

Gate training finds the delay at which the read DQS preamble can be reliably captured. The MC
asserts `dfi_rdlvl_gate_en` for the target slice(s), issues the read or MRR commands required by
the memory type, and the PHY adjusts the gate delay until the DQS window is centered.

When complete, the PHY drives `dfi_rdlvl_resp = 'b11`. The MC then de-asserts
`dfi_rdlvl_gate_en`. The `dfi_lvl_pattern` signal selects the pattern for read data eye training but is
not used for gate training.

## Read data eye training

Read data eye training centers the read capture clock in the valid data eye. The MC asserts
`dfi_rdlvl_en` for the target slice(s) and issues read/MRR commands. The PHY evaluates the data
and adjusts read delay.

If the PHY returns `dfi_rdlvl_resp = 'b01`, the current sequence is complete but more sequences
remain. The MC de-asserts `dfi_rdlvl_en`, sets up the next sequence (e.g., next `dfi_lvl_pattern`
value), and re-asserts `dfi_rdlvl_en`. When the PHY returns `'b11`, training is complete.

For LPDDR4, `dfi_lvl_pattern` is an index into a programmed pattern table rather than a direct
pattern encoding.

## Write leveling

Write leveling aligns the write DQS rising edge with the DRAM clock rising edge. The MC asserts
`dfi_wrlvl_en`, then asserts `dfi_wrlvl_strobe` for the number of clocks defined by
`syswrlvl_strobe_num`. The PHY samples the DQ bus response and adjusts write DQS delay.

When the PHY returns `dfi_wrlvl_resp = 'b1`, write leveling is complete for that slice.

## CA training

CA training is required for LPDDR3 and LPDDR4. The MC asserts `dfi_calvl_en`, drives the
calibration command on `dfi_cs`, and uses `dfi_calvl_capture` to tell the PHY when to sample the
CA value returned on the DQ bus. For LPDDR4 CA VREF training, the MC drives `dfi_calvl_data`,
asserts `dfi_calvl_strobe` to generate DQS pulses, and uses `dfi_calvl_done` and
`dfi_calvl_result` to iterate to the best VREF setting.

## Write DQ training

Write DQ training is new in DFI 4.0 and centers the clock in the write DQ eye. The MC asserts
`dfi_wdqlvl_en`, issues a sequence of write bursts followed by matching read bursts, and iterates
VREF values using `dfi_wdqlvl_done` and `dfi_wdqlvl_result`. The PHY returns
`dfi_wdqlvl_resp` status. This training is unused unless both MC and PHY are DFI 4.0 devices.

## DB training

DB training supports DDR4 LRDIMM data-buffer training in PHY evaluation mode. The MC asserts
`dfi_db_train_en`, transfers commands through the PHY, and evaluates `dfi_db_train_resp`. This
is specialized to LRDIMM systems and is not part of the andesite design point.

## PHY master during training

The PHY master interface can be used when the PHY needs to take control of the DRAM bus for
extended calibration. The PHY asserts `dfi_phymstr_req`; the MC places the DRAM in IDLE or self-
refresh and asserts `dfi_phymstr_ack`. The MC may still forward refresh commands, which the
PHY relays to the DRAM. This is a DFI 4.0 feature and is not required for basic DDR4/LPDDR4
operation.

## Training chip-select renaming

A subtle but important 3.1 -> 4.0 change is the removal of the `_n` suffix on training chip-select
signals. DFI 4.0 uses `dfi_phy_wrlvl_cs`, `dfi_phy_rdlvl_cs`, `dfi_phy_rdlvl_gate_cs` and
`dfi_phy_calvl_cs`. The polarity is the same as `dfi_cs`; the name simply no longer embeds the
active-low assumption.

**Source:** DFI Specification v4.0 sections 3.6, 3.9, 3.10, 3.12, 4.12, 4.15, 4.16
