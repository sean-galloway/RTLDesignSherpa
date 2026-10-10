# Training Interface

DFI 3.1 defines four training operations: gate training, read data eye
training, write leveling and CA training. Gate training and read data eye
training together are called "read training". The DRAM class determines
which operations a system uses.

| Operation | DRAM classes | Purpose |
| --- | --- | --- |
| Gate training | DDR4, DDR3, LPDDR3, LPDDR2 | Center the read DQS gate in the read preamble. |
| Read data eye training | DDR4, DDR3, LPDDR3, LPDDR2 | Center read DQS in the DQ data eye. |
| Write leveling | DDR4, DDR3, LPDDR3 | Align write DQS to the DRAM clock. |
| CA training | LPDDR3 only | Optimize CA bus setup/hold relative to the memory clock. |

: Training operations in DFI 3.1

## Read training signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_rdlvl_en` | MC | DFI Read Leveling MC I/F Width | 0x0 | Enables read data eye training logic in the PHY. |
| `dfi_rdlvl_req` | PHY | DFI Read Leveling PHY I/F Width | 0x0 | PHY requests read data eye training; MC must respond with `dfi_rdlvl_en` within `trdlvl_resp` cycles. |
| `dfi_rdlvl_gate_en` | MC | DFI Read Leveling MC I/F Width | 0x0 | Enables gate training logic in the PHY. |
| `dfi_rdlvl_gate_req` | PHY | DFI Read Leveling PHY I/F Width | 0x0 | PHY requests gate training; MC must respond with `dfi_rdlvl_gate_en` within `trdlvl_resp` cycles. |
| `dfi_rdlvl_resp` | PHY | DFI Read Leveling Response Width | none | Per-slice indication that training is complete. |
| `dfi_phy_rdlvl_cs_n` | PHY | CS Width x Read Training PHY I/F Width | 0x1 | Target chip select for read data eye training. |
| `dfi_phy_rdlvl_gate_cs_n` | PHY | CS Width x Read Training PHY I/F Width | 0x1 | Target chip select for gate training. |

: Read training signals

When either read-training enable de-asserts, both the MC and the PHY must
reset their DFI read data word pointers to zero.

## Write leveling signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_wrlvl_en` | MC | DFI Write Leveling MC I/F Width | 0x0 | Enables write leveling logic in the PHY. |
| `dfi_wrlvl_req` | PHY | DFI Write Leveling PHY I/F Width | 0x0 | PHY requests write leveling; MC must respond with `dfi_wrlvl_en` within `twrlvl_resp` cycles. |
| `dfi_wrlvl_strobe` | MC | DFI Write Leveling MC I/F Width | 0x0 | One-DFI-clock pulse that tells the PHY to capture the write leveling response from DQ. |
| `dfi_wrlvl_resp` | PHY | DFI Write Leveling Response Width | none | Per-slice indication that write leveling is complete. |
| `dfi_phy_wrlvl_cs_n` | PHY | CS Width x Write Leveling PHY I/F Width | 0x1 | Target chip select for write leveling. |

: Write leveling signals

Write leveling is the operation that DDR3 adds over DDR2, and it is the main
reason scoria moved from a v2.1.1-style interface to v3.1.

## CA training signals (LPDDR3)

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_calvl_en` | MC | DFI CA Training MC I/F Width | none | Enables LPDDR3 CA training logic. Also acknowledges `dfi_calvl_req`. |
| `dfi_calvl_req` | PHY | DFI CA Training PHY I/F Width | none | Optional PHY request for CA training. |
| `dfi_calvl_capture` | MC | DFI CA Training MC I/F Width | none | One-cycle pulse telling the PHY to capture the CA value from DQ. |
| `dfi_calvl_resp` | PHY | DFI CA Training Response Width | none | `00`=not done, `01`=done/do not change segment, `10`=done/change segment, `11`=complete. |
| `dfi_phy_calvl_cs_n` | PHY | DFI Chip Select Width | none | Target chip select for CA training. |

: CA training signals

During CA training the control signals `dfi_address`, `dfi_cke` and
`dfi_cs_n` take on training-specific roles: `dfi_address` carries background
and calibration patterns, `dfi_cke` enables DRAM output drivers, and
`dfi_cs_n` becomes the calibration command.

## PHY-requested training in non-DFI training mode

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_phylvl_req_cs_n` | PHY | DFI Rank Width | none | PHY requests control of the DRAM bus to train one chip select. |
| `dfi_phylvl_ack_cs_n` | MC | DFI Chip Select Width | none | MC grants the request when the bus is idle and all pages are closed. |

: PHY-requested training signals

This interface, new in v3.1, lets the PHY ask for the DRAM bus during
normal operation so it can perform its own training without using the DFI
training sequences. The MC idles the bus and grants the request.

## Common training controls

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_lvl_pattern` | MC | 4 bits (DDR4) or 1 bit (LPDDR3/LPDDR2) | 0x0 / 0x1 | Selects the training pattern for gate/read data eye training. |
| `dfi_lvl_periodic` | MC | DFI Leveling PHY I/F Width | 0 | `0`=full/long training; `1`=periodic/short training. |

: Common training control signals

## Training timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `trdlvl_en` | PHY | Minimum cycles from read training enable to first read command. |
| `trdlvl_resp` | MC | Max cycles from `dfi_rdlvl_req`/`dfi_rdlvl_gate_req` to enable assertion. |
| `trdlvl_max` | MC | Max cycles the MC waits for `dfi_rdlvl_resp`. |
| `trdlvl_rr` | PHY | Minimum cycles between read training reads. |
| `twrlvl_en` | PHY | Minimum cycles from write leveling enable to first `dfi_wrlvl_strobe`. |
| `twrlvl_resp` | MC | Max cycles from `dfi_wrlvl_req` to `dfi_wrlvl_en` assertion. |
| `twrlvl_max` | MC | Max cycles the MC waits for `dfi_wrlvl_resp`. |
| `twrlvl_ww` | PHY | Minimum cycles between `dfi_wrlvl_strobe` assertions. |
| `tcalvl_en` | PHY | Minimum cycles from `dfi_calvl_en` to `dfi_cke` de-assertion. |
| `tcalvl_capture` | PHY | Cycles from calibration command to `dfi_calvl_capture` pulse. |
| `tcalvl_resp` | MC | Max cycles from `dfi_calvl_req` to `dfi_calvl_en`. |
| `tcalvl_max` | MC | Max cycles the MC waits for `dfi_calvl_resp`. |
| `tcalvl_cc` | PHY | Minimum cycles between calibration commands. |
| `tphylvl` | PHY | Max cycles `dfi_phylvl_req_cs_n` may stay asserted after acknowledge. |
| `tphylvl_resp` | PHY | Max cycles from request to acknowledge for PHY-requested training. |

: Training interface timing parameters

## Training programmable parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `phyrdlvl_en` | PHY | PHY supports read data eye training. |
| `phyrdlvl_gate_en` | PHY | PHY supports gate training. |
| `phywrlvl_en` | PHY | PHY supports write leveling. |
| `phycalvl_en` | PHY | PHY supports CA training. |

: Training programmable parameters

**Source:** DFI Specification v3.1 sections 3.6, 4.11, Table 16, Table 17, Table 18
