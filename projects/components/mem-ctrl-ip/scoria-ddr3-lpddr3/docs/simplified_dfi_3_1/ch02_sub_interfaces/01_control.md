# Control Interface

The control interface carries the command, address and control signals that
the MC sends to the PHY. The PHY must preserve bit ordering and timing
relationships so that, after its own `tctrl_delay`, the signals arrive at the
DRAM pins correctly aligned.

## Command/address signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_address` | MC | DFI Address Width | none | Address bus. For DDR3 carries row/column address; for LPDDR3/LPDDR2 it maps the double-data-rate CA bus and must be at least 20 bits. |
| `dfi_bank` | MC | DFI Bank Width | none | Bank select bits. |
| `dfi_bg` | MC | DFI Bank Group Width | none | Bank group, DDR4 only. Unused for DDR3/LPDDR3. |
| `dfi_cid` | MC | DFI Chip ID Width | none | Stacked-device chip ID, DDR4 only. Unused for DDR3/LPDDR3. |
| `dfi_act_n` | MC | 1 bit | none | DDR4 command encoding; held constant for LPDDR3/LPDDR2. |
| `dfi_cas_n` | MC | DFI Control Width | 0x1 | Column address strobe / command bit. |
| `dfi_ras_n` | MC | DFI Control Width | 0x1 | Row address strobe / command bit. |
| `dfi_we_n` | MC | DFI Control Width | 0x1 | Write enable / command bit. |

: Control interface command and address signals

In a frequency-ratio system these signals become `dfi_address_pN`,
`dfi_bank_pN`, `dfi_cas_n_pN`, and so on. The MC may place a command on any
phase; the PHY must accept commands on any and all phases.

## DRAM enable and select signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_cs_n` | MC | DFI Chip Select Width | 0x1 | Chip select. Low active. For LPDDR3 CA training it carries the calibration command on the bit being trained. |
| `dfi_cke` | MC | DFI Chip Select Width | 0x0 or 0x1 | Clock enable. Must be driven in all phases. For LPDDR3 CA training it enables DRAM output drivers. |
| `dfi_odt` | MC | DFI Chip Select Width | 0x0 | On-die termination control. Used by DDR3, DDR2 and LPDDR3. Must be driven in all phases. |
| `dfi_reset_n` | MC | DFI Chip Select Width | 0x0 or 0x1 | DRAM reset. Used by DDR4 and DDR3. |

: Control interface enable and select signals

## LPDDR3/LPDDR2 CA-bus mapping

For LPDDR3 and LPDDR2, the DRAM CA bus is double data rate and is mapped
onto the 20-bit `dfi_address` bus. The PHY transmits `dfi_address[9:0]` on
the rising CA edge and `dfi_address[19:10]` on the falling CA edge. During
these operations the signals `dfi_act_n`, `dfi_bank`, `dfi_bg`, `dfi_cid`,
`dfi_cas_n`, `dfi_ras_n` and `dfi_we_n` must be held constant, and
`dfi_address` must drive a NOP until `dfi_init_complete` asserts.

## Control timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `tcmd_lat` | MC | DFI PHY clock cycles from `dfi_cs_n` assertion to the associated CA signals being driven. |
| `tctrl_delay` | PHY | DFI clock cycles from a control signal change until that change reaches the DRAM interface. |

: Control interface timing parameters

`tctrl_delay` is what makes the DFI contract practical: the MC issues
signals on its clock, and the PHY promises to deliver them to the DRAM
after a fixed, rounded-up delay.

**Source:** DFI Specification v3.1 sections 3.1, 4.2, Table 4, Table 5
