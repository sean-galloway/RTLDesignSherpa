# Control Interface

The control interface carries the command and address information that the MC
wants the PHY to reflect to the DRAM devices. The PHY may delay these signals
by `tctrl_delay` cycles, but it must preserve their timing relationship and bit
ordering at the PHY-DRAM boundary.

In a frequency-ratio system every control signal becomes phase-specific:
`dfi_address_pN`, `dfi_bank_pN`, `dfi_cas_n_pN`, and so on. Phase 0 may drop the
suffix. The MC may issue commands on any phase; the PHY must accept commands on
all phases.

## Control signals

| Signal | Direction | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| dfi_address | MC -> PHY | DFI address width | no default | Address bus for all control commands. For LPDDR2 it carries the 20-bit CA word. |
| dfi_bank | MC -> PHY | DFI bank width | no default | Bank select for DDR1/LPDDR1/DDR2/DDR3; idle for LPDDR2. |
| dfi_cas_n | MC -> PHY | DFI control width | 0x1 | Column-address strobe. Idle for LPDDR2. |
| dfi_cke | MC -> PHY | DFI chip select width | 0x0 or 0x1 | Clock enable to DRAMs; must be driven in all phases for ratio systems. |
| dfi_cs_n | MC -> PHY | DFI chip select width | 0x1 | Chip select, active low. |
| dfi_odt | MC -> PHY | DFI chip select width | 0x0 | On-die termination control; required for DDR2/DDR3. |
| dfi_ras_n | MC -> PHY | DFI control width | 0x1 | Row-address strobe. Idle for LPDDR2. |
| dfi_reset_n | MC -> PHY | DFI chip select width | 0x0 | DRAM reset; required only for DDR3. |
| dfi_we_n | MC -> PHY | DFI control width | 0x1 | Write enable. Idle for LPDDR2. |
: DFI 2.1 control interface signals

## LPDDR2 CA mapping on dfi_address

For LPDDR2 the 10-bit CA bus is sent on both edges of the clock. DFI 2.1 packs
the two 10-bit halves into one `dfi_address` word per command cycle.

| dfi_address bit | CA bit / edge |
| --- | --- |
| 9:0 | CA[9:0] on the rising edge |
| 19:10 | CA[9:0] on the falling edge |
: LPDDR2 CA packing into dfi_address

So `dfi_address[0]` is CA0 on the rising edge, `dfi_address[10]` is CA0 on the
falling edge, and so on up to `dfi_address[19]`. The minimum `dfi_address`
width for LPDDR2 is therefore 20 bits. During initialization the LPDDR2 CA bus
must be driven with a NOP until `dfi_init_complete` asserts.

## Defaults and idle values

Most control signals default to the DRAM idle state: RAS, CAS, and WE are high,
chip select is high, ODT is low, and reset is low. CKE is memory-dependent; most
parts expect CKE low at reset, but Mobile DDR parts may expect it high. For
LPDDR2 the classic RAS/CAS/WE/bank signals are unused and must remain at their
idle values while `dfi_address` carries the CA-encoded command.

## Timing

The only control-interface timing parameter is `tctrl_delay`, defined by the
PHY. It specifies how many DFI clock cycles elapse between an assertion or
de-assertion on the DFI control signals and the same transition appearing at the
PHY-DRAM boundary. If the DFI clock and memory clock are not phase aligned, this
value is rounded up to the next integer.

**Source:** DFI Specification v2.1.1 sections 3.1, 4.2
