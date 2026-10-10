# Command Mapping

The DFI control interface is essentially a delayed, possibly widened, copy of
the DRAM command interface. How the MC encodes a command depends on the memory
type.

## DDR2 command encoding

For DDR2 the classic command truth table applies directly on the DFI control
signals.

| Command | CS_n | RAS_n | CAS_n | WE_n | Address A10 | Address other | Bank |
| --- | --- | --- | --- | --- | --- | --- | --- |
| NOP | 0 | 1 | 1 | 1 | X | X | X |
| ACT | 0 | 0 | 1 | 1 | row bit | row | bank |
| RD | 0 | 1 | 0 | 1 | 0 | column | bank |
| RDA | 0 | 1 | 0 | 1 | 1 | column | bank |
| WR | 0 | 1 | 0 | 0 | 0 | column | bank |
| WRA | 0 | 1 | 0 | 0 | 1 | column | bank |
| PRE (one bank) | 0 | 0 | 1 | 0 | 0 | X | bank |
| PREA (all banks) | 0 | 0 | 1 | 0 | 1 | X | X |
| REF | 0 | 0 | 0 | 1 | X | X | X |
| DES | 1 | X | X | X | X | X | X |
: DDR2 command encoding on DFI control signals

`dfi_cke` is driven high during normal operation and manipulated separately for
self-refresh or power-down entry. `dfi_odt` is driven according to the DRAM ODT
programming for reads and writes.

## LPDDR2 command encoding

LPDDR2 has no RAS/CAS/WE pins. Commands and a scrambled address are multiplexed
onto a 10-bit CA bus across two clock edges. DFI 2.1 maps the entire CA word
onto `dfi_address` as a flat 20-bit value, while `dfi_bank`, `dfi_ras_n`,
`dfi_cas_n`, and `dfi_we_n` are held idle.

| dfi_address bit | CA bit / edge |
| --- | --- |
| 9:0 | CA[9:0] on rising edge |
| 19:10 | CA[9:0] on falling edge |
: DFI 2.1 LPDDR2 CA mapping

The rising-edge opcode is decoded from CA0r, CA1r, CA2r, CA3r:

| Command | CA0r | CA1r | CA2r | CA3r |
| --- | --- | --- | --- | --- |
| MRW | 0 | 0 | 0 | 0 |
| MRR | 0 | 0 | 0 | 1 |
| Refresh per-bank | 0 | 0 | 1 | 0 |
| Refresh all-bank | 0 | 0 | 1 | 1 |
| Activate | 0 | 1 | X | X |
| Write | 1 | 0 | 0 | X |
| Read | 1 | 0 | 1 | X |
| Precharge | 1 | 1 | 0 | 1 |
| BST | 1 | 1 | 0 | 0 |
| NOP/Deselect | 1 | 1 | 1 | X |
: LPDDR2 rising-edge command opcode

Row, column, bank, and mode-register fields are then placed on the remaining CA
pins according to the JEDEC LPDDR2 command truth table. The PHY splits the
20-bit `dfi_address` word into the two 10-bit DDR CA cycles.

**Source:** DFI Specification v2.1.1 sections 3.1, 4.2; JEDEC JESD209-2F Table 60
