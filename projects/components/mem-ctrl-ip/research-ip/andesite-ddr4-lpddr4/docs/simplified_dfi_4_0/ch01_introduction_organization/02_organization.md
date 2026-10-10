# Organization of the DFI 4.0 Interface

## Sub-interface map

DFI 4.0 groups signals into sub-interfaces. Each group has its own direction, width naming, and
timing parameters. The andesite controller drives most of them and ignores a few that are not
required at its design point.

| Sub-interface | Direction | Purpose | DFI 4.0 section |
| --- | --- | --- | --- |
| Control | MC -> PHY | Commands, address, bank, bank-group, CKE, CS, ODT, reset | 3.1 |
| Write Data | MC -> PHY | Write data, byte mask/write DBI, write enable, write CS | 3.2 |
| Read Data | PHY -> MC (data), MC -> PHY (enables) | Read data, read valid, read DBI, read enable, read CS | 3.3 |
| Update | Both | MC-initiated and PHY-initiated update handshakes | 3.4 |
| Status | Both | Init, frequency, clock disable, parity, alert | 3.5 |
| DFI Training | Both | Gate, read data eye, write leveling, CA, write DQ training | 3.6 |
| Low Power Control | MC -> PHY (req), PHY -> MC (ack) | Low-power opportunity requests | 3.7 |
| Error | PHY -> MC | PHY-detected error indication and info | 3.8 |
| DB Training | Both | DDR4 LRDIMM data-buffer training | 3.9 |
| PHY Master | PHY -> MC (req), MC -> PHY (ack) | PHY takes control of the DRAM bus | 3.10 |
| Geardown | MC -> PHY | DDR4 geardown-mode enable | 3.13 |
| LPDDR4 Channels | MC/PHY/system | Channel enable for LPDDR4 combined/independent modes | 3.14 |

: DFI 4.0 sub-interface map

## Clocking

DFI is clocked by the DFI clock. In a matched-frequency (1:1) system the DFI clock and the DRAM
clock run at the same rate. In frequency-ratio systems the DFI PHY clock is a divided version of
the DRAM clock: 1:2 means one DFI clock per two DRAM clocks; 1:4 means one DFI clock per
four DRAM clocks.

The andesite design point uses a 1:4 frequency ratio inherited from its predecessor. Four phases of
control and write data are transferred per DFI clock; read data is returned as words that map back
to those phases.

## Phase, word and cycle replication

DFI 4.0 replicates signals with suffixes that depend on the sub-interface:

- `_pN` (phase): used on control, write data, read enable, parity, and training strobes. Phase 0
  may drop the suffix.
- `_wN` (data word): used on read data, read data valid, read data DNV, read data DBI, and
  DB training response.
- `_aN` (clock cycle): used on `dfi_alert_n`.

For a 1:4 system, `_p0` through `_p3` carry the four DRAM-clock phases of each DFI clock. The
MC may issue commands on any phase; the PHY must accept commands on any phase. For read
data, `_w0` through `_w3` carry the corresponding data words.

## Slices and channels

A **slice** is an independent data-logic component in the PHY. DFI minimizes slice-to-slice
communication and replicates data-control signaling for point-to-point MC-PHY connectivity. In
andesite, slices correspond to x8 or x16 data groups; training enables like `dfi_rdlvl_en` are one
bit per slice.

**LPDDR4 channels** are a DFI 4.0 concept. LPDDR4 devices may be configured as two
independent 16-bit channels or one combined 32-bit channel. The `phychannel_en` parameter tells
the PHY which channels are enabled. The andesite design point uses one DFI bus per channel at
x16 width.

**Source:** DFI Specification v4.0 sections 3.0, 3.11, 3.14, 4.9
