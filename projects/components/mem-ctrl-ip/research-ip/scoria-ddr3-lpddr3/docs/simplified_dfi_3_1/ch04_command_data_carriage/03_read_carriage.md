# Read Carriage

A DFI read transaction is split into the MC's request (`dfi_rddata_en`) and
the PHY's response (`dfi_rddata` plus `dfi_rddata_valid`). The MC knows
how many words to expect; the PHY returns them when ready.

## Read timing parameters in use

| Parameter | Meaning |
| --- | --- |
| `trddata_en` | Cycles from read command to `dfi_rddata_en` assertion. |
| `tphy_rdlat` | Maximum cycles from `dfi_rddata_en` assertion to `dfi_rddata_valid` assertion. |

: Read carriage timing parameters

`trddata_en` and `tphy_rdlat` are normally held constant while commands
flow. They may only be changed when the bus is idle.

## Single read transaction

1. The MC issues a read command on the control interface.
2. `trddata_en` cycles later, the MC asserts `dfi_rddata_en` for the
   expected number of data words. For burst-length-8 this is four DFI data
   words.
3. Within `tphy_rdlat` cycles, the PHY asserts `dfi_rddata_valid` and
   drives the first `dfi_rddata` word.
4. The PHY holds `dfi_rddata_valid` for the same number of cycles that
   `dfi_rddata_en` was asserted.
5. The MC de-asserts `dfi_rddata_en` once the expected data has returned.

## Contiguous vs non-contiguous reads

Like writes, reads may be contiguous or separated by bubbles. The
`dfi_rddata_en` signal can stay asserted across multiple read commands if
no gap is expected; `dfi_rddata_valid` follows with the actual data. The
PHY may return data earlier than the maximum `tphy_rdlat`, so the actual
valid pattern may vary even when the enable is contiguous.

## Per-slice independence

`dfi_rddata_valid` is one bit per PHY data slice. Different slices may
return data on different cycles, and `tphy_rdlat` is the maximum across
all slices. This is important for wide data buses where read capture timing
varies by slice.

## Read chip select timing

When `dfi_rddata_cs_n` is used, the MC drives it `tphy_rdcslat` cycles
after the read command and holds it for the transfer length plus
`tphy_rdcsgap`. If the next read targets a different chip select, the MC
adds `tphy_rdcsgap` cycles.

## LPDDR2/LPDDR3 mode-register reads

For LPDDR3 and LPDDR2, mode-register reads (MRR) use the same DFI read
interface. The MC issues the MRR as a read command, asserts
`dfi_rddata_en` for the expected return length, and the PHY returns the
mode-register value on `dfi_rddata`. The `dfi_rddata_dnv` signal marks any
invalid bytes in the returned word.

**Source:** DFI Specification v3.1 sections 3.3, 4.5, Table 9, Table 10
