<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# DFI Datapath (`andesite_dfi_cmd_path`, `andesite_dfi_rd_aligner`, `andesite_dfi_wr_serializer`, `andesite_dfi_layer`)

**Module:** `andesite_dfi_cmd_path`, `andesite_dfi_rd_aligner`, `andesite_dfi_wr_serializer`, `andesite_dfi_layer`
**Location:** `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/`
**Category:** DFI 4.0 boundary / datapath
**Parent:** `andesite_top` / PHY interface
**Status:** implemented (TASK-016 t6)

## Purpose

This page covers four modules because the DFI 4.0 delta touches them as one
layer. The command path widens for DDR4's extra pins; the read aligner and
write serializer grow DBI handling; and the DFI layer presents the new
control surface. The CDC (`dfi_cdc`) and `dfi_signal_pack` stay inherited and
dormant per the HAS, so they don't get their own MAS page.

## Parameters

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `NUM_RANKS` | int | 1..4 | 1 | rank count for chip-select fanout | C3 |
| `NUM_BANKS` | int | — | 8 | bank count | — |
| `NUM_BG` | int | — | 4 | bank-group count | — |
| `ROW_WIDTH` | int | — | 14 | row address width | — |
| `COL_WIDTH` | int | — | 10 | column address width | — |
| `ADDR_WIDTH` | int | — | 18 | DFI address bus width | — |
| `DFI_RATE` | int | 1,2,4 | 2 | DFI frequency ratio | — |
| `DRAM_BEAT_WIDTH` | int | PHY-defined | 64 | DRAM beat DQ width | C1 |
| `DFI_DATA_WIDTH` | int | `DRAM_BEAT_WIDTH * DFI_RATE` | 128 | DQ width at the DFI boundary | C1 |
| `CMD_FIFO_DEPTH` | int | power of 2 | 8 | command CDC FIFO depth | — |
| `WD_FIFO_DEPTH` | int | power of 2 | 16 | write-data CDC FIFO depth | — |
| `RD_FIFO_DEPTH` | int | power of 2 | 32 | read-data CDC FIFO depth | — |
| `RD_MAX_OUTSTANDING` | int | — | 16 | read-aligner outstanding-read depth | — |
| `RD_EN_CYC` | int | — | 4 | `dfi_rddata_en` window width (DFI cycles) | — |
| `BL_WORDS` | int | — | `RD_EN_CYC` | DFI words captured per read | — |

: Table 2.10.1: DFI datapath parameters

## Interface

The full pin-level inventory of the DFI 4.0 boundary lives in
`ch03_interfaces/01_dfi40_pins.md`; this page describes the modules behind the
signals, not the signal list itself. The cross-reference is intentional —
that page owns the table so this one doesn't duplicate it.

| Signal group | Source block | DFI 4.0 clause suffix |
|---|---|---|
| Command pins (`dfi_act_n*`, `dfi_bg*`, `dfi_parity_in*`, etc.) | `dfi_cmd_path` / `dfi_cmd_formatter` | `§TBC(TASK-005)` |
| Read data + DBI | `dfi_rd_aligner` | `§TBC(TASK-005)` |
| Write data + DBI | `dfi_wr_serializer` | `§TBC(TASK-005)` |
| Training handshakes | Owned by `andesite_training_layer`, not routed here | `§TBC(TASK-005)` |

: Table 2.10.2: DFI datapath signal groups

## Microarchitecture internals

### `dfi_cmd_path`: widened command bus

`dfi_cmd_path` inherits scoria's registered pipeline and widens the command
word to carry the DDR4 additions:

```text
inherited: dfi_cs_n, dfi_ras_n, dfi_cas_n, dfi_we_n, dfi_address, dfi_bank
added:     dfi_act_n, dfi_bg[1:0], dfi_parity_in
```

The added pins are driven from `dfi_cmd_formatter`: `dfi_act_n` is the fifth
command pin, `dfi_bg[1:0]` carry the bank-group decode from `addr_mapper`, and
`dfi_parity_in` carries the CA parity bit. For LPDDR4 these pins leave over
the formatter's LPDDR4 CA submodule instead; `dfi_cmd_path` simply passes the
wider container through.

### `dfi_rd_aligner`: DBI on the read path

The read aligner presents `dfi_rddata_dbi` alongside the read data. DBI is
enabled per-byte from the MR5 read-DBI image: when enabled, the DRAM inverts
bytes whose DBI bit is set at send time, and the receiver (PHY/controller)
restores them. The aligner reports the inversion mask to the upper layers
aligned to the same beat as the data. Read DBI is MR5-programmed and
independent of write DBI.

```text
per-byte behavior:
  if MR5[read DBI enable] == 1:
     dfi_rddata_dbi[n] reports whether byte n was inverted
  else:
     dfi_rddata_dbi[n] is zero / don't-care
```

### `dfi_wr_serializer`: DBI on the write path

The write serializer applies `dfi_wrdata_dbi` to the write data before it
reaches the PHY. When MR5 write-DBI is enabled, each byte whose DBI bit is set
is inverted on the way out; when disabled, the DBI vector is ignored. Write
CRC is explicitly out of scope this edition (HAS Ch 3.1; inert in MR2) — the
serializer carries no CRC lane, no CRC state machine, and no stub. It is named
here so nobody wires a placeholder.

```text
per-byte behavior:
  if MR5[write DBI enable] == 1:
     byte_out[n] = dfi_wrdata[n] ^ dfi_wrdata_dbi[n]
  else:
     byte_out[n] = dfi_wrdata[n]
```

### `dfi_layer`: the 4.0 control surface

`andesite_dfi_layer` is a structural assembly in `rtl/macro/`:

```text
andesite_dfi_cdc        : ctl_clk <-> dfi_clk async FIFOs (cmd, wrdata, rddata)
andesite_dfi_cmd_path   : widened command word -> DFI 4.0 pin vector + fire strobes
andesite_dfi_wr_serializer : drive dfi_wrdata/en/mask at t_phy_wrlat
andesite_dfi_rd_aligner    : capture dfi_rddata and push into the read CDC FIFO
```

`andesite_dfi_signal_pack` stays dormant per the HAS and is not instantiated.
Training pins (write-leveling, read-leveling, CA/WDQ training) live on
`andesite_training_layer`, which owns the DFI training pins and their PHY
clock-domain crossing — they are deliberately not carried through the DFI
datapath layer.

The command word is the widened scheduler container
`{ap,col,row,bg,bank,rank,op}`; the CDC command FIFO width is parameterized so
the layer passes the full word without narrowing.

The single-rank design point drives the DFI v3.1 CS-qualified data lanes
`dfi_wrdata_cs_o` and `dfi_rddata_cs_o` to constant zero, matching scoria's
v3.1 precedent. Only `dfi_cs_o` (from `dfi_cmd_path`) is active.

`dfi_cke_o` is the registered `cke_i` input, the real CKE pin generated by the
P1 init sequencer. The P1 formatter's own `dfi_cke` output is a DDR4
placeholder and is intentionally not forwarded.

`dfi_init_start_o` is the CDC's registered copy of `init_busy_i`. There is no
`dfi_error` / `dfi_error_info` at this layer: scoria never had them here, and
they are not added in andesite (the MAS claim is reconciled here).

### LPDDR4 delta

The datapath structure is memory-type neutral. Only the command pin mapping
changes: for LPDDR4, the command word leaves through the formatter's 6-bit
CA submodule as a double-data-rate CA bus, two cycles per command. The read
and write data paths are unchanged. LPDDR4's two x16 channels are a build
parameter the datapath doesn't care about — per-channel state lives in
`ca_train_ifc` and the refresh path, not here.

## FSM policy

There are no FSMs in this layer. `dfi_cmd_path`, `dfi_rd_aligner`, and
`dfi_wr_serializer` are registered pipelines and muxing, inherited shape. The
DBI enable qualification is combinational on the MR5 image. `dfi_layer` itself
is a routing and registration shell; the only "state" is the CDC FIFOs in the
inherited `dfi_cdc`, and those keep scoria's elastic-buffer policy.

## Timing

- The command path is a registered pipeline; latency is one DFI clock per
  stage, matching scoria's verified shape.
- The read aligner and write serializer add no FSM latency beyond the
  inherited pipeline; DBI inversion is combinational on the MR5 image.
- Gear-down entry timing is owned by `init_sequencer`; `dfi_layer` only
  presents the handshake pins, per DFI 4.0 `§TBC(TASK-005)`.
- All DFI 4.0 clause references are suffixed `§TBC(TASK-005)` because the
  specification is acquired and studied under andesite TASK-005.

## Notes

- The DFI 4.0 `_pN` phase notation is a generalization, not a new signal. The
  1:4 frequency ratio remains a defined mode of the newer revision, per DFI
  4.0 `§TBC(TASK-005)`.
- Write CRC is out of scope this edition. The datapath has no CRC lane and no
  stub; if the condition in HAS Ch 3.1 changes, the change starts with the
  MR2 image and a new datapath specification.
- The full pin table belongs to `ch03_interfaces/01_dfi40_pins.md`; this page
  intentionally cross-references rather than duplicates it.
