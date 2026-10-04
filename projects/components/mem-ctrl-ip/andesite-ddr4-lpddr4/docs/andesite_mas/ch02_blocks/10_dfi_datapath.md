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
**Status:** specified — no RTL exists (HAS v0.1 posture)

## Purpose

This page covers four modules because the DFI 4.0 delta touches them as one
layer. The command path widens for DDR4's extra pins; the read aligner and
write serializer grow DBI handling; and the DFI layer presents the new
control surface. The CDC (`dfi_cdc`) and `dfi_signal_pack` stay inherited and
dormant per the HAS, so they don't get their own MAS page.

## Parameters

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `DFI_DATA_WIDTH` | int | PHY-defined | TBD | DQ width at the DFI boundary | C1 |
| `DFI_DBI_WIDTH` | int | `DFI_DATA_WIDTH / 8` | TBD | per-byte DBI mask width | C2 |
| `NUM_RANKS` | int | 1..4 | 1 | rank count for chip-select fanout | C3 |
| `MEMTYPE` | string | "DDR4" / "LPDDR4" | TBD | selects command formatter path | C4 |

: Table 2.10.1: DFI datapath parameters

## Interface

The full pin-level inventory of the DFI 4.0 boundary lives in
`ch03_interfaces/01_dfi_v40.md`; this page describes the modules behind the
signals, not the signal list itself. The cross-reference is intentional —
that page owns the table so this one doesn't duplicate it.

| Signal group | Source block | DFI 4.0 clause suffix |
|---|---|---|
| Command pins (`dfi_act_n*`, `dfi_bg*`, `dfi_parity_in*`, etc.) | `dfi_cmd_path` / `dfi_cmd_formatter` | `§TBC(TASK-005)` |
| Read data + DBI | `dfi_rd_aligner` | `§TBC(TASK-005)` |
| Write data + DBI | `dfi_wr_serializer` | `§TBC(TASK-005)` |
| Training handshakes | `dfi_layer` routes to `wrlvl_ifc` / `rdlvl_ifc` / `ca_train_ifc` | `§TBC(TASK-005)` |

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
enabled per-byte from the MR5 read-DBI image: when enabled, the PHY inverts
bytes whose DBI bit is set, and the aligner reports the inversion mask to the
upper layers. The aligner does not interpret the data; it just aligns the
mask to the same beat as the data. Read DBI is MR5-programmed and independent
of write DBI.

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
CRC is explicitly out of scope this edition (HAS Ch 3.1; inert in MR4) — the
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

`dfi_layer` presents the DFI 4.0 control surface at pin level. The signal
inventory of HAS Ch 4's Table 4.1 lives here; `ch03_interfaces/01_dfi_v40.md`
owns the full pin table. The layer's job is fan-out and registration: it
routes training handshakes to the right interface block, it carries the
datapath FIFOs, and it exposes `dfi_init`, `dfi_error`, `dfi_error_info`, and
the low-power request pair exactly as scoria did. The gear-down handshake is
driven from `init_sequencer` through the layer, per DFI 4.0 `§TBC(TASK-005)`.

The CDC stage (`dfi_cdc`) and `dfi_signal_pack` are inherited/dormant per the
HAS. They are not re-derived for this page; if the dormant-pair condition in
HAS Ch 3.1 wakes them, their MAS pages will be added then.

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
  MR4 image and a new datapath specification.
- The full pin table belongs to `ch03_interfaces/01_dfi_v40.md`; this page
  intentionally cross-references rather than duplicates it.
