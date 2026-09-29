# 2.7 AXIL Wide-Alignment Converters

`axil_to_axi4_wide_align_wr` and `axil_to_axi4_wide_align_rd` are drop-in
replacements for `axi4_dwidth_converter_wr` / `_rd` for the one case those
converters get wrong: a slave-side master that is effectively AXI4-Lite --
every transfer single-beat, narrow, at a sub-row address.

## 2.7.1 Why They Exist

The generic converters place data by **beat counter**. `axi_data_upsize`
aggregates N narrow beats into one wide beat in arrival order, and
`axi_data_dnsize` emits narrow beats the same way. That is correct for a true
multi-beat narrow burst.

An AXI4-Lite master never issues one. Every transfer is a single beat with
`awlen=0`, and AXI4 requires the data for a narrow single-beat transfer to sit
in the byte lanes selected by the address, not in lane 0. With the generic
upsize, every such write lands at lane 0 whatever `awaddr` says, and every such
read is taken from lane 0 rather than the requested slot.

These two modules place the beat at byte offset `(addr & wide_mask) * 8`
instead, which is what the specification requires.

The path this matters on is the bridge generator's: it wraps an AXI4-Lite
master with `axi4_slave_wr`, which presents `fub_axi_*` with
`awlen=0`, a narrow `awsize` and `awburst=01`. That is exactly the shape the
generic upsize mishandles.

## 2.7.2 Parameters

Both modules take the same set. Defaults differ from the generic converters
because the intended direction is narrow master to wide slave.

| Parameter | Default | Description |
|-----------|---------|-------------|
| `S_AXI_DATA_WIDTH` | 32 | Slave-side (narrow, AXIL-like) data width |
| `M_AXI_DATA_WIDTH` | 256 | Master-side (wide) data width |
| `AXI_ID_WIDTH` | 8 | ID width |
| `AXI_ADDR_WIDTH` | 32 | Address width |
| `AXI_USER_WIDTH` | 1 | User-signal width |
| `SKID_DEPTH_AW` | 2 | **Accepted for API parity; unused.** Tied into the module's `_unused` sink |
| `SKID_DEPTH_W` | 2 | Likewise unused (write module) |
| `SKID_DEPTH_B` | 2 | Likewise unused (write module) |
| `SKID_DEPTH_AR` | 2 | Likewise unused (read module) |
| `SKID_DEPTH_R` | 4 | Likewise unused (read module) |

: Wide-Alignment Converter Parameters

The `SKID_DEPTH_*` parameters exist so these modules can be swapped in for the
generic converters without editing the instantiation. They buffer nothing --
the RTL lists them explicitly in a `verilator lint_off UNUSED` sink rather than
leaving the non-use implicit.

Several AW/AR sideband inputs are declared and deliberately unused for the same
reason -- `awlen`, `awsize`, `awburst`, `awlock`, `awqos`, `awregion` and
`wlast` on the write side. A single-beat AXIL transfer carries no useful burst
description, so the module ignores it rather than trusting it.
