# 3.8 Width-plus-Protocol Chains

A chain is a FUB-level module that wires one width converter directly to one
protocol converter. Neither chain adds logic of its own: they exist because
that pairing is what a real bridge instantiates, and because the bugs worth
catching live at the seam between the two, not inside either one.

Both are downsizing chains -- a wide AXI4 master talking to a narrow
peripheral -- and both were built to reproduce the back-to-back page-boundary
class of defect at FUB level, where it can be driven directly, instead of only
at the bridge level where it was first seen.

## 3.8.1 axi4_dwidth_to_axil4_wr_chain

Write path. The slave port is wide AXI4 (`S_AXI_DATA_WIDTH`); the master port
is AXI4-Lite at `M_AXIL_DATA_WIDTH`.

| Stage | Module | What it does |
|-------|--------|--------------|
| 1 | `axi4_dwidth_converter_wr` | Downsizes the W beats and rewrites `awlen`/`awsize`, so the next stage sees a narrow AXI4 burst of `M_AXIL_DATA_WIDTH`-wide beats |
| 2 | `axi4_to_axil4_wr` | Decomposes that narrow burst into single-beat AXI4-Lite writes |

| Parameter | Default | Description |
|-----------|---------|-------------|
| `S_AXI_DATA_WIDTH` | 64 | Slave-side (wide) AXI4 data width |
| `M_AXIL_DATA_WIDTH` | 32 | Master-side AXI4-Lite data width; the width beats are downsized to |
| `AXI_ID_WIDTH` | 8 | Slave-side ID width |
| `AXI_ADDR_WIDTH` | 32 | Address width, both sides |
| `AXI_USER_WIDTH` | 1 | User-signal width |

: axi4_dwidth_to_axil4_wr_chain Parameters

Ports are the slave-side AXI4 write channels and the master-side AXI4-Lite
write channels, unchanged from the two modules it wraps -- see
[AXI4 to AXI4-Lite](02_axi4_to_axil4.md) for the AXI4-Lite side and the width
block chapters for the AXI4 side.

## 3.8.2 axi4_dwidth_to_apb4_chain

Read path only. **The write channels on the slave port are tied off inside the
chain** -- this is a read chain, not a general bridge.

| Stage | Module | What it does |
|-------|--------|--------------|
| 1 | `axi4_dwidth_converter_rd` | Rewrites `arlen`/`arsize` down to `APB_DATA_WIDTH`-wide narrow beats, and upsizes the returning R beats back to `S_AXI_DATA_WIDTH` |
| 2 | `axi4_to_apb4_shim` | Decomposes the narrow burst into single-beat APB reads |

| Parameter | Default | Description |
|-----------|---------|-------------|
| `S_AXI_DATA_WIDTH` | 64 | Slave-side (wide) AXI4 data width |
| `APB_DATA_WIDTH` | 32 | APB data width on the master side |
| `AXI_ID_WIDTH` | 8 | Slave-side ID width |
| `AXI_ADDR_WIDTH` | 32 | AXI address width |
| `APB_ADDR_WIDTH` | 32 | APB address width |
| `AXI_USER_WIDTH` | 1 | User-signal width |
| `USE_JOHNSON` | 0 | CDC-FIFO pointer encoding forwarded to the shim: 0 = Gray (power-of-2 depth only), 1 = Johnson |

: axi4_dwidth_to_apb4_chain Parameters

The direction is worth stating plainly, because the two readings of "downsize"
point opposite ways. The wide master issues a wide-beat AR burst; the read
converter rewrites it into narrow `APB_DATA_WIDTH` beats for the shim; the R
data coming back is reassembled into wide beats for the master.
