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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Simple Dual-Port BRAM Slave Family

**Modules:**
- `sdpram_core.sv` — common backend (BRAM glue + clear FSM); the protocol skids live in the WRAPPERS, not the backend
- `sdpram_slave_axi4_axi4.sv` — wrapper: AXI4 write, AXI4 read
- `sdpram_slave_axi4_axil.sv` — wrapper: AXI4 write, AXIL read
- `sdpram_slave_axil_axi4.sv` — wrapper: AXIL write, AXI4 read
- `sdpram_slave_axil_axil.sv` — wrapper: AXIL write, AXIL read

**Location:** `rtl/amba/shared/`
**Category:** Memory / BRAM Slave
**Status:** Production Ready

---

## Overview

The `sdpram_slave` family provides a BRAM-backed simple-dual-port slave
with **independent protocol choice on each side** (write, read). It
unifies what used to be two separate modules (`axi4_sdpram_slave` +
`axil_sdpram_slave`) into a single common backend plus four protocol-
specific wrappers that expose the exact port shape for their
configuration.

The most common deployment in this repo is the **monitor bus memory
dump ring** — `monbus_axil_axil_group`'s `m_axil_*` master writes the
compressed (or raw) trace into a `sdpram_slave_axil_axil`, and the host
CPU reads it back through the same slave's read port. Wide AXI4
descriptor RAMs (e.g. `stream_char_harness::u_desc_ram`, 256-bit data,
8-bit AXI ID) instantiate `sdpram_slave_axi4_axi4`.

---

## Why four wrappers + a backend?

SystemVerilog cannot conditionally include or exclude ports from a
single module's port list. The port list is a static syntactic
construct, fixed at module declaration. So to give each protocol
combination an exact port shape — no spurious AXI4-only fields for the
caller to tie off — the family is split:

- **One common backend** (`sdpram_core.sv`) with the BRAM port-A/B
  glue, bulk-clear FSM and burst tracker. Its whole parameter list is
  `AXI_ID_WIDTH, ADDR_WIDTH, DATA_WIDTH, MEM_DEPTH` -- there is no
  string-switch generate plumbing; its header says the wrappers "drop
  straight on top".
- **Four wrappers**, each with the right protocol-shaped port list,
  that instantiate the matching protocol skids (`axi4_slave_wr`,
  `axil4_slave_rd`, ...) AND the core -- the protocol skids live in the
  wrappers, not the backend.

| Wrapper | Wr ports | Rd ports |
|---|---|---|
| `sdpram_slave_axi4_axi4` | `s_axi_aw*/w*/b*` (full AXI4) | `s_axi_ar*/r*` (full AXI4) |
| `sdpram_slave_axi4_axil` | `s_axi_aw*/w*/b*` (full AXI4) | `s_axil_ar*/r*` (AXIL only) |
| `sdpram_slave_axil_axi4` | `s_axil_aw*/w*/b*` (AXIL only) | `s_axi_ar*/r*` (full AXI4) |
| `sdpram_slave_axil_axil` | `s_axil_aw*/w*/b*` (AXIL only) | `s_axil_ar*/r*` (AXIL only) |

Callers pick the wrapper module name matching their fabric. (An older
`sdpram_slave` backend with `WR_PROTOCOL`/`RD_PROTOCOL` string
parameters no longer exists -- this family replaced it.)

---

## Common Parameters

All wrappers expose the same scaling knobs as the backend:

| Parameter | Default | Notes |
|---|---|---|
| `ADDR_WIDTH` | 32 | Address width. |
| `DATA_WIDTH` | 256 (`axi4_*`) / 64 (`axil_axil`) | Data-bus width. |
| `MEM_DEPTH` | 2048 (`axi4_*`) / 1024 (`axil_axil`) | BRAM word count. |
| `AXI_ID_WIDTH` | 8 | Present only when at least one side is AXI4. |
| `USER_WIDTH` | 1 | Present only when at least one side is AXI4. |
| `SKID_DEPTH_AW/W/B/AR/R` | 2/2/2/2/4 | Skid buffer depths for each channel. |

---

## Burst Support

- **AXI4 mode** supports `INCR` (`awburst/arburst = 2'b01`) and `FIXED`
  (`2'b00`) of any length up to AXI4's 256-beat maximum. `WRAP` (`2'b10`)
  raises a SIMULATION-only `$warning` ("not yet validated") and the burst
  PROCEEDS -- and the burst proceeds with wrap-shaped addressing via `axi_gen_addr`
  (fed the latched burst length since the 2026-08-13 mask fix). Still
  UNVALIDATED -- no test drives WRAP through the BRAM glue.
- **AXIL mode** is single-beat by construction — the AXIL skid ties the
  fub-side `awlen`/`arlen` to 0, so the burst-aware backend produces
  exactly one beat per AW/AR. Multi-beat transactions are not
  expressible in AXIL anyway.

---

## Bulk Clear

All wrappers expose:

- `i_cfg_start_clear` (input) — pulse high to start a memory-wide clear.
- `o_cfg_done_clear` (output) — a STICKY LEVEL: set when the clear FSM
  finishes and held high until the next clear is accepted. Do not
  edge-count it as a pulse.

The clear FSM owns BRAM port A while it walks the whole memory writing
zeros. It waits for both sides idle before claiming the port, so an
in-flight write or read completes cleanly before the clear begins.

---

## Debug / Observation Outputs

Common to all wrappers (`o_dbg_fub_vr`/`o_dbg_bram_*` come from
`sdpram_core`; `o_dbg_vr` and the busy flags come from the wrapper-level
skids):

| Output | Width | Meaning |
|---|---|---|
| `o_dbg_vr` | 10 | External `{rready,rvalid, arready,arvalid, bready,bvalid, wready,wvalid, awready,awvalid}` — R = [9:8], AR = [7:6], B = [5:4], W = [3:2], AW = [1:0] |
| `o_dbg_fub_vr` | 10 | Fub-side (post-skid) valid/ready for the same five channels |
| `o_dbg_bram_wr` | 1 | One-cycle pulse on BRAM port-A write fire |
| `o_dbg_bram_rd` | 1 | One-cycle pulse on BRAM port-B read fire |
| `o_dbg_busy_wr` | 1 | Write-side skid busy |
| `o_dbg_busy_rd` | 1 | Read-side skid busy |

---

## Use in the Monitor System

The `sdpram_slave_axil_axil` wrapper is the canonical SRAM-ring backend
for the [`monbus_axil_axil_group`](../monitor/monbus_group.md) master writer —
both sides AXIL, so no AXI4-only fields anywhere on the harness wiring.
For details on the slot stream landing in the ring, see
[`monbus_compressor.md`](../monitor/monbus_compressor.md) (the compressed case)
and the raw-record beat layout described in
[`monbus_group.md`](../monitor/monbus_group.md).

---

## Test

`val/amba/test_sdpram_slave.py` builds `sdpram_slave_axi4_axi4` (the
full-AXI4 wrapper, which contains `sdpram_core`) and drives the four
protocol-combination stimulus shapes against it via
`@pytest.mark.parametrize`. The other three wrappers are thin
port-shape variants over the same core. Sub-tests cover:

1. Single-beat AW/W/B + AR/R round-trip (all 4 combos)
2. AXI4 INCR burst write + read (AXI4-only)
3. AXI4 FIXED burst write (last beat wins) + read (AXI4-only)
4. Random fill + readback (all 4 combos)

```bash
pytest val/amba/test_sdpram_slave.py -v
```

---

## Migration

If you have an old caller that instantiates the bare `sdpram_slave`:

```systemverilog
// Old: full AXI4-shape ports, tie off AXI4-only for AXIL side
sdpram_slave #(
    .WR_PROTOCOL ("AXIL"),
    .RD_PROTOCOL ("AXIL"),
    .AXI_ID_WIDTH (1),  // unused
    ...
) u_dump (
    .s_axi_awid    (1'b0),       // ← unsightly tie-off
    .s_axi_awaddr  (axil_awaddr),
    .s_axi_awlen   (8'h00),      // ← unsightly tie-off
    .s_axi_awsize  (3'h0),       // ← unsightly tie-off
    ...
);
```

After migrating to the matching wrapper:

```systemverilog
// New: AXIL-only ports, no tie-offs needed
sdpram_slave_axil_axil #(
    .ADDR_WIDTH (32),
    .DATA_WIDTH (64),
    .MEM_DEPTH  (1024)
) u_dump (
    .s_axil_awaddr  (axil_awaddr),
    .s_axil_awprot  (axil_awprot),
    .s_axil_awvalid (axil_awvalid),
    .s_axil_awready (axil_awready),
    ...
);
```

The backend is unchanged so functional behavior is identical — only
the port list shape and signal names differ.

---

## Related Modules

| Module | Role |
|---|---|
| [`monbus_axil_axil_group`](../monitor/monbus_group.md) | Most common consumer (memory-dump ring) |
| [`monbus_compressor`](../monitor/monbus_compressor.md) | Source of the compressed slot stream landing in the ring |
| `axi4_slave_wr` / `axi4_slave_rd` | AXI4-side skids instantiated by the WRAPPERS |
| `axil4_slave_wr` / `axil4_slave_rd` | AXIL-side skids instantiated by the WRAPPERS |
