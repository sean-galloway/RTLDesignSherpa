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
- `sdpram_slave.sv` — common backend (BRAM glue + clear FSM + protocol skids)
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
dump ring** — `monbus_axil_group`'s `m_axil_*` master writes the
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

- **One common backend** (`sdpram_slave.sv`) with the BRAM port-A/B
  glue, bulk-clear FSM, burst tracker, and the two protocol-skid
  generate blocks (gated by `WR_PROTOCOL` / `RD_PROTOCOL` string
  parameters). The backend's port list is the AXI4 superset; in AXIL
  mode the unused fields are ignored on inputs / driven to 0 on
  outputs.
- **Four thin wrappers**, each with the right protocol-shaped port
  list, that instantiate the backend with the matching parameter
  setting and tie off any AXI4-only fields for an AXIL side.

| Wrapper | Wr ports | Rd ports |
|---|---|---|
| `sdpram_slave_axi4_axi4` | `s_axi_aw*/w*/b*` (full AXI4) | `s_axi_ar*/r*` (full AXI4) |
| `sdpram_slave_axi4_axil` | `s_axi_aw*/w*/b*` (full AXI4) | `s_axil_ar*/r*` (AXIL only) |
| `sdpram_slave_axil_axi4` | `s_axil_aw*/w*/b*` (AXIL only) | `s_axi_ar*/r*` (full AXI4) |
| `sdpram_slave_axil_axil` | `s_axil_aw*/w*/b*` (AXIL only) | `s_axil_ar*/r*` (AXIL only) |

Callers pick the wrapper module name matching their fabric. The bare
`sdpram_slave` remains directly callable for unusual configs (or for
the existing `test_sdpram_slave.py` regression which exercises both
sides independently via the parameter knobs).

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
  is rejected by a SIMULATION-only `$error` and treated as `INCR` in
  synth (the BRAM glue advances linearly).
- **AXIL mode** is single-beat by construction — the AXIL skid ties the
  fub-side `awlen`/`arlen` to 0, so the burst-aware backend produces
  exactly one beat per AW/AR. Multi-beat transactions are not
  expressible in AXIL anyway.

---

## Bulk Clear

All wrappers expose:

- `i_cfg_start_clear` (input) — pulse high to start a memory-wide clear.
- `o_cfg_done_clear` (output) — pulses high when the clear FSM finishes.

The clear FSM owns BRAM port A while it walks the whole memory writing
zeros. It waits for both sides idle before claiming the port, so an
in-flight write or read completes cleanly before the clear begins.

---

## Debug / Observation Outputs

Common to all wrappers (and the backend):

| Output | Width | Meaning |
|---|---|---|
| `o_dbg_vr` | 10 | External `{aw,w,b,ar,r}_{valid,ready}` (AW = [9:8], W = [7:6], B = [5:4], AR = [3:2], R = [1:0]) |
| `o_dbg_fub_vr` | 10 | Fub-side (post-skid) valid/ready for the same five channels |
| `o_dbg_bram_wr` | 1 | One-cycle pulse on BRAM port-A write fire |
| `o_dbg_bram_rd` | 1 | One-cycle pulse on BRAM port-B read fire |
| `o_dbg_busy_wr` | 1 | Write-side skid busy |
| `o_dbg_busy_rd` | 1 | Read-side skid busy |

---

## Use in the Monitor System

The `sdpram_slave_axil_axil` wrapper is the canonical SRAM-ring backend
for the [`monbus_axil_group`](monbus_axil_group.md) master writer —
both sides AXIL, so no AXI4-only fields anywhere on the harness wiring.
For details on the slot stream landing in the ring, see
[`monbus_compressor.md`](monbus_compressor.md) (the compressed case)
and the raw-record beat layout described in
[`monbus_axil_group.md`](monbus_axil_group.md).

---

## Test

`val/amba/test_sdpram_slave.py` exercises the bare `sdpram_slave`
backend across all four `(WR_PROTOCOL, RD_PROTOCOL)` combinations via
`@pytest.mark.parametrize`. The wrappers are thin pass-throughs so the
backend regression is the load-bearing one. Sub-tests cover:

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
| [`monbus_axil_group`](monbus_axil_group.md) | Most common consumer (memory-dump ring) |
| [`monbus_compressor`](monbus_compressor.md) | Source of the compressed slot stream landing in the ring |
| `axi4_slave_wr` / `axi4_slave_rd` | AXI4-side skids instantiated by the backend |
| `axil4_slave_wr` / `axil4_slave_rd` | AXIL-side skids instantiated by the backend |
