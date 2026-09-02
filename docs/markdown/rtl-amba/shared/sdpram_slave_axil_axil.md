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

# SDPRAM Slave — AXIL Write / AXIL Read

**Module:** `sdpram_slave_axil_axil.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`sdpram_slave_axil_axil` is the all-AXI4-Lite permutation of the family: a **single-beat AXIL slave on the write side** (AW + W + B) and a **single-beat AXIL slave on the read side** (AR + R) in front of the shared `sdpram_core` backend. It directly instantiates the native `axil4_slave_wr` and `axil4_slave_rd` skid leaves and bridges their AXIL FUB outputs into the core's AXI-shaped FUB by supplying single-beat defaults on both sides. No AXI4-only fields appear anywhere on the wrapper's external boundary — which is exactly what you want from a register-style memory.

Sometimes you just need a lightweight memory shared between two AXIL agents — one writing, one reading — with no burst machinery exposed. This wrapper is exactly that: both sides are single-word AXIL, and the shared backend supplies the burst/ID scaffolding internally. Because AXIL carries no transaction ID, the wrapper carries a 1-bit zero ID through `sdpram_core` purely for type-width bookkeeping. The single-beat defaults are the only "fake" AXI4 fields in the design, and they live in exactly one place per side.

### Key Features

- Single-beat AXIL slave on both write and read sides
- Native `axil4_slave_wr` + `axil4_slave_rd` skid leaves
- Both FUBs bridged into the core with `len=0`, `size=$clog2(STRB_W)`, `burst=INCR`, `id=0`
- A 1-bit zero ID carried through the core for typing only (`CORE_ID_WIDTH = 1`)
- Shared `sdpram_core` backend
- Byte-enabled writes, single-cycle-latency reads
- Bulk-clear control and debug taps
- No WRAP assertion needed (both sides are inherently single-beat INCR)

**Use Cases:**
- Lightweight scratch / mailbox RAM shared between two AXIL agents
- Small semaphore RAM in a control-plane fabric
- Memory-ring backend for the AXIL/AXIL monitor-bus capture master-write port (pairs with `monbus_axil4_axil4_group`)
- Any AXIL-only shared-memory test scaffold

**Key Benefit:** A minimal AXIL-in / AXIL-out shared memory with all burst and clear complexity hidden in the shared core, and no spurious AXI4 fields on the external ports.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | Byte-address width (both sides) |
| DATA_WIDTH | int | 64 | Data-bus / BRAM word width (bits) |
| MEM_DEPTH | int | 1024 | BRAM depth in words |
| SKID_DEPTH_AW | int | 2 | Write-address skid depth |
| SKID_DEPTH_W | int | 2 | Write-data skid depth |
| SKID_DEPTH_B | int | 2 | Write-response skid depth |
| SKID_DEPTH_AR | int | 2 | Read-address skid depth |
| SKID_DEPTH_R | int | 4 | Read-data skid depth |
| `USE_WSTRB` | bit | `1'b1` | Honour WSTRB byte enables on writes. 0 = every write commits the full word. |

**Derived localparams:** `STRB_W = DATA_WIDTH/8`, `FUB_AWSIZE_DEFAULT = $clog2(STRB_W)` (the `awsize`/`arsize` fed to the core), `CORE_ID_WIDTH = 1` (a 1-bit zero ID carried through the core for typing only — AXIL has no transaction ID).

> Note: unlike the AXI4-bearing wrappers, this module has **no** `AXI_ID_WIDTH` or `USER_WIDTH` parameter, and its `DATA_WIDTH` / `MEM_DEPTH` defaults are smaller (64 / 1024), reflecting its lightweight role.

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### AXIL Slave Write (AW + W + B)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axil_awaddr | input | ADDR_WIDTH | Write address (single beat) |
| s_axil_awprot | input | 3 | Write protection attributes |
| s_axil_awvalid | input | 1 | Write-address valid |
| s_axil_awready | output | 1 | Write-address ready |
| s_axil_wdata | input | DATA_WIDTH | Write data |
| s_axil_wstrb | input | DATA_WIDTH/8 | Per-byte write strobe |
| s_axil_wvalid | input | 1 | Write-data valid |
| s_axil_wready | output | 1 | Write-data ready |
| s_axil_bresp | output | 2 | Write response |
| s_axil_bvalid | output | 1 | Write-response valid |
| s_axil_bready | input | 1 | Write-response ready |

### AXIL Slave Read (AR + R)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axil_araddr | input | ADDR_WIDTH | Read address (single beat) |
| s_axil_arprot | input | 3 | Read protection attributes |
| s_axil_arvalid | input | 1 | Read-address valid |
| s_axil_arready | output | 1 | Read-address ready |
| s_axil_rdata | output | DATA_WIDTH | Read data |
| s_axil_rresp | output | 2 | Read response |
| s_axil_rvalid | output | 1 | Read-data valid |
| s_axil_rready | input | 1 | Read-data ready |

### Bulk-Clear Control and Debug

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_cfg_start_clear | input | 1 | Request full-array clear (accepted when both sides idle) |
| o_cfg_done_clear | output | 1 | Clear-walk complete |
| o_dbg_vr | output | 10 | External valid/ready snapshot `{rready,rvalid, arready,arvalid, bready,bvalid, wready,wvalid, awready,awvalid}` |
| o_dbg_fub_vr | output | 10 | FUB-side valid/ready snapshot from the core |
| o_dbg_bram_wr | output | 1 | BRAM write-fire pulse |
| o_dbg_bram_rd | output | 1 | BRAM read-issue pulse |
| o_dbg_busy_wr | output | 1 | Write-side (AXIL) skid-leaf busy |
| o_dbg_busy_rd | output | 1 | Read-side (AXIL) skid-leaf busy |

---

## Functional Description

### Structure

Three instances: `axil4_slave_wr` (write), `axil4_slave_rd` (read), and `sdpram_core` (backend, parameterized with `AXI_ID_WIDTH = CORE_ID_WIDTH = 1`). Both AXIL FUBs carry only address and data; the wrapper supplies the burst/ID fields the core expects.

### Single-Beat Defaults on Both Sides

At each FUB-to-core boundary the wrapper ties the AXI-shaped fields the core needs:

**Write side:**
- `fub_awid = 1'b0`
- `fub_awlen = 8'h00`
- `fub_awsize = 3'(FUB_AWSIZE_DEFAULT)` = `$clog2(STRB_W)`
- `fub_awburst = 2'b01` (INCR)

**Read side:**
- `fub_arid = 1'b0`
- `fub_arlen = 8'h00`
- `fub_arsize = 3'(FUB_AWSIZE_DEFAULT)`
- `fub_arburst = 2'b01` (INCR)

The core's `fub_bid`, `fub_rid`, and `fub_rlast` outputs terminate on `*_unused` nets. With `len = 0` on both sides, every access is a single-beat BRAM access.

### Memory Behavior

Byte-enabled writes, single-cycle-latency reads, one outstanding access per side, and the bulk-clear FSM all live in `sdpram_core` — see [`sdpram_core`](sdpram_core.md).

### No WRAP Assertion

Neither side can express a burst, so there is no WRAP-burst assertion in this wrapper (the AXI4-bearing wrappers carry one because their burst-capable side could request WRAP).

---

## Timing Characteristics

| Skid parameter | Default depth |
|---|---|
| `SKID_DEPTH_AW` | 2 entries |
| `SKID_DEPTH_W` | 2 entries |
| `SKID_DEPTH_B` | 2 entries |
| `SKID_DEPTH_AR` | 2 entries |
| `SKID_DEPTH_R` | 4 entries |

Each channel traverses one `gaxi_skid_buffer`, which registers both `rd_valid`
and its storage. The **1-cycle input-to-output latency therefore applies on
every transfer, including the unstalled case** -- there is no combinational
bypass. Depth buys backpressure absorption, not throughput; full rate is
sustained once the pipeline is primed. Legal range is 2..8 inclusive, odd
values included.

Clocking: `aclk`, reset `aresetn` (active-low asynchronous).

No synthesis numbers are quoted here. Frequency and area depend on the target
device and the parameters you elaborate with; run your own build.

---

## Usage Examples
```systemverilog
sdpram_slave_axil_axil #(
    .ADDR_WIDTH (32),
    .DATA_WIDTH (64),
    .MEM_DEPTH  (1024)
) u_scratch (
    .aclk    (aclk),
    .aresetn (aresetn),

    // AXIL write port
    .s_axil_awaddr  (wr_awaddr),
    .s_axil_awprot  (wr_awprot),
    .s_axil_awvalid (wr_awvalid),
    .s_axil_awready (wr_awready),
    .s_axil_wdata   (wr_wdata),
    .s_axil_wstrb   (wr_wstrb),
    .s_axil_wvalid  (wr_wvalid),
    .s_axil_wready  (wr_wready),
    .s_axil_bresp   (wr_bresp),
    .s_axil_bvalid  (wr_bvalid),
    .s_axil_bready  (wr_bready),

    // AXIL read port
    .s_axil_araddr  (rd_araddr),
    .s_axil_arprot  (rd_arprot),
    .s_axil_arvalid (rd_arvalid),
    .s_axil_arready (rd_arready),
    .s_axil_rdata   (rd_rdata),
    .s_axil_rresp   (rd_rresp),
    .s_axil_rvalid  (rd_rvalid),
    .s_axil_rready  (rd_rready),

    .i_cfg_start_clear (clear_pulse),
    .o_cfg_done_clear  (clear_done),
    .o_dbg_vr          (dbg_vr),
    .o_dbg_fub_vr      (dbg_fub_vr),
    .o_dbg_bram_wr     (dbg_bram_wr),
    .o_dbg_bram_rd     (dbg_bram_rd),
    .o_dbg_busy_wr     (dbg_busy_wr),
    .o_dbg_busy_rd     (dbg_busy_rd)
);
```

---

## Design Notes

### The Only "Fake" Fields, In One Place Per Side

AXIL has no id / len / burst, so the wrapper feeds `sdpram_core` single-beat INCR defaults. These are the only synthetic AXI4 fields anywhere in the design, and they live in exactly one place per side — the smell of the legacy `generate`-if base is gone.

### Monitor-Bus Pairing

This wrapper is the canonical memory-ring backend for the AXIL/AXIL monitor-bus capture path: `monbus_axil4_axil4_group`'s master-write port streams records into an `sdpram_slave_axil_axil` acting as the dump ring.

### One Backend, Four Wrappers

This wrapper shares `sdpram_core` with the three other permutations. Each protocol combination is a thin wrapper with its exact port shape; the memory kernel lives once in the core.

---

## Related Modules

### Used By
- `monbus_axil4_axil4_group` master-write dump ring (memory-ring backend)
- Lightweight AXIL-only shared-memory test scaffolds

### Uses
- **axil4_slave_wr.sv** — Write-side AXIL skid leaf
- **axil4_slave_rd.sv** — Read-side AXIL skid leaf
- **sdpram_core.sv** — Shared SDPRAM backend

### See Also
- **sdpram_core.sv** — Protocol-agnostic backend ([doc](sdpram_core.md))
- **sdpram_slave_axi4_axi4.sv** — AXI4 write + AXI4 read variant
- **sdpram_slave_axi4_axil.sv** — AXI4 write + AXIL read variant
- **sdpram_slave_axil_axi4.sv** — AXIL write + AXI4 read variant
- **monbus_axil4_axil4_group.sv** — Monitor-bus delivery wrapper this RAM backs

---

## Testing

`val/amba/test_sdpram_slave_axil_axil.py` exercises this module. It collects 4 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_sdpram_slave_axil_axil.py -v
```

---

## References

### Source Code
- RTL: `rtl/amba/shared/sdpram_slave_axil_axil.sv`
- Backend: `rtl/amba/shared/sdpram_core.sv`

### Documentation
- Backend spec: `docs/markdown/rtl-amba/shared/sdpram_core.md`
- Architecture: `docs/markdown/rtl-amba/shared/README.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
