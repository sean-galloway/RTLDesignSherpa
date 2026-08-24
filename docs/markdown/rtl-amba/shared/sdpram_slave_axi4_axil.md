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

# SDPRAM Slave — AXI4 Write / AXIL Read

**Module:** `sdpram_slave_axi4_axil.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`sdpram_slave_axi4_axil` is the family permutation that exposes a **full AXI4 slave on the write side** (AW + W + B) and a **single-beat AXI4-Lite slave on the read side** (AR + R) in front of the shared `sdpram_core` backend. The write side instantiates `axi4_slave_wr` (full AXI4 with id / len / size / burst); the read side instantiates `axil4_slave_rd`, and the wrapper bridges the AXIL read FUB into the core's AXI-shaped read FUB using single-beat defaults.

### Key Features

- Full AXI4 write slave (burst, ID, size)
- Single-beat AXIL read slave (no burst / ID)
- AXIL read FUB bridged into the core with `arlen=0`, `arsize=$clog2(STRB_W)`, `arburst=INCR`, `arid=0`
- Shared `sdpram_core` backend
- Byte-enabled writes, single-cycle-latency reads
- Bulk-clear control and debug taps
- Sim-only WRAP-burst assertion on the AXI4 write side

Some harness topologies write bulk data over a high-throughput AXI4 burst port but only need simple, single-word AXIL reads for status polling or spot checks. This wrapper matches that shape: fast AXI4 in, lightweight AXIL out, over one shared BRAM.

The AXIL read side has no burst or ID fields, so the wrapper supplies the missing AXI-shaped fields at the single point where the AXIL read FUB meets the core, letting the core's burst tracker collapse to a single-beat read path.

**Use Cases:**
- AXI4 bulk-write memory model with an AXIL status/read-back port
- Descriptor RAM written by an AXI4 engine and polled over AXIL
- Any shared memory where the read side is a simple register-style AXIL access

**Key Benefit:** Full AXI4 write throughput paired with a minimal AXIL read port, with the single-beat adaptation isolated to one place in the wrapper.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AXI_ID_WIDTH | int | 8 | AXI4 write-side transaction-ID width |
| ADDR_WIDTH | int | 32 | Byte-address width (both sides) |
| DATA_WIDTH | int | 256 | Data-bus / BRAM word width (bits) |
| USER_WIDTH | int | 1 | AXI4 write-side USER width (carried by leaf, not preserved through BRAM) |
| MEM_DEPTH | int | 2048 | BRAM depth in words |
| SKID_DEPTH_AW | int | 2 | Write-address skid depth |
| SKID_DEPTH_W | int | 2 | Write-data skid depth |
| SKID_DEPTH_B | int | 2 | Write-response skid depth |
| SKID_DEPTH_AR | int | 2 | Read-address skid depth |
| SKID_DEPTH_R | int | 4 | Read-data skid depth |

**Derived localparams:** `STRB_W = DATA_WIDTH/8`, `FUB_ARSIZE_DEFAULT = $clog2(STRB_W)` (the `arsize` fed to the core for the single-beat read path).

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### AXI4 Slave Write (AW + W + B)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_awid | input | AXI_ID_WIDTH | Write-address ID |
| s_axi_awaddr | input | ADDR_WIDTH | Write burst base address |
| s_axi_awlen | input | 8 | Burst length minus 1 |
| s_axi_awsize | input | 3 | Beat size (log2 bytes) |
| s_axi_awburst | input | 2 | Burst type (INCR / FIXED / WRAP) |
| s_axi_awlock | input | 1 | Lock (ignored by core) |
| s_axi_awcache | input | 4 | Cache attributes (ignored by core) |
| s_axi_awprot | input | 3 | Protection attributes (ignored by core) |
| s_axi_awqos | input | 4 | QoS (ignored by core) |
| s_axi_awregion | input | 4 | Region (ignored by core) |
| s_axi_awuser | input | USER_WIDTH | User sideband (ignored by core) |
| s_axi_awvalid | input | 1 | Write-address valid |
| s_axi_awready | output | 1 | Write-address ready |
| s_axi_wdata | input | DATA_WIDTH | Write data |
| s_axi_wstrb | input | DATA_WIDTH/8 | Per-byte write strobe |
| s_axi_wlast | input | 1 | Write-data last beat |
| s_axi_wuser | input | USER_WIDTH | Write-data user sideband |
| s_axi_wvalid | input | 1 | Write-data valid |
| s_axi_wready | output | 1 | Write-data ready |
| s_axi_bid | output | AXI_ID_WIDTH | Write-response ID |
| s_axi_bresp | output | 2 | Write response |
| s_axi_buser | output | USER_WIDTH | Write-response user (hardwired to 0) |
| s_axi_bvalid | output | 1 | Write-response valid |
| s_axi_bready | input | 1 | Write-response ready |

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
| o_dbg_vr | output | 10 | External valid/ready snapshot `{rready,rvalid, arready,arvalid, bready,bvalid, wready,wvalid, awready,awvalid}` (AXIL R/AR on top, AXI4 B/W/AW below) |
| o_dbg_fub_vr | output | 10 | FUB-side valid/ready snapshot from the core |
| o_dbg_bram_wr | output | 1 | BRAM write-fire pulse |
| o_dbg_bram_rd | output | 1 | BRAM read-issue pulse |
| o_dbg_busy_wr | output | 1 | Write-side (AXI4) skid-leaf busy |
| o_dbg_busy_rd | output | 1 | Read-side (AXIL) skid-leaf busy |

---

## Functional Description

### Structure

Three instances: `axi4_slave_wr` (write), `axil4_slave_rd` (read), and `sdpram_core` (backend). The write leaf's FUB carries full AXI4 write fields into the core. The read leaf's AXIL FUB carries only address and data; the wrapper supplies the burst/ID fields the core expects.

### AXIL Read Bridge

The AXIL read FUB (`fub_axil_araddr / arvalid / arready` and `rdata / rresp / rvalid / rready`) is wired to the core's read FUB, and the AXI-shaped fields the core needs are tied off at that boundary:

- `fub_arid = '0`
- `fub_arlen = 8'h00` (single beat)
- `fub_arsize = 3'(FUB_ARSIZE_DEFAULT)` = `$clog2(STRB_W)` (one full data word per beat)
- `fub_arburst = 2'b01` (INCR)

The core's `fub_rid` and `fub_rlast` outputs go to `*_unused` nets — AXIL has no ID or last field. With `arlen = 0`, each AXIL read is a single-beat access into BRAM.

### Write Path and Tie-Offs

The write side passes full AXI4 fields straight through. The AXI4 qualifier fields the core ignores (`lock`, `cache`, `prot`, `qos`, `region`, `user`, `wlast`) terminate on `*_unused` nets. `s_axi_buser` is hardwired to zero since the core does not preserve user across the BRAM.

### Memory Behavior

Byte-enabled writes, single-cycle-latency reads, one outstanding burst per side, and the bulk-clear FSM all live in `sdpram_core` — see [`sdpram_core`](sdpram_core.md).

### WRAP Assertion

A `translate_off` block asserts on each accepted AW that `awburst` is not WRAP. Only the write side carries this assertion; the AXIL read side is inherently single-beat INCR.

---

## Usage Example

```systemverilog
sdpram_slave_axi4_axil #(
    .AXI_ID_WIDTH (8),
    .ADDR_WIDTH   (32),
    .DATA_WIDTH   (256),
    .MEM_DEPTH    (2048)
) u_mem (
    .aclk    (aclk),
    .aresetn (aresetn),

    // AXI4 burst write in
    .s_axi_awid    (eng_awid),
    .s_axi_awaddr  (eng_awaddr),
    .s_axi_awlen   (eng_awlen),
    .s_axi_awsize  (eng_awsize),
    .s_axi_awburst (eng_awburst),
    /* ...remaining AW/W/B... */
    .s_axi_bvalid  (eng_bvalid),
    .s_axi_bready  (eng_bready),

    // AXIL single-beat read-back
    .s_axil_araddr  (cpu_araddr),
    .s_axil_arprot  (cpu_arprot),
    .s_axil_arvalid (cpu_arvalid),
    .s_axil_arready (cpu_arready),
    .s_axil_rdata   (cpu_rdata),
    .s_axil_rresp   (cpu_rresp),
    .s_axil_rvalid  (cpu_rvalid),
    .s_axil_rready  (cpu_rready),

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

### Single-Beat Adaptation Lives in One Place

The only "fake AXI4" fields anywhere in this wrapper are the four read-side defaults (`arid / arlen / arsize / arburst`) fed to the core at the AXIL read FUB boundary. Everything else on the write side is genuine AXI4.

### One Backend, Four Wrappers

This wrapper shares `sdpram_core` with the three other permutations. Each protocol combination is a thin wrapper with its exact port shape; the memory kernel lives once in the core.

### Read Beat Size

`FUB_ARSIZE_DEFAULT = $clog2(STRB_W)` selects a full-data-word beat for each AXIL read, matching the BRAM word width. Sub-word AXIL reads are not modeled — a read returns the whole BRAM word at the addressed word index.

---

## Related Modules

### Used By
- Characterization harnesses with AXI4 bulk-write and AXIL read-back

### Uses
- **axi4_slave_wr.sv** — Write-side AXI4 skid leaf
- **axil4_slave_rd.sv** — Read-side AXIL skid leaf
- **sdpram_core.sv** — Shared SDPRAM backend

### See Also
- **sdpram_core.sv** — Protocol-agnostic backend ([doc](sdpram_core.md))
- **sdpram_slave_axi4_axi4.sv** — AXI4 write + AXI4 read variant
- **sdpram_slave_axil_axi4.sv** — AXIL write + AXI4 read variant
- **sdpram_slave_axil_axil.sv** — AXIL write + AXIL read variant

---

## References

### Source Code
- RTL: `rtl/amba/shared/sdpram_slave_axi4_axil.sv`
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
