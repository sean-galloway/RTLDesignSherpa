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

# SDPRAM Slave — AXI4 Write / AXI4 Read

**Module:** `sdpram_slave_axi4_axi4.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`sdpram_slave_axi4_axi4` is one of four protocol-pair wrappers that place a Simple Dual-Port RAM behind two independent AMBA slave interfaces — a write-side slave and a read-side slave. This variant exposes a **full AXI4 slave** on both the write side (AW + W + B) and the read side (AR + R). It directly instantiates the native `axi4_slave_wr` and `axi4_slave_rd` skid leaf modules and pipes their FUB-side outputs into the shared `sdpram_core` backend.

### Key Features

- Full AXI4 slave on both write and read sides (burst, ID, size)
- Native `axi4_slave_wr` + `axi4_slave_rd` skid leaves (no protocol emulation)
- Shared `sdpram_core` backend — one BRAM, one clear FSM, one burst tracker set
- Byte-enabled writes, single-cycle-latency reads
- Bulk-clear control input and done flag
- Full complement of debug taps (external and FUB valid/ready, BRAM fire pulses, leaf busy)
- Sim-only assertion flagging unvalidated WRAP bursts

Characterization harnesses need a synthesizable memory that a device-under-test can read and write over AXI4 while a separate host or checker uses the other port. Splitting the write side and read side into two independent AXI4 slaves lets one agent stream data in while another drains it out, with the BRAM as the shared medium.

This is the pure-AXI4 permutation of the family. When both the producer and consumer speak full AXI4 (bursts, IDs), this wrapper avoids any width- or burst-adaptation on either side.

**Use Cases:**
- Memory model behind an AXI4 DUT in a characterization harness
- Descriptor RAM with an AXI4 host-write port and an AXI4 engine-read port
- Semaphore / scratch RAM shared between two AXI4 masters
- General synthesizable dual-port memory with a fast bulk clear

**Key Benefit:** Full AXI4 on both sides with zero fake fields — the burst/ID information flows straight through the skid leaves into the shared core.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AXI_ID_WIDTH | int | 8 | AXI transaction-ID width on both sides |
| ADDR_WIDTH | int | 32 | Byte-address width |
| DATA_WIDTH | int | 256 | Data-bus / BRAM word width (bits) |
| USER_WIDTH | int | 1 | AXI USER-signal width (carried by leaves, not preserved through BRAM) |
| MEM_DEPTH | int | 2048 | BRAM depth in words |
| SKID_DEPTH_AW | int | 2 | Write-address skid depth |
| SKID_DEPTH_W | int | 2 | Write-data skid depth |
| SKID_DEPTH_B | int | 2 | Write-response skid depth |
| SKID_DEPTH_AR | int | 2 | Read-address skid depth |
| SKID_DEPTH_R | int | 4 | Read-data skid depth |

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
| s_axi_awlock | input | 1 | Lock (carried by leaf, ignored by core) |
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

### AXI4 Slave Read (AR + R)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_arid | input | AXI_ID_WIDTH | Read-address ID |
| s_axi_araddr | input | ADDR_WIDTH | Read burst base address |
| s_axi_arlen | input | 8 | Burst length minus 1 |
| s_axi_arsize | input | 3 | Beat size (log2 bytes) |
| s_axi_arburst | input | 2 | Burst type |
| s_axi_arlock | input | 1 | Lock (ignored by core) |
| s_axi_arcache | input | 4 | Cache attributes (ignored by core) |
| s_axi_arprot | input | 3 | Protection attributes (ignored by core) |
| s_axi_arqos | input | 4 | QoS (ignored by core) |
| s_axi_arregion | input | 4 | Region (ignored by core) |
| s_axi_aruser | input | USER_WIDTH | User sideband (ignored by core) |
| s_axi_arvalid | input | 1 | Read-address valid |
| s_axi_arready | output | 1 | Read-address ready |
| s_axi_rid | output | AXI_ID_WIDTH | Read-data ID |
| s_axi_rdata | output | DATA_WIDTH | Read data |
| s_axi_rresp | output | 2 | Read response |
| s_axi_rlast | output | 1 | Read-data last beat |
| s_axi_ruser | output | USER_WIDTH | Read-data user (hardwired to 0) |
| s_axi_rvalid | output | 1 | Read-data valid |
| s_axi_rready | input | 1 | Read-data ready |

### Bulk-Clear Control and Debug

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_cfg_start_clear | input | 1 | Request full-array clear (accepted when both sides idle) |
| o_cfg_done_clear | output | 1 | Clear-walk complete |
| o_dbg_vr | output | 10 | External valid/ready snapshot `{rready,rvalid, arready,arvalid, bready,bvalid, wready,wvalid, awready,awvalid}` |
| o_dbg_fub_vr | output | 10 | FUB-side valid/ready snapshot from the core |
| o_dbg_bram_wr | output | 1 | BRAM write-fire pulse |
| o_dbg_bram_rd | output | 1 | BRAM read-issue pulse |
| o_dbg_busy_wr | output | 1 | Write-side skid-leaf busy |
| o_dbg_busy_rd | output | 1 | Read-side skid-leaf busy |

---

## Functional Description

### Structure

The wrapper is three instances and a little glue:

1. `axi4_slave_wr` accepts the external AXI4 write channels and presents a FUB-shaped write interface.
2. `axi4_slave_rd` accepts the external AXI4 read channels and presents a FUB-shaped read interface.
3. `sdpram_core` consumes both FUBs, owns the BRAM, the burst trackers, and the clear FSM.

### Field Pass-Through and Tie-Offs

Because both sides are full AXI4, the real `awid / awlen / awsize / awburst` (and the AR equivalents) flow straight through the leaves into the core. The AXI4-only qualifier fields the core does not consume — `lock`, `cache`, `prot`, `qos`, `region`, `user`, and `wlast` — are carried through the leaf FUB and terminated on `*_unused` nets. The core does not preserve `user` across the BRAM, so `s_axi_buser` and `s_axi_ruser` are hardwired to zero (matching legacy behavior).

### Memory Behavior

All memory semantics live in `sdpram_core`: byte-enabled writes on BRAM port A, single-cycle-latency reads on port B, one outstanding burst per side, and the bulk-clear FSM gated on both sides idle. See [`sdpram_core`](sdpram_core.md) for the full backend description.

### Debug Taps

`o_dbg_vr` mirrors the five external channel valid/ready pairs; `o_dbg_fub_vr` mirrors the same for the internal FUB. `o_dbg_bram_wr` / `o_dbg_bram_rd` pulse on real BRAM accesses, and `o_dbg_busy_wr` / `o_dbg_busy_rd` expose each skid leaf's busy flag.

### WRAP Assertion

A `translate_off` block asserts on each accepted AW and AR that `awburst`/`arburst` is not WRAP (`2'b10`). WRAP is computed by `axi_gen_addr` but not yet validated through the BRAM glue, so the assertion warns at the sim boundary.

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
sdpram_slave_axi4_axi4 #(
    .AXI_ID_WIDTH (8),
    .ADDR_WIDTH   (32),
    .DATA_WIDTH   (256),
    .MEM_DEPTH    (2048)
) u_mem (
    .aclk    (aclk),
    .aresetn (aresetn),

    // Write-side AXI4 slave (from the producer master)
    .s_axi_awid    (dut_awid),
    .s_axi_awaddr  (dut_awaddr),
    .s_axi_awlen   (dut_awlen),
    .s_axi_awsize  (dut_awsize),
    .s_axi_awburst (dut_awburst),
    .s_axi_awlock  (dut_awlock),
    .s_axi_awcache (dut_awcache),
    .s_axi_awprot  (dut_awprot),
    .s_axi_awqos   (dut_awqos),
    .s_axi_awregion(dut_awregion),
    .s_axi_awuser  (dut_awuser),
    .s_axi_awvalid (dut_awvalid),
    .s_axi_awready (dut_awready),
    // ... W, B, and the AR/R read channels ...

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

### Native AXI4, No Emulation

Unlike the AXIL-side wrappers, this variant needs no default-field synthesis — both sides are already AXI4, so the burst/ID fields pass through unchanged. The only tie-offs are the qualifier fields the core intentionally ignores, plus the `user` outputs the BRAM does not preserve.

### One Backend, Four Wrappers

This wrapper shares `sdpram_core` with the three other permutations. SystemVerilog cannot conditionally include ports in a single module's port list, so each protocol combination gets its own thin wrapper with the exact port shape; the memory kernel lives once in the core.

### WRAP Support Is Sim-Gated

INCR and FIXED bursts of any length are supported. WRAP is flagged by assertion until validated. Callers relying on WRAP semantics should exercise and confirm the path first.

---

## Related Modules

### Used By
- Characterization harnesses (memory model, descriptor RAM, semaphore RAM)
- Any AXI4-to-AXI4 shared-memory test scaffold

### Uses
- **axi4_slave_wr.sv** — Write-side AXI4 skid leaf
- **axi4_slave_rd.sv** — Read-side AXI4 skid leaf
- **sdpram_core.sv** — Shared SDPRAM backend

### See Also
- **sdpram_core.sv** — Protocol-agnostic backend ([doc](sdpram_core.md))
- **sdpram_slave_axi4_axil.sv** — AXI4 write + AXIL read variant
- **sdpram_slave_axil_axi4.sv** — AXIL write + AXI4 read variant
- **sdpram_slave_axil_axil.sv** — AXIL write + AXIL read variant

---

## References

### Source Code
- RTL: `rtl/amba/shared/sdpram_slave_axi4_axi4.sv`
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
