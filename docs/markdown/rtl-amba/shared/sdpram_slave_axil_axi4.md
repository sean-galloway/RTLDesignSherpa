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

# SDPRAM Slave — AXIL Write / AXI4 Read

**Module:** `sdpram_slave_axil_axi4.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`sdpram_slave_axil_axi4` is the asymmetric member of the family: a **single-beat AXI4-Lite slave on the write side** (AW + W + B) and a **full AXI4 slave on the read side** (AR + R), both in front of the shared `sdpram_core` backend. The write side instantiates `axil4_slave_wr`; the read side instantiates `axi4_slave_rd` (full AXI4 with id / len / size / burst). AXIL carries no burst or ID fields, so the wrapper bridges the AXIL write FUB into the core's AXI-shaped write FUB using single-beat defaults — the one spot in this design where anything is synthesized rather than genuine.

That shape fits a common characterization pattern: a host CPU populates a memory a word at a time over a simple AXIL write port (a descriptor RAM's host-write port, say), while a high-throughput engine reads bursts back over full AXI4. Supplying the missing AXI-shaped fields at the single point where the AXIL write FUB meets the core collapses the core's write burst tracker to a single-beat path.

### Key Features

- Single-beat AXIL write slave (no burst / ID)
- Full AXI4 read slave (burst, ID, size)
- AXIL write FUB bridged into the core with `awlen=0`, `awsize=$clog2(STRB_W)`, `awburst=INCR`, `awid=0`
- Shared `sdpram_core` backend
- Byte-enabled writes, single-cycle-latency reads
- Bulk-clear control and debug taps
- Sim-only WRAP-burst assertion on the AXI4 read side

**Use Cases:**
- Descriptor RAM: host writes descriptors over AXIL, an engine reads them over AXI4 bursts
- Semaphore / mailbox RAM: single-word AXIL writes, bursty AXI4 reads
- Memory model populated by a control-plane CPU and consumed by a data-plane master

**Key Benefit:** A simple word-at-a-time AXIL write port with full AXI4 burst read throughput, with the single-beat adaptation isolated to one place in the wrapper.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AXI_ID_WIDTH | int | 8 | AXI4 read-side transaction-ID width |
| ADDR_WIDTH | int | 32 | Byte-address width (both sides) |
| DATA_WIDTH | int | 256 | Data-bus / BRAM word width (bits) |
| USER_WIDTH | int | 1 | AXI4 read-side USER width (carried by leaf, not preserved through BRAM) |
| MEM_DEPTH | int | 2048 | BRAM depth in words |
| SKID_DEPTH_AW | int | 2 | Write-address skid depth |
| SKID_DEPTH_W | int | 2 | Write-data skid depth |
| SKID_DEPTH_B | int | 2 | Write-response skid depth |
| SKID_DEPTH_AR | int | 2 | Read-address skid depth |
| SKID_DEPTH_R | int | 4 | Read-data skid depth |

**Derived localparams:** `STRB_W = DATA_WIDTH/8`, `FUB_AWSIZE_DEFAULT = $clog2(STRB_W)` (the `awsize` fed to the core for the single-beat write path).

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
| o_dbg_vr | output | 10 | External valid/ready snapshot `{rready,rvalid, arready,arvalid, bready,bvalid, wready,wvalid, awready,awvalid}` (AXI4 R/AR on top, AXIL B/W/AW below) |
| o_dbg_fub_vr | output | 10 | FUB-side valid/ready snapshot from the core |
| o_dbg_bram_wr | output | 1 | BRAM write-fire pulse |
| o_dbg_bram_rd | output | 1 | BRAM read-issue pulse |
| o_dbg_busy_wr | output | 1 | Write-side (AXIL) skid-leaf busy |
| o_dbg_busy_rd | output | 1 | Read-side (AXI4) skid-leaf busy |

---

## Functional Description

### Structure

Three instances: `axil4_slave_wr` (write), `axi4_slave_rd` (read), and `sdpram_core` (backend). The read leaf's FUB carries full AXI4 read fields into the core. The write leaf's AXIL FUB carries only address and data — the wrapper supplies the burst/ID fields the core expects.

### AXIL Write Bridge

The AXIL write FUB (`fub_axil_awaddr / awvalid / awready`, `wdata / wstrb / wvalid / wready`, `bresp / bvalid / bready`) is wired to the core's write FUB, and the AXI-shaped fields the core needs are tied off at that boundary:

- `fub_awid = '0`
- `fub_awlen = 8'h00` (single beat)
- `fub_awsize = 3'(FUB_AWSIZE_DEFAULT)` = `$clog2(STRB_W)` (one full data word per beat)
- `fub_awburst = 2'b01` (INCR)

The core's `fub_bid` output goes to a `*_unused` net — AXIL has no B-channel ID. With `awlen = 0`, each AXIL write is a single-beat access into BRAM.

### Read Path and Tie-Offs

The read side passes full AXI4 fields straight through. The AXI4 qualifier fields the core ignores (`lock`, `cache`, `prot`, `qos`, `region`, `user`) terminate on `*_unused` nets. `s_axi_ruser` is hardwired to zero since the core does not preserve user across the BRAM.

### Memory Behavior

Byte-enabled writes, single-cycle-latency reads, one outstanding burst per side, and the bulk-clear FSM all live in `sdpram_core` — see [`sdpram_core`](sdpram_core.md).

### WRAP Assertion

A `translate_off` block asserts on each accepted AR that `arburst` is not WRAP. Only the read side carries this assertion; the AXIL write side is inherently single-beat INCR.

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
sdpram_slave_axil_axi4 #(
    .AXI_ID_WIDTH (8),
    .ADDR_WIDTH   (32),
    .DATA_WIDTH   (256),
    .MEM_DEPTH    (2048)
) u_desc_ram (
    .aclk    (aclk),
    .aresetn (aresetn),

    // AXIL host-write port (descriptor population)
    .s_axil_awaddr  (host_awaddr),
    .s_axil_awprot  (host_awprot),
    .s_axil_awvalid (host_awvalid),
    .s_axil_awready (host_awready),
    .s_axil_wdata   (host_wdata),
    .s_axil_wstrb   (host_wstrb),
    .s_axil_wvalid  (host_wvalid),
    .s_axil_wready  (host_wready),
    .s_axil_bresp   (host_bresp),
    .s_axil_bvalid  (host_bvalid),
    .s_axil_bready  (host_bready),

    // AXI4 burst read port (engine fetch)
    .s_axi_arid    (eng_arid),
    .s_axi_araddr  (eng_araddr),
    .s_axi_arlen   (eng_arlen),
    /* ...remaining AR/R... */
    .s_axi_rvalid  (eng_rvalid),
    .s_axi_rready  (eng_rready),

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

### Descriptor-RAM Fit

This is the natural shape for a descriptor / semaphore RAM: a control-plane CPU pokes single words over AXIL, and a data-plane engine burst-reads them over AXI4. The `rapids_char_harness` descriptor RAM host-write port is exactly this pattern.

### Single-Beat Adaptation Lives in One Place

The only "fake AXI4" fields anywhere in this wrapper are the four write-side defaults (`awid / awlen / awsize / awburst`) fed to the core at the AXIL write FUB boundary. Everything else on the read side is genuine AXI4.

### One Backend, Four Wrappers

This wrapper shares `sdpram_core` with the three other permutations. Each protocol combination is a thin wrapper with its exact port shape; the memory kernel lives once in the core.

---

## Related Modules

### Used By
- `rapids_char_harness` descriptor RAM (host-write port)
- Characterization harnesses with AXIL host-write and AXI4 engine-read

### Uses
- **axil4_slave_wr.sv** — Write-side AXIL skid leaf
- **axi4_slave_rd.sv** — Read-side AXI4 skid leaf
- **sdpram_core.sv** — Shared SDPRAM backend

### See Also
- **sdpram_core.sv** — Protocol-agnostic backend ([doc](sdpram_core.md))
- **sdpram_slave_axi4_axi4.sv** — AXI4 write + AXI4 read variant
- **sdpram_slave_axi4_axil.sv** — AXI4 write + AXIL read variant
- **sdpram_slave_axil_axil.sv** — AXIL write + AXIL read variant

---

## Testing

`val/amba/test_sdpram_slave_axil_axi4.py` exercises this module. It collects 3 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_sdpram_slave_axil_axi4.py -v
```

---

## References

### Source Code
- RTL: `rtl/amba/shared/sdpram_slave_axil_axi4.sv`
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
