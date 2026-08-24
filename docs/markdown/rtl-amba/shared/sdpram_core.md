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

# SDPRAM Core

**Module:** `sdpram_core.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`sdpram_core` is the protocol-agnostic Simple Dual-Port RAM backend shared by the four `sdpram_slave_*` protocol wrappers. It owns the inferred dual-port BRAM array, a burst-aware write tracker, a burst-aware read tracker, and a bulk-clear FSM. It exposes a single FUB-shaped slave interface (an AXI superset with `id / addr / len / size / burst` on the address channels and `id / resp / last` on the response channels) so that a protocol-specific wrapper can drop straight on top without any string-switch `generate` plumbing.

### Key Features

- Inferred simple dual-port BRAM: one write port (port A) and one read port (port B)
- No reset on the RAM array (BRAM contents are undefined at power-up, cleared only via the bulk-clear FSM)
- FPGA `ram_style = "auto"` attribute for tool-driven BRAM inference
- Burst-aware write and read trackers driven by `axi_gen_addr` (INCR / FIXED any length up to AXI4's 256-beat max)
- Byte-enabled writes via `fub_wstrb`
- Single-cycle read latency on port B
- Bulk-clear FSM that walks the whole array to zero, gated on both sides idle
- FUB-shaped interface that degenerates cleanly to single-beat for AXIL wrappers
- Observation outputs (valid/ready snapshot, BRAM write/read fire pulses)

The `sdpram_slave_*` family needs one memory kernel that behaves identically regardless of which AMBA protocol drives its write and read sides. Rather than duplicate the BRAM, burst logic, and clear FSM in every protocol permutation, that logic lives once here, and the wrappers translate their protocol's FUB into this core's AXI-shaped FUB.

The core speaks exactly one wire format. AXI4 wrappers pass the real `awlen / awsize / awburst / awid` fields straight through; AXIL wrappers, which have no burst or ID fields, feed single-beat defaults (`awlen=0`, `awsize=$clog2(STRB_W)`, `awburst=INCR`, `awid=0`) so the burst tracker collapses to a single-beat path.

**Use Cases:**
- Shared backend for all four `sdpram_slave_{axi4,axil}_{axi4,axil}` wrappers
- Memory model / descriptor-RAM / semaphore-RAM inside characterization harnesses
- Memory ring backend behind a monitor-bus capture master-write port
- Any test bench needing a synthesizable dual-port scratch memory with a fast clear

**Key Benefit:** One compute kernel with all the burst and clear complexity in a single place, so the protocol wrappers stay thin and no "fake AXI4" fields leak into any external port list.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AXI_ID_WIDTH | int | 8 | FUB transaction-ID width. Passthrough on AXI4 wrappers; tied to a 1-bit zero by AXIL wrappers |
| ADDR_WIDTH | int | 32 | Byte-address width on both FUB address channels |
| DATA_WIDTH | int | 256 | Data-bus / BRAM word width (bits) |
| MEM_DEPTH | int | 2048 | Number of BRAM words (array depth) |

**Derived localparams:**
- `STRB_W = DATA_WIDTH / 8` — write-strobe / byte-enable width
- `ADDR_LSB = $clog2(STRB_W)` — byte-offset bits below the word address
- `MEM_AW = $clog2(MEM_DEPTH)` — BRAM word-address width
- `WORD_AW = ADDR_WIDTH - ADDR_LSB` — full word-address width

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Clock |
| aresetn | input | 1 | Active-low asynchronous reset (control logic only; never resets the BRAM array) |

### FUB Write Side (AW + W + B)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_awid | input | AXI_ID_WIDTH | Write transaction ID (echoed back on `fub_bid`) |
| fub_awaddr | input | ADDR_WIDTH | Write burst base byte-address |
| fub_awlen | input | 8 | Burst length minus 1 (0 = single beat) |
| fub_awsize | input | 3 | Beat size (log2 bytes) fed to `axi_gen_addr` |
| fub_awburst | input | 2 | Burst type: INCR (2'b01) / FIXED (2'b00) / WRAP (2'b10) |
| fub_awvalid | input | 1 | Write-address valid |
| fub_awready | output | 1 | Write-address ready (accepts when no write active, no B pending, not clearing) |
| fub_wdata | input | DATA_WIDTH | Write data |
| fub_wstrb | input | DATA_WIDTH/8 | Per-byte write strobe |
| fub_wvalid | input | 1 | Write-data valid |
| fub_wready | output | 1 | Write-data ready (asserted while a write burst is active and not clearing) |
| fub_bid | output | AXI_ID_WIDTH | Write-response ID (captured from `fub_awid`) |
| fub_bresp | output | 2 | Write response (OKAY 2'b00; SLVERR 2'b10 reserved for out-of-range) |
| fub_bvalid | output | 1 | Write-response valid (asserted while B pending) |
| fub_bready | input | 1 | Write-response ready |

### FUB Read Side (AR + R)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_arid | input | AXI_ID_WIDTH | Read transaction ID (echoed on `fub_rid`) |
| fub_araddr | input | ADDR_WIDTH | Read burst base byte-address |
| fub_arlen | input | 8 | Burst length minus 1 (0 = single beat) |
| fub_arsize | input | 3 | Beat size (log2 bytes) fed to `axi_gen_addr` |
| fub_arburst | input | 2 | Burst type: INCR / FIXED / WRAP |
| fub_arvalid | input | 1 | Read-address valid |
| fub_arready | output | 1 | Read-address ready (accepts when no read active, not clearing) |
| fub_rid | output | AXI_ID_WIDTH | Read-data ID (from the inflight tracker) |
| fub_rdata | output | DATA_WIDTH | Read data (BRAM port-B output) |
| fub_rresp | output | 2 | Read response (OKAY / SLVERR reserved) |
| fub_rlast | output | 1 | Last-beat marker of the read burst |
| fub_rvalid | output | 1 | Read-data valid (reflects the inflight tracker) |
| fub_rready | input | 1 | Read-data ready |

### Bulk-Clear Control

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_cfg_start_clear | input | 1 | Request a full-array clear (accepted only when both sides idle) |
| o_cfg_done_clear | output | 1 | Asserted when the clear walk has finished |

### Observation

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_dbg_fub_vr | output | 10 | FUB-side valid/ready snapshot: `{rready,rvalid, arready,arvalid, bready,bvalid, wready,wvalid, awready,awvalid}` |
| o_dbg_bram_wr | output | 1 | One-cycle pulse when a BRAM port-A write fires |
| o_dbg_bram_rd | output | 1 | One-cycle pulse when a BRAM port-B read issues |

---

## Functional Description

### FUB Interface Contract

The core speaks a single wire format — a FUB-shaped AXI superset — and nothing else. On the address channels it carries `id / addr / len / size / burst`; on the response channels it carries `id / resp / last`. Wrappers translate their protocol into this shape:

- **AXI4 wrappers** pass the real `awlen / awsize / awburst / awid` (and the AR equivalents) straight through.
- **AXIL wrappers** feed defaults: `awlen = 0`, `awsize = $clog2(STRB_W)`, `awburst = 2'b01` (INCR), `awid = 0`. With `len = 0`, the burst tracker degenerates to a single-beat path.

### Write Path — Burst Tracker

On `fub_awvalid && fub_awready`, the tracker latches the burst's ID, base address, beat count (`awlen`), size, and burst type, and asserts `r_wr_active`. Each accepted W beat (`fub_wvalid && fub_wready`) writes byte-enabled data into BRAM port A at the current word address, then advances the address through `axi_gen_addr` and decrements the beat counter. When the last beat is accepted (`r_wr_beats_left == 0`), the tracker drops `r_wr_active`, latches a pending B response (`r_b_pending`), and captures the ID and response code. `fub_awready` deasserts while a write is active or a B is pending, so only one write burst is in flight at a time.

### Read Path — Burst Tracker

On `fub_arvalid && fub_arready`, the read tracker latches the burst parameters and asserts `r_rd_active`. A read beat issues (`read_issue`) when the burst is active, the core is not clearing, and either the inflight register is empty or the current beat is being consumed (`!r_inflight || fub_rready`). Each issue reads BRAM port B at the current word address (one-cycle latency), advances the address through `axi_gen_addr`, decrements the beat count, and — on the last beat — drops `r_rd_active`. An inflight tracker holds the `(id, rresp, rlast)` for the beat currently presented on `fub_r`, driving `fub_rvalid`; it clears on handshake unless a new issue refills it the same cycle.

### Address Generation

Both paths use an `axi_gen_addr` instance (parameterized `AW=ADDR_WIDTH`, `DW=ODW=DATA_WIDTH`, `LEN=8`) to compute the next beat address from the current address, size, and burst type. INCR and FIXED are handled directly by the glue. WRAP addressing is wrap-shaped end to end: the burst type feeds `axi_gen_addr`, whose `len` input is the LATCHED burst length (the pre-2026-08-13 wiring fed the decrementing remainder, which shrank the wrap mask mid-burst and folded addresses early). The AXI4 wrappers still carry a sim-only assertion flagging WRAP until the path is validated by a test.

### BRAM Array

The memory is an inferred dual-port array (`(* ram_style = "auto" *) logic [DATA_WIDTH-1:0] r_mem [MEM_DEPTH]`). It is **never reset** — BRAM contents come up undefined and are only zeroed by the bulk-clear FSM. Port A is shared between the clear FSM (when clearing) and byte-enabled writes; port B is a registered read (single-cycle latency). A benign `WIDTHTRUNC` lint-off covers Verilator computing an extra index bit for the never-taken clear wrap path; every index that reaches the array is provably in `[0, MEM_DEPTH-1]` by tracker construction.

### Bulk-Clear FSM

The clear FSM has two states (`CLR_IDLE`, `CLR_BUSY`). It accepts `i_cfg_start_clear` only when both sides report idle (`!r_wr_active && !r_b_pending && !r_rd_active && !r_inflight`), which keeps it from glitching `fub_*_ready` mid-transaction. Once busy, it walks `r_clear_addr` from 0 to `MEM_DEPTH-1`, writing zero to BRAM port A each cycle, then returns to idle and asserts `o_cfg_done_clear`. While `w_clearing` is asserted, `fub_awready`, `fub_wready`, and `fub_arready` are all deasserted so the FSM owns port A cleanly.

### Observation Outputs

`o_dbg_fub_vr` packs the ten FUB valid/ready bits for waveform-free probing. `o_dbg_bram_wr` pulses on a real byte-enabled write fire, and `o_dbg_bram_rd` pulses on each read issue.

---

## Usage Example

`sdpram_core` is not usually instantiated directly — the `sdpram_slave_*` wrappers do that. The pattern (as used inside every wrapper) is:

```systemverilog
sdpram_core #(
    .AXI_ID_WIDTH (AXI_ID_WIDTH),
    .ADDR_WIDTH   (ADDR_WIDTH),
    .DATA_WIDTH   (DATA_WIDTH),
    .MEM_DEPTH    (MEM_DEPTH)
) u_core (
    .aclk    (aclk),
    .aresetn (aresetn),

    // Write FUB (from a slave-write leaf, or single-beat defaults for AXIL)
    .fub_awid    (fub_awid),
    .fub_awaddr  (fub_awaddr),
    .fub_awlen   (fub_awlen),      // 8'h00 for AXIL
    .fub_awsize  (fub_awsize),     // $clog2(STRB_W) for AXIL
    .fub_awburst (fub_awburst),    // 2'b01 (INCR) for AXIL
    .fub_awvalid (fub_awvalid),
    .fub_awready (fub_awready),
    .fub_wdata   (fub_wdata),
    .fub_wstrb   (fub_wstrb),
    .fub_wvalid  (fub_wvalid),
    .fub_wready  (fub_wready),
    .fub_bid     (fub_bid),
    .fub_bresp   (fub_bresp),
    .fub_bvalid  (fub_bvalid),
    .fub_bready  (fub_bready),

    // Read FUB (from a slave-read leaf)
    .fub_arid    (fub_arid),
    .fub_araddr  (fub_araddr),
    .fub_arlen   (fub_arlen),
    .fub_arsize  (fub_arsize),
    .fub_arburst (fub_arburst),
    .fub_arvalid (fub_arvalid),
    .fub_arready (fub_arready),
    .fub_rid     (fub_rid),
    .fub_rdata   (fub_rdata),
    .fub_rresp   (fub_rresp),
    .fub_rlast   (fub_rlast),
    .fub_rvalid  (fub_rvalid),
    .fub_rready  (fub_rready),

    // Bulk clear + debug
    .i_cfg_start_clear (i_cfg_start_clear),
    .o_cfg_done_clear  (o_cfg_done_clear),
    .o_dbg_fub_vr      (o_dbg_fub_vr),
    .o_dbg_bram_wr     (o_dbg_bram_wr),
    .o_dbg_bram_rd     (o_dbg_bram_rd)
);
```

---

## Design Notes

### No Reset on the RAM Array

The BRAM array is deliberately not reset. Resetting a large inferred RAM prevents BRAM inference on most FPGA flows and costs an enormous number of flip-flops on ASIC. Contents are undefined at power-up; software (or a harness) issues `i_cfg_start_clear` to zero the array when a defined starting state is required.

### One Wire Format, Four Wrappers

The core exists so that the burst logic, byte-enable write, single-cycle read, and clear FSM are written exactly once. The four protocol permutations are thin wrappers that only translate their protocol's FUB into this AXI-shaped FUB. AXIL sides supply the burst/ID defaults in exactly one place per wrapper, so no external port list ever exposes a "fake AXI4" field.

### WRAP Bursts

WRAP address math is wrap-shaped via `axi_gen_addr` fed with the latched burst length (mask-shrink bug fixed 2026-08-13), but the path remains UNVALIDATED: the AXI4 wrappers assert (sim-only) that `awburst`/`arburst` is not WRAP at the interface boundary until a test drives it. INCR and FIXED are fully supported.

### Single Outstanding Burst Per Side

Each side accepts one burst at a time — `fub_awready` deasserts while a write is active or a B is pending, and `fub_arready` deasserts while a read is active. This keeps the tracker state minimal and matches the descriptor-RAM / scratch-memory use cases the family targets.

---

## Related Modules

### Used By
- `sdpram_slave_axi4_axi4.sv` — AXI4 write + AXI4 read wrapper
- `sdpram_slave_axi4_axil.sv` — AXI4 write + AXIL read wrapper
- `sdpram_slave_axil_axi4.sv` — AXIL write + AXI4 read wrapper
- `sdpram_slave_axil_axil.sv` — AXIL write + AXIL read wrapper
- Characterization harnesses (e.g. `rapids_char_harness` descriptor RAM, `stream_char_harness` memory ring)

### Uses
- **axi_gen_addr.sv** — Next-beat address generation for both trackers
- **reset_defs.svh** — `ALWAYS_FF_RST` / `RST_ASSERTED` reset macros

### See Also
- **sdpram_slave_axi4_axi4.sv** — the AXI4/AXI4 protocol wrapper
- **sdpram_slave_axil_axil.sv** — the AXIL/AXIL protocol wrapper
- **monbus_group_core.sv** — a comparable "one core + protocol wrappers" split for the monitor-bus delivery layer

---

## References

### Source Code
- RTL: `rtl/amba/shared/sdpram_core.sv`
- Address gen: `rtl/amba/shared/axi_gen_addr.sv`
- Wrappers: `rtl/amba/shared/sdpram_slave_*.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Subsystem guide: `rtl/amba/CLAUDE.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
