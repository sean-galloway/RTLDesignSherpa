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

# peregrine_top Port Specification

**Module:** `peregrine_top.sv`

`peregrine_top` is the cached build: `peregrine_core` at `CACHE_EN=1`, the I\$, amber, the CLINT, the uncached port and the arbiter, with one AXI4 master port to the fabric.

## Parameters

<!-- GEN:params:peregrine_top -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `RESET_ADDR` | parameter | `logic [31:0]` | `32'h0000_0000` | First fetch address |
| `MUL_DSP` | parameter | `bit` | `1'b0` | 0: iterative multiply (33 stall cycles); 1: one registered DSP product (2) |
| `BP_EN` | parameter | `bit` | `1'b1` | 1: BTB + BHT prediction; 0: predict not taken (merlin's fetch) |
| `BTB_ENTRIES` | parameter | `int` | `32` | BTB entries, a power of two (PRD P5: 32) |
| `BHT_ENTRIES` | parameter | `int` | `256` | BHT counters, a power of two >= BTB_ENTRIES (PRD P5: 256) |
| `ICACHE_BYTES` | parameter | `int` | `4096` | I\$ capacity (PRD P9: 4096) |
| `ICACHE_LINE` | parameter | `int` | `64` | I\$ line size (PRD P9: 64) |
| `AXI_DW` | parameter | `int` | `64` | Fabric data width, and amber's BUS_WIDTH (32 or 64) |
| `AXI_IW` | parameter | `int` | `4` | Per-master AXI id width; the fabric id is AXI_IW + 2 |
| `MTIME_DIV` | parameter | `int` | `1` | CLINT clocks per mtime tick (>= 1) |
| `DC_SETS` | parameter | `int` | `128` | amber sets |
| `DC_WAYS` | parameter | `int` | `4` | amber ways |
| `DC_LINE` | parameter | `int` | `64` | amber line bytes |
| `UC_BASE` | parameter | `logic [31:0]` | `32'h1000_0000` | Uncached window base: an address is uncached when (addr & UC_MASK) == UC_BASE |
| `UC_MASK` | parameter | `logic [31:0]` | `32'hF000_0000` | Uncached window mask (default: bits 31:28, the 0x1000_0000 window) |
| `FIW` | localparam | `int` | `AXI_IW + 2` | Fabric id width (derived) |

: peregrine_top parameters

<!-- /GEN -->

The I\$ and amber geometries are the ones peregrine was verified and timed at: a 4 KiB I\$ with 64 B lines, and amber at 128 sets x 4 ways x 64 B (32 KiB), the geometry amber's hit latency was measured at (PRD P13).

## Ports

<!-- GEN:ports:peregrine_top -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock for the core, caches and fabric port |
| `rst_n` | input | `1` | Asynchronous active-low reset (synchronized inside) |
| `irq_external` | input | `1` | Machine external interrupt (level) |
| `tb_irq_software` | input | `1` | TB hook ORed into the CLINT software interrupt; tie 0 |
| `tb_irq_timer` | input | `1` | TB hook ORed into the CLINT timer interrupt; tie 0 |

: peregrine_top ports: Clock, reset and interrupts

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `dc_clean_req` | input | `1` | Hold high to clean the D\$ (TB / debug hook); tie 0 |
| `dc_clean_done` | output | `1` | High from the clean's completion until dc_clean_req drops |

: peregrine_top ports: D\$ clean hook

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `m_axi_arid` | output | `[FIW-1:0]` | Read address id |
| `m_axi_araddr` | output | `[31:0]` | Read address |
| `m_axi_arlen` | output | `[7:0]` | Burst length - 1 |
| `m_axi_arsize` | output | `[2:0]` | Beat size (log2 bytes) |
| `m_axi_arburst` | output | `[1:0]` | Burst type |
| `m_axi_arvalid` | output | `1` | Read address valid |
| `m_axi_arready` | input | `1` | Read address ready |
| `m_axi_rid` | input | `[FIW-1:0]` | Read data id |
| `m_axi_rdata` | input | `[AXI_DW-1:0]` | Read data beat |
| `m_axi_rresp` | input | `[1:0]` | Read response |
| `m_axi_rlast` | input | `1` | Last read beat |
| `m_axi_rvalid` | input | `1` | Read data valid |
| `m_axi_rready` | output | `1` | Read data ready |
| `m_axi_arlock` | output | `1` | Driven 0 |
| `m_axi_arcache` | output | `[3:0]` | Driven 0 |
| `m_axi_arprot` | output | `[2:0]` | Driven 0 |
| `m_axi_arqos` | output | `[3:0]` | Driven 0 |
| `m_axi_arregion` | output | `[3:0]` | Driven 0 |

: peregrine_top ports: AXI4 fabric master: read

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `m_axi_awid` | output | `[FIW-1:0]` | Write address id |
| `m_axi_awaddr` | output | `[31:0]` | Write address |
| `m_axi_awlen` | output | `[7:0]` | Burst length - 1 |
| `m_axi_awsize` | output | `[2:0]` | Beat size (log2 bytes) |
| `m_axi_awburst` | output | `[1:0]` | Burst type |
| `m_axi_awvalid` | output | `1` | Write address valid |
| `m_axi_awready` | input | `1` | Write address ready |
| `m_axi_wdata` | output | `[AXI_DW-1:0]` | Write data beat |
| `m_axi_wstrb` | output | `[STRBW-1:0]` | Write byte strobes |
| `m_axi_wlast` | output | `1` | Last write beat |
| `m_axi_wvalid` | output | `1` | Write data valid |
| `m_axi_wready` | input | `1` | Write data ready |
| `m_axi_bid` | input | `[FIW-1:0]` | Write response id |
| `m_axi_bresp` | input | `[1:0]` | Write response |
| `m_axi_bvalid` | input | `1` | Write response valid |
| `m_axi_bready` | output | `1` | Write response ready |
| `m_axi_awlock` | output | `1` | Driven 0 |
| `m_axi_awcache` | output | `[3:0]` | Driven 0 |
| `m_axi_awprot` | output | `[2:0]` | Driven 0 |
| `m_axi_awqos` | output | `[3:0]` | Driven 0 |
| `m_axi_awregion` | output | `[3:0]` | Driven 0 |

: peregrine_top ports: AXI4 fabric master: write

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `dobs_valid` | output | `1` | A load or store was accepted this cycle |
| `dobs_addr` | output | `[31:0]` | Its word address |
| `dobs_wstrb` | output | `[3:0]` | Its byte strobes (0 for a load) |
| `dobs_wdata` | output | `[31:0]` | Its store data |

: peregrine_top ports: D-side observation (TB)

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `rvfi_valid` | output | `1` | One instruction retires this cycle (WB, not under mem_wait) |
| `rvfi_order` | output | `[63:0]` | Retire index, counting trap beats |
| `rvfi_pc_rdata` | output | `[31:0]` | PC of the retiring instruction |
| `rvfi_pc_wdata` | output | `[31:0]` | Its next PC: the trap vector on a trap, mepc on mret |
| `rvfi_insn` | output | `[31:0]` | Instruction word |
| `rvfi_trap` | output | `1` | The instruction trapped in MEM (no rd write, no memory access) |
| `rvfi_rs1_addr` | output | `[4:0]` | rs1 field |
| `rvfi_rs2_addr` | output | `[4:0]` | rs2 field |
| `rvfi_rs1_rdata` | output | `[31:0]` | rs1 value used (the latched operand for an M instruction) |
| `rvfi_rs2_rdata` | output | `[31:0]` | rs2 value used (the latched operand for an M instruction) |
| `rvfi_rd_addr` | output | `[4:0]` | rd written, 0 when none |
| `rvfi_rd_wdata` | output | `[31:0]` | Value written to rd, 0 when none |
| `rvfi_mem_addr` | output | `[31:0]` | Word address of the access |
| `rvfi_mem_rmask` | output | `[3:0]` | Bytes read |
| `rvfi_mem_wmask` | output | `[3:0]` | Bytes written |
| `rvfi_mem_rdata` | output | `[31:0]` | Word read |
| `rvfi_mem_wdata` | output | `[31:0]` | Data written, on its lanes |

: peregrine_top ports: RVFI retire

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `rvfi_trap_cause` | output | `[31:0]` | mcause of the trap committed with this beat, valid with rvfi_trap |
| `rvfi_bp_pred_taken` | output | `1` | Predicted taken at fetch |
| `rvfi_bp_pred_target` | output | `[31:0]` | Predicted target at fetch |
| `rvfi_bp_mispredict` | output | `1` | EX found the prediction wrong |

: peregrine_top ports: Trap and predictor observation

<!-- /GEN -->

## Fabric Port Contract

- **One master, three sources.** The fabric id is `{master index, master id}`, `AXI_IW + 2` bits wide. Index 0 is the I\$ refill, 1 is amber, 2 is the uncached port. A fabric slave must return R and B with the id it was given; the arbiter routes them by the index.
- **Reads** may be in flight from different masters at once. Each master has at most one read outstanding: the I\$ and amber are blocking, and the uncached port holds one transaction.
- **Writes are serialized.** An AW grant makes its master the W owner until its `wlast` beat, and no other AW is granted meanwhile; W never interleaves. Writes come from amber (write-back, WriteClean during a clean) and the uncached port.
- **Bursts.** The I\$ and amber issue INCR bursts of a whole line (`LINE_BYTES / (AXI_DW/8)` beats); the uncached port issues single beats with AxSIZE 4 bytes.
- **Unused fields.** `AxLOCK`, `AxCACHE`, `AxPROT`, `AxQOS` and `AxREGION` are driven 0.
- **Errors.** `rresp` / `bresp` bit 1 (SLVERR, DECERR) is an error: an instruction access fault on an I\$ refill, a load or store access fault on an uncached access or an amber fill, and the bus-error interrupt on an amber write-back ("Trap and Interrupt Behavior"). A slave must still return every beat of a burst it answers with an error. Bit 0 (EXOKAY vs OKAY) is not read.

## Hooks a System Ties Off

| Port | Tie | Purpose |
|------|-----|---------|
| `tb_irq_software`, `tb_irq_timer` | 0 | Let the TB drive interrupts directly on the cached build |
| `dc_clean_req` | 0 | Lets a TB clean amber before reading memory (the arch-test signature) |
| `dobs_*` | open | D-side observation at the handshake, for TB checks |

: peregrine_top test and debug hooks

---

**Last Updated:** 2026-11-25
