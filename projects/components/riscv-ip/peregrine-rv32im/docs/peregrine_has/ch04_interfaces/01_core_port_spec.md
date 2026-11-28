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

# peregrine_core Port Specification

**Module:** `peregrine_core.sv`

`peregrine_core` is the whole core. At `CACHE_EN=0` it is also the whole cacheless build; at `CACHE_EN=1` it is instantiated by `peregrine_top`, which drives its memory ports from the I\$ and the D-side wrapper. All tables in this chapter are generated from the RTL header by `peregrine_mas/gen_port_tables.py`.

## Parameters

<!-- GEN:params:peregrine_core -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `RESET_ADDR` | parameter | `logic [31:0]` | `32'h0000_0000` | First fetch address |
| `MUL_DSP` | parameter | `bit` | `1'b0` | 0: iterative multiply (33 stall cycles); 1: one registered DSP product (2) |
| `BP_EN` | parameter | `bit` | `1'b1` | 1: BTB + BHT prediction; 0: predict not taken (merlin's fetch) |
| `BTB_ENTRIES` | parameter | `int` | `32` | BTB entries, a power of two (PRD P5: 32) |
| `BHT_ENTRIES` | parameter | `int` | `256` | BHT counters, a power of two >= BTB_ENTRIES (PRD P5: 256) |
| `CACHE_EN` | parameter | `bit` | `1'b0` | 0: cacheless build (PRD P12); 1: the build inside peregrine_top |

: peregrine_core parameters

<!-- /GEN -->

## Ports

All ports are synchronous to `clk`. `rst_n` is asynchronous active-low and is synchronized inside the core (`reset_sync`, three stages); the core leaves reset three clocks after `rst_n` rises.

<!-- GEN:ports:peregrine_core -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Core clock |
| `rst_n` | input | `1` | Asynchronous active-low reset (synchronized inside) |
| `mem_wait` | input | `1` | 1: memories not ready -- hold all state |

: peregrine_core ports: Clock, reset and hold

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `imem_addr` | output | `[31:0]` | PC of the instruction being fetched |
| `imem_addr_next` | output | `[31:0]` | PC after this edge (registered-read fetch) |
| `imem_addr_next_nw` | output | `[31:0]` | the same, as if mem_wait were low |
| `imem_rdata` | input | `[31:0]` | The word at imem_addr, this cycle (comb read, or a registered read at last cycle's imem_addr_next) |

: peregrine_core ports: Instruction fetch

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `dmem_req` | output | `1` | Load or store in MEM this cycle (gated by mem_wait) |
| `dmem_addr` | output | `[31:0]` | Word address of the access |
| `dmem_rdata` | input | `[31:0]` | The load's word in the cycle after the request (WB), held until WB retires |
| `dmem_wstrb` | output | `[3:0]` | Store byte strobes, 0 for a load |
| `dmem_wdata` | output | `[31:0]` | Store data, rotated onto its lanes |

: peregrine_core ports: Data access

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `dmem_req_pre` | output | `1` | the MEM access, before the mem_wait gate |
| `fencei_req` | output | `1` | fence.i in MEM: clean D\$, invalidate I\$ |

: peregrine_core ports: Cached-build handshake (CACHE_EN=1; 0 when CACHE_EN=0)

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `imem_fault` | input | `1` | the fetch at imem_addr faulted (with imem_rdata) |
| `dmem_fault` | input | `1` | WB's load/store response was an error (with dmem_rdata) |
| `irq_buserr` | input | `1` | amber's sticky write-back error (mip.16) |
| `buserr_info` | input | `[31:0]` | what mbuserr (0x7C0) reads |
| `buserr_clear` | output | `1` | a write to mbuserr committed |

: peregrine_core ports: Bus errors (CACHE_EN=1; tie 0 when CACHE_EN=0)

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `irq_software` | input | `1` | Machine software interrupt (level) |
| `irq_timer` | input | `1` | Machine timer interrupt (level) |
| `irq_external` | input | `1` | Machine external interrupt (level) |

: peregrine_core ports: Interrupts

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

: peregrine_core ports: RVFI retire

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `rvfi_trap_cause` | output | `[31:0]` | mcause of the trap committed with this beat, valid with rvfi_trap |
| `rvfi_bp_pred_taken` | output | `1` | Predicted taken at fetch |
| `rvfi_bp_pred_target` | output | `[31:0]` | Predicted target at fetch |
| `rvfi_bp_mispredict` | output | `1` | EX found the prediction wrong |

: peregrine_core ports: Trap and predictor observation

<!-- /GEN -->

## Port Notes

- **`imem_addr_next` and `imem_addr_next_nw`.** `imem_addr_next` is the value the PC takes at the coming edge (`RESET_ADDR` in reset), for a registered-read instruction memory. `imem_addr_next_nw` is the same value as if `mem_wait` were low; a memory that takes `mem_wait` as its read enable can address itself with it, which keeps `mem_wait` off the RAM address path (the I\$ does this).
- **`dmem_req` and `dmem_req_pre`.** `dmem_req` is the MEM-stage access gated by `~mem_wait`, for the cacheless contract. `dmem_req_pre` is the same access before that gate, for a valid/ready target: it stays high until the access is accepted (see "Memory Contract"). It is 0 at `CACHE_EN=0`.
- **`fencei_req`.** High while a `fence.i` that is going to commit sits in MEM at `CACHE_EN=1`. The wrapper holds `mem_wait` until its maintenance is done; 0 at `CACHE_EN=0`.
- **RVFI.** One beat per retired instruction, including trap beats, in program order at WB (the MAS RVFI chapter gives the field rules). There are no `rvfi_intr` or `rvfi_csr_*` fields; trap observation is `rvfi_trap` with `rvfi_trap_cause`.

---

**Last Updated:** 2026-11-25
