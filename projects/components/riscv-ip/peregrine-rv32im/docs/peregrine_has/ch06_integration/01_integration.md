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

# Integration Guide

## Choosing a Build

| Need | Use |
|------|-----|
| A system with caches and an AXI4 fabric | `peregrine_top` |
| Instruction and data memories of your own, no caches | `peregrine_core` at `CACHE_EN=0` |
| riscv-formal, fast ISA batteries | `peregrine_core` at `CACHE_EN=0` |

: Which module to integrate

`peregrine_core` at `CACHE_EN=1` is meant only for `peregrine_top`: it expects the wrapper to drive `mem_wait` from the D-side handshake and to service `fencei_req`.

## Filelists

Compile from the filelists, never from a hand-listed set of sources:

| Filelist | Contents |
|----------|----------|
| `rtl/filelists/top/peregrine_core.f` | The core and everything it instantiates, including the shared common-rv32i blocks and kestrel's register file |
| `rtl/filelists/top/peregrine_top.f` | The core, the I\$, CLINT, uncached port, arbiter, and amber (through `$AMBER_ROOT/rtl/filelists/amber_top.f`) |
| `rtl/filelists/peregrine_all.f` | The whole area |

: peregrine filelists

The filelists use `$REPO_ROOT`, `$PEREGRINE_ROOT`, `$RV32I_COMMON_ROOT`, `$KESTREL_ROOT` and `$AMBER_ROOT`, which the repo's `env_python` sets.

## Clock and Reset

One clock and one active-low asynchronous reset. Both modules synchronize `rst_n` internally; the reset may be released asynchronously. The CLINT's `mtime` counts in core clocks divided by `MTIME_DIV`; set it so `mtime` ticks at the rate software expects.

## Cacheless Instantiation

```systemverilog
peregrine_core #(
    .RESET_ADDR  (32'h0000_0000),
    .MUL_DSP     (1'b0),
    .BP_EN       (1'b1),
    .BTB_ENTRIES (32),
    .BHT_ENTRIES (256),
    .CACHE_EN    (1'b0)
) u_core (
    .clk                 (clk),
    .rst_n               (rst_n),
    .mem_wait            (mem_wait),
    .imem_addr           (imem_addr),
    .imem_addr_next      (imem_addr_next),
    .imem_addr_next_nw   (),
    .imem_rdata          (imem_rdata),
    .dmem_req            (dmem_req),
    .dmem_addr           (dmem_addr),
    .dmem_rdata          (dmem_rdata),
    .dmem_wstrb          (dmem_wstrb),
    .dmem_wdata          (dmem_wdata),
    .dmem_req_pre        (),
    .fencei_req          (),
    .irq_software        (irq_software),
    .irq_timer           (irq_timer),
    .irq_external        (irq_external),
    .rvfi_valid          (rvfi_valid),
    .rvfi_order          (),
    .rvfi_pc_rdata       (),
    .rvfi_pc_wdata       (),
    .rvfi_insn           (),
    .rvfi_trap           (),
    .rvfi_rs1_addr       (),
    .rvfi_rs2_addr       (),
    .rvfi_rs1_rdata      (),
    .rvfi_rs2_rdata      (),
    .rvfi_rd_addr        (),
    .rvfi_rd_wdata       (),
    .rvfi_mem_addr       (),
    .rvfi_mem_rmask      (),
    .rvfi_mem_wmask      (),
    .rvfi_mem_rdata      (),
    .rvfi_mem_wdata      (),
    .rvfi_trap_cause     (),
    .rvfi_bp_pred_taken  (),
    .rvfi_bp_pred_target (),
    .rvfi_bp_mispredict  ()
);
```

The memories must meet the contract in "Memory Contract". The CLINT is not part of `peregrine_core`; a cacheless system that needs timer and software interrupts drives `irq_timer` and `irq_software` itself.

## Cached Instantiation Checklist

- Connect the `m_axi_*` port to a fabric slave that returns the id it was given, supports INCR bursts of a whole line, and has the RAM at `RESET_ADDR` and the I/O devices in 0x1000_0000-0x1FFF_FFFF.
- Tie `tb_irq_software`, `tb_irq_timer` and `dc_clean_req` to 0; leave `dobs_*` and `dc_clean_done` open.
- Drive `irq_external` from the system's interrupt controller (level).
- Point the boot image at `RESET_ADDR`; the I\$ fetches it from the fabric on the first miss.
- Leave `DC_SETS`, `DC_WAYS`, `DC_LINE`, `ICACHE_BYTES` and `ICACHE_LINE` at their defaults unless you re-verify: those are the geometries peregrine was gated and timed at.

## Software Notes

- Set `mtvec` before enabling interrupts; it is direct mode only (bits 1:0 read 0).
- Use `fence.i` after writing code, in both builds.
- Read the data a TB or debugger needs from memory only after a `fence.i` or a `dc_clean_req` clean: amber is write-back, so stores may still be in the cache.
- `mstatus.MIE` is cleared on trap entry; nested interrupts need the handler to save `mepc` and `mcause` and set MIE itself.

---

**Last Updated:** 2026-11-25
