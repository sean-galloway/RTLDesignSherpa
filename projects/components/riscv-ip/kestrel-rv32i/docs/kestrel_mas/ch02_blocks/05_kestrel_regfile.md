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

# kestrel_regfile

## Purpose

`kestrel_regfile` is the 32 x 32-bit general-purpose register file: two combinational read ports, one synchronous write port, and the architectural x0 rule enforced in hardware. It has no reset (2026-10-20): the array is plain storage and maps to distributed RAM instead of 1,024 flops. Reads are combinational because the single-cycle design cannot afford a read latency; the write commits on the clock edge.

## Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | Clock (no reset port) |
| `rs1_addr` / `rs1_data` | Input / Output | 5 / 32 | Read port 1 (combinationally `regs[rs1_addr]`, zero for address 0) |
| `rs2_addr` / `rs2_data` | Input / Output | 5 / 32 | Read port 2 |
| `rd_addr` / `rd_data` / `rd_wen` | Input / Input / Input | 5 / 32 / 1 | Write port; committed on the edge when `rd_wen` and `rd_addr != 0` |

: kestrel_regfile interface

## Internal Structure and Rules

- Storage is `logic [31:0] regs [32]` with `ram_style = "distributed"` and **no reset**: a register is undefined until written, and keeps the previous program's value across a reload. Every program initializes each register it reads (the riscv-tests p-env does, with `INIT_XREG`; kestrel's golden interpreter raises `UninitializedRegisterRead` on any test that does not).
- **No x0 rule here.** Entry 0 is ordinary storage and the read ports have no zero-select (2026-10-20). kestrel_core keeps x0 zero by *writing* it: in reset it writes zero to entry 0 (reset_sync holds the internal reset for at least three clocks), and any instruction that targets x0 writes zero, through the writeback mux's existing zero row. So x0 reads zero with no logic on the register-read path, which is on the critical path. The stored-zero idea comes from the BRISKI barrel core; kestrel does it init-by-write per the house SRAM rule, not with an `initial` block. riscv-formal checks `rs*_rdata == 0` for x0 on every instruction (and fails every check if the reset write is removed).
- The core drives this port: `rd_wen = rd_wen_eff | ~reset`, `rd_addr = reset ? 0 : insn[11:7]`, with `rd_wen_eff` gating memory-wait and halting cycles — see the kestrel_core chapter.
- No write-forwarding exists: a write commits on the edge and is readable the next cycle. This is exactly the single-cycle contract (a store is visible to the next cycle's load *through the memory*; a register write is visible to the next instruction *through the register file*).

---

**Last Updated:** 2026-10-20
