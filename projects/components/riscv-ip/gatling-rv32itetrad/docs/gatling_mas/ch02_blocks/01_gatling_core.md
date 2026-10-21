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


# gatling_core

## Purpose

The barrel core: the rotation, four PCs, per-context halt and run control, the stage registers between F, D, X and W, and the RVFI retire port. It instantiates kestrel's decode, immediate generator and ALU, and `gatling_regfile`.

## Interface

| Port | Dir | Stage | Description |
|---|---|---|---|
| `clk`, `rst_n` | in | | Clock; asynchronous-assert reset, synchronized internally (`reset_sync`, N=3) |
| `hart_run[3:0]` | in | all | Per context: 1 = run, 0 = hold at RESET_ADDR (kills any of its instructions in flight) |
| `imem_ctx`, `imem_addr` | out | F | Fetch request: context and PC |
| `imem_rdata` | in | D | The fetched word, one cycle after the request (registered read) |
| `dmem_req`, `dmem_ctx`, `dmem_addr`, `dmem_wstrb`, `dmem_wdata` | out | X | Data access; `dmem_addr` is word-aligned, strobes and data lane-rotated |
| `dmem_rdata` | in | W | The load word, one cycle after the request |
| `halted[3:0]`, `halt_cause[3:0][3:0]` | out | | Per-context halt state (kestrel_pkg causes) |
| `rvfi_*`, `rvfi_ctx` | out | W | One retirement per cycle at most, tagged with its context; `rvfi_order` counts that context's retirements |

: Table 2.1: gatling_core ports

Parameter: `RESET_ADDR` (default 0; the board and the rv32ui battery use 0x8000_0000).

## The stages

| Stage | Context | Work | Registers out |
|---|---|---|---|
| F | `sel_q` | PC of the context to the instruction RAM | `d_valid`, `d_ctx`, `d_pc` |
| D | `d_ctx` | Fetched word decoded (kestrel_decode) and its immediate built (kestrel_imm_gen); register read issued with `{d_ctx, rs1}`, `{d_ctx, rs2}`; PC+imm and PC+4 formed | control bundle, `x_pc_imm`, `x_pc4`, `x_imm`, `x_insn` |
| X | `x_ctx` | Operands arrive from the register file; ALU, branch comparator, next PC, misalignment and halt; data access issued; the context's PC (or halt) written | `w_*`: the writeback value, load selectors, RVFI fields |
| W | `w_ctx` | Load word arrives, aligned and extended; register write `{w_ctx, rd}`; RVFI beat | |

: Table 2.2: Work per stage

PC+imm and PC+4 are formed in D because both operands are known there, which keeps the adders off X; X only selects.

## Per-context state

`pc_q[c]`, `halted_q[c]`, `cause_q[c]` and `order_q[c]` are the only per-context state besides the register file. `hart_run[c]` low wins every update: the PC returns to RESET_ADDR and the halt and order clear. Otherwise the X stage updates the context it holds -- its PC to the next PC, or, if the instruction halts, its halt bit and cause (the PC is not advanced, as kestrel).

Validity is carried per stage (`d_valid`, `x_valid`, `w_valid`) and re-qualified by `hart_run` of the stage's context at every stage, so stopping a context kills its in-flight instruction in whichever stage holds it: no store, no PC update, no register write, no retirement.

## Halts (context-lock)

The X stage raises a halt for decode's causes (ecall, ebreak, illegal -- including the not-yet-built Xcell custom-0 opcode), a misaligned control-flow target (IALIGN=32) and a misaligned load or store, exactly as kestrel. The halting instruction retires as an RVFI trap beat in W -- the same cycle `halted[c]` rises -- with no register write and no memory access. The context's next F slot sees `halted_q[c]` and fetches nothing; the other three contexts are unaffected.
