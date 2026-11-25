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

# Pipeline Registers

**Module:** `peregrine_if_id.sv`

The four boundary registers, `peregrine_if_id`, `peregrine_id_ex`, `peregrine_ex_mem` and `peregrine_mem_wb`, share one shape: a record in (`d_i`), a record out (`q_o`), `stall` and `flush`. The records are the `peregrine_pkg` structs ("Package Types and Encodings").

## Ports (all four)

<!-- GEN:ports:peregrine_if_id -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset (control fields) |
| `stall` | input | `1` | Hold the record |
| `flush` | input | `1` | Load the bubble record (wins over stall) |
| `d_i` | input | `peregrine_pkg::if_id_t` | Record in |
| `q_o` | output | `peregrine_pkg::if_id_t` | Record out |

: peregrine_if_id ports

<!-- /GEN -->

The four modules differ only in the record type on `d_i` / `q_o` (`if_id_t`, `id_ex_t`, `ex_mem_t`, `mem_wb_t`).

## Control Versus Payload

Each register splits its record:

- **Control fields** reset and flush to the bubble value (all zero) under the asynchronous reset.
- **The payload** is a plain enable flop: captured unless stalled, with no reset and no flush clear. A bubble carries a stale payload, and every consumer gates on `valid` or on a cleared control field. Putting an asynchronous clear on the payload cost about 680 reset flops and a LUT in front of each (riscv-ip common-rv32i ISSUE-001 row 2), which is why merlin split it.

| Register | Control fields |
|----------|----------------|
| IF/ID | `valid` |
| ID/EX | `valid`, `rd_wen`, `dmem_req`, `dmem_we`, `branch`, `jump`, `jalr`, `exc_cause`, `csr_op` |
| EX/MEM | `valid`, `rd_wen`, `dmem_req`, `dmem_we`, `ls_misalign`, `exc_cause`, `csr_op` |
| MEM/WB | `valid`, `rd_wen`, `exc_cause`, `trap` |

: Control fields per pipeline register

Flush wins over stall. The core never flushes MEM/WB.

---

**Last Updated:** 2026-11-25
