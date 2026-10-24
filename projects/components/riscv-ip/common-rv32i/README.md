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

# common-rv32i

The RV32I pieces that are identical in every core built on the kestrel
ISA contract, kept once. kestrel (single-cycle) and gatling (barrel)
instantiate these blocks unchanged; a fix here is a fix to both.

| Block | File | What it is |
|---|---|---|
| `rv32i_pkg` | `rtl/includes/rv32i_pkg.sv` | XLEN, `alu_op_e`, `imm_sel_e`, the HALT_* cause encoding (single source of truth) |
| `rv32i_decode` | `rtl/fub/rv32i_decode.sv` | The `{opcode, funct3, funct7}` truth table to the control bundle; ecall/ebreak/illegal causes |
| `rv32i_imm_gen` | `rtl/fub/rv32i_imm_gen.sv` | The five immediate formats, selected by the major opcode alone |
| `rv32i_alu` | `rtl/fub/rv32i_alu.sv` | Ten operations, OR-combined zero-gated rows, one adder, one 33-bit compare; eq/lt/ltu flags |

All three blocks are combinational; the package has no state. The halt
causes a core raises itself (misaligned control-flow target, misaligned
load/store) are encoded here too, so one table covers decode and core.

## Consuming

Each block has its own complete-closure filelist under `rtl/filelists/`
(`rv32i_pkg.f`, `fub/rv32i_{alu,imm_gen,decode}.f`); `rv32i_common_all.f`
is the master. Consumers `-f` these through `$RV32I_COMMON_ROOT`
(registered in `env_python`, `bin/filelist_registry.py`,
`bin/TBClasses/shared/filelist_utils.py`, `make/formal_flat.mk`) and never
hand-list the sources -- see kestrel's `top/kestrel_core.f` and gatling's
`top/gatling_core.f`.

## Verification

`dv/tests/test_rv32i_decode.py` is the unit test of all three blocks
(exhaustive ALU golden model, immediate vectors plus a seeded sweep, the
48-encoding decode truth table with the reserved encodings); the three
testplans are under `dv/testplans/`. Run it the standard way:

```bash
cd projects/components/riscv-ip/common-rv32i/dv/tests
make clean-all && make run-all-func-parallel
```

The blocks are also proved in context by both cores' riscv-formal suites
(`formal/kestrel`, `formal/gatling`) and exercised by their rv32ui
batteries.

## Documentation

The block chapters live in the kestrel MAS
([`../kestrel-rv32i/docs/kestrel_mas/`](../kestrel-rv32i/docs/kestrel_mas/)
chapter 2: decode, imm_gen, ALU; chapter 3: the package), kestrel being
the reference consumer. The *Simplified RV32I* study book documents the
same decode table and ALU.

## History

Pulled out of `kestrel-rv32i` on 2026-10-22 when gatling became the second
consumer (it had been reaching into kestrel's filelists). The modules were
`kestrel_pkg`, `kestrel_decode`, `kestrel_imm_gen`, `kestrel_alu`; nothing
but the names and the paths changed.
