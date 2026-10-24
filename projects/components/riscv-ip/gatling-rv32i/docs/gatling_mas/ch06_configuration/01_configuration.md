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


# Configuration

| Item | Where | Value |
|---|---|---|
| `RESET_ADDR` | gatling_core parameter | 0 (board and battery: 0x8000_0000) |
| `MEM_WORDS` | gatling_mem_bram parameter | 4096 per context (16 KB) |
| `NUM_HARTS` | gatling_core, gatling_regfile, gatling_mem_bram parameter | 4 (the tetrad). At least the pipeline depth (4): fewer contexts than stages would put two instructions of one context in flight. More is legal (each context then owns 1/NUM_HARTS of the datapath); the rotation counter wraps explicitly, so a power of two is not required. gatling_mem_bram caps it at 16 (its per-context register block) and checks that the bank field fits below the register address bit. Both checks are elaboration-time `$error`s |

: Table 6.1: Configuration surface

Filelists (`rtl/filelists/`): `fub/gatling_regfile.f`, `fub/gatling_mem_bram.f`, `top/gatling_core.f` (pulls the common-rv32i decode/imm_gen/ALU filelists, which bring `rv32i_pkg` with them), `gatling_all.f`. The root variable is `GATLING_ROOT`; `RV32I_COMMON_ROOT` must also be set. There is no gatling package: the barrel adds no ISA vocabulary of its own.
