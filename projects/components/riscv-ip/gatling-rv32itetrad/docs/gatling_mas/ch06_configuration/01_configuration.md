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
| `NUM_HARTS`, `HART_W` | gatling_pkg localparams | 4, 2 -- not a free parameter: the rotation length is the stage count |

: Table 6.1: Configuration surface

Filelists (`rtl/filelists/`): `gatling_pkg.f` (pulls kestrel_pkg first), `fub/gatling_regfile.f`, `fub/gatling_mem_bram.f`, `top/gatling_core.f` (pulls kestrel's decode/imm_gen/ALU filelists), `gatling_all.f`. The root variable is `GATLING_ROOT`; `KESTREL_ROOT` must also be set.
