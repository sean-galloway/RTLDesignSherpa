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

# common-rv32i Testplans

YAML testplans for the three shared RV32I blocks, in the same format as
kestrel's (`../../kestrel-rv32i/dv/testplans/README.md`), so the same
coverage rollup applies (`bin/cov_utils/functional_coverage_tracker.py`).

| Testplan | Module | Test file | Scenarios |
|----------|--------|-----------|----------:|
| `rv32i_alu_testplan.yaml` | rv32i_alu.sv | test_rv32i_decode.py | 5 |
| `rv32i_imm_gen_testplan.yaml` | rv32i_imm_gen.sv | test_rv32i_decode.py | 6 |
| `rv32i_decode_testplan.yaml` | rv32i_decode.sv | test_rv32i_decode.py | 12 |

Moved from kestrel 2026-10-22 together with the blocks; scenario IDs and
the `covers` line references are unchanged.
