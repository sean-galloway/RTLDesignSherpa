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

# kestrel-rv32i Testplans

YAML testplans mapping every kestrel FUB and the core top to the cocotb/pytest
tests that exercise them. Format mirrors the pumice/retro_legacy_blocks
testplan convention so the same coverage rollup applies
(`bin/cov_utils/functional_coverage_tracker.py`).

## Inventory

| Testplan | Module | Test file(s) | Scenarios | Verified | Not impl. |
|----------|--------|--------------|----------:|---------:|----------:|
| `kestrel_regfile_testplan.yaml` | kestrel_regfile.sv | test_kestrel_regfile.py | 5 | 5 | 0 |
| `kestrel_alu_testplan.yaml` | kestrel_alu.sv | test_kestrel_decode.py | 5 | 5 | 0 |
| `kestrel_imm_gen_testplan.yaml` | kestrel_imm_gen.sv | test_kestrel_decode.py | 6 | 5 | 1 |
| `kestrel_decode_testplan.yaml` | kestrel_decode.sv | test_kestrel_decode.py | 12 | 11 | 1 |
| `kestrel_mem_loader_testplan.yaml` | kestrel_mem_loader.sv | test_kestrel_mem_loader.py | 9 | 7 | 2 |
| `kestrel_core_testplan.yaml` | kestrel_core.sv | test_kestrel_{core,branch,ls,rv32ui,mem_loader}.py | 18 | 16 | 2 |
| **Total** | | | **55** | **49** | **6** |

Not-implemented scenarios and why:

- **IG-06** — randomized immediate sweep vs `imm_golden` (directed vectors
  cover all 5 formats both signs today).
- **DEC-11** — CSRRC / CSRRSI / CSRRCI stub forms have no golden-table row
  (CSRRW / CSRRS / CSRRWI do).
- **ML-08** — AXIL skid backpressure / busy-tap behavior.
- **ML-09** — loader write issued after CTRL.run must not touch the arrays.
- **CORE-17** — randomized instruction-stream fuzz vs spike lockstep
  (**Phase C**).
- **CORE-18** — functional coverage closure / cover model (**Phase C**).

## What each plan covers

- **RF (kestrel_regfile)**: reset-to-zero, write/readback on both ports,
  read-during-write old-value, x0 discard, independent port addressing
  (attributed to the core-level golden trace, RF-05).
- **ALU (kestrel_alu)**: exhaustive 10-op x 16-value x 16-value golden-model
  sweep including shamt=`b[4:0]`, signed/unsigned compare flags. The flags
  are unconnected inside kestrel_core by design (branch comparator is
  separate) — verified at unit level only.
- **IG (kestrel_imm_gen)**: I/S/B/U/J immediate assembly and sign extension
  with directed ±vectors; B/J LSB-zero rule.
- **DEC (kestrel_decode)**: the 45-encoding golden truth table (37 canonical
  RV32I + mret + fence/fence.i + ecall/ebreak + 3 CSR-stub forms), illegal /
  reserved encodings landing on halt cause 0xF, ecall/ebreak causes 1/2.
  Halt cause 3 (IALIGN) is decode-invisible by design and lives in the CORE
  plan (CORE-13).
- **ML (kestrel_mem_loader)**: AXIL window over both 64 KB regions, per-byte
  wstrb merge, CTRL.run readback/release sequencing, load-mode isolation
  (core_rst_n hold, parked PC, no retirement), core↔dmem cross-mux both
  directions, run-mode observability through the AXIL port, and the
  golden-trace board path (battery images streamed over AXIL with spike
  lockstep).
- **CORE (kestrel_core)**: ISA classes via golden trace, branches/jumps
  (incl. IALIGN halt cause 3), loads/stores incl. the cross-word 2-cycle
  retry, the system layer (FENCE NOPs, ECALL/EBREAK halt+hold, illegal
  halt, trap-beat shape), RVFI invariants, the 42-image rv32ui battery, and
  spike lockstep. Phase C gaps (fuzz, coverage closure) are tracked as
  not_implemented.

## JUnit naming convention (observed)

Kestrel's pytest wrappers launch one Verilator build per (cocotb testcase,
test level) cell; each cell writes a cocotb JUnit XML whose testcase
`name` is the **cocotb test function name**, with the pytest module as
`classname`:

```
<testcase name="cocotb_test_kestrel_core_focus" classname="test_kestrel_core" .../>
```

So `test_function` strings in these plans quote the `cocotb_test_*` node
names exactly (e.g. `cocotb_test_kestrel_branch_all`,
`cocotb_test_kestrel_rv32ui_battery`). They match the tracker by exact
name — there are no pytest-parametrized `[case-level]` node names in the
cocotb XML.

Results XML layout: the wrappers set `COCOTB_RESULTS_FILE` to
`dv/tests/logs/results_<testcase>_<level>.xml`. The archived run artifacts
checked in today live one level down at
`dv/tests/local_sim_build/<testcase>_<level>/<rand>_results.xml` with
identical testcase names. To feed the tracker from archived artifacts,
flatten them first:

```bash
cd projects/components/riscv-ip/kestrel-rv32i/dv/tests
find local_sim_build -name '*_results.xml' -exec cp {} logs/ \;
```

## Rollup

```bash
# From the repo root, after a regression (or after flattening archived XMLs
# into dv/tests/logs/ as above):
python3 bin/cov_utils/functional_coverage_tracker.py \
    --testplans-dir projects/components/riscv-ip/kestrel-rv32i/dv/testplans \
    --report \
    --results-dir projects/components/riscv-ip/kestrel-rv32i/dv/tests/logs
```

The `implied_coverage` block in each YAML is the functional-coverage
contribution: `scenario_tracked` counts `status: verified` scenarios,
`implied_percentage = tracked / total_scenarios`.

## Running the tests

```bash
cd projects/components/riscv-ip/kestrel-rv32i/dv/tests
make list                     # discovered test roots
make run-all-func-parallel    # FUNC regression (gate+func cells)
make run-all-full-parallel    # FULL regression (gate+func+full cells)
```

REG_LEVEL semantics: GATE runs gate cells only, FUNC adds func, FULL adds
full. The rv32ui battery reads TEST_LEVEL inside the sim (gate = 3-image
smoke, func = 42 images + spike lockstep, full = 42 images without
lockstep).
