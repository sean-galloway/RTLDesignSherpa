# Task 6 Report: DV runs + AXI3 Review-Focus supplements

## Summary

Validated the AXI3 slave-adapter generator fix, regenerated all affected AXI3
slave adapters, ran the four generated AXI3 bridge tests and the four
Review-Focus supplement tests at `REG_LEVEL=GATE`, and ran the bridge generator
package test suite.  All targeted tests pass.  The work is committed in two
clean commits.

## Root cause and generator fix

File: `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/generators/slave_adapter_generator.py`

The AXI4-to-AXI3 converter inside the slave adapter wired `s_axi_awready`,
`s_axi_arready`, and `s_axi_rlast` directly to the crossbar-facing `xbar_*`
nets.  The same adapter also drives those nets through the existing bridge_id
FIFO not-full gating logic (`w_sub_*ready`).  Verilator flagged this as
`MULTIDRIVEN` and, with `--assert`, treated it as an error.

Fix:
- In non-monitored (direct) mode, capture the converter ready outputs on
  internal `converter_awready` / `converter_arready` and capture `s_axi_rlast`
  on `converter_rlast`.
- Feed the captured ready signals into the existing `w_sub_*ready` plumbing so
  the bridge_id FIFO not-full status still gates the crossbar-facing ready.
- In monitored mode, the `axi4_master_*_mon` wrapper already provides gated
  ready/rlast on the intermediate nets, so the converter continues to connect
  directly to those nets.

Five AXI3 slave adapters were regenerated and updated:
- `bridge_1x2_axi3/s0_adapter.sv`
- `bridge_1x2_axi3_mon/s0_adapter.sv`
- `bridge_2x2_axi3_slaves/ddr_axi3_adapter.sv`
- `bridge_2x2_axi3_slaves/sram_axi3_adapter.sv`
- `bridge_mix_e/ddr_axi3_adapter.sv`

Generator consistency was verified by running the full bulk regeneration from
`projects/components/fabric-gen-ip/bridge/bin`:

```bash
source $REPO_ROOT/env_python
make all   # equivalent to python3 bridge_generator.py --bulk bridge_batch.csv
```

The bulk regen produced no additional diffs beyond the five adapters already
changed; `git status` on the generated trees showed no remaining modifications.
Declaration-order checks also passed for every regenerated adapter.

## Test results

### Decl-order check on regenerated adapters

```bash
venv/bin/python bin/check_sv_decl_order.py \
  projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_1x2_axi3/s0_adapter.sv \
  projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_1x2_axi3_mon/s0_adapter.sv \
  projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_2x2_axi3_slaves/ddr_axi3_adapter.sv \
  projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_2x2_axi3_slaves/sram_axi3_adapter.sv \
  projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_mix_e/ddr_axi3_adapter.sv
```

Result: `Checked 5 file(s) - no declaration order issues found`

### Generated AXI3 bridge tests at GATE

```bash
cd projects/components/fabric-gen-ip/bridge/dv/tests
PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src REG_LEVEL=GATE \
  python3 -m pytest test_bridge_1x2_axi3.py test_bridge_2x2_axi3_masters.py \
                   test_bridge_2x2_axi3_slaves.py test_bridge_mix_e.py -v
```

Result: **11 passed in 58.46s**

### AXI3 Review-Focus supplement tests at GATE

Created / validated:
- `test_bridge_1x2_axi3_chunk.py` (>16-beat bursts to AXI3 slave)
- `test_bridge_1x2_axi3_multioutstanding.py` (same-ID outstanding reads +
  ordered multi-ID writes)
- `test_bridge_2x2_axi3_masters_wideburst.py` (32-bit AXI3 master to 64-bit
  fabric)
- `test_bridge_1x2_axi3_lock.py` (AxLOCK=2'b10 pass-through)

Level-profile depth knobs added in `dv/tbclasses/bridge_levels.py`:
`outstanding_count`, `write_id_count`, `wideburst_beats`, `chunk_beats`,
`lock_repeats`.

```bash
cd projects/components/fabric-gen-ip/bridge/dv/tests
PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src REG_LEVEL=GATE \
  python3 -m pytest test_bridge_1x2_axi3_chunk.py \
                   test_bridge_1x2_axi3_lock.py \
                   test_bridge_1x2_axi3_multioutstanding.py \
                   test_bridge_2x2_axi3_masters_wideburst.py -v
```

Result: **4 passed in 18.72s**

### Bridge generator package tests

```bash
source $REPO_ROOT/env_python
python3 -m pytest projects/components/fabric-gen-ip/bridge/bin/tests/test_generator_pkg.py -v
```

Result: **141 passed in 9.22s**

## Commits

1. `b3ed37fb0` — `fix(bridge): gate AXI3 slave adapter converter readies through bridge_id FIFO (GitHub #97)`
   - `projects/components/fabric-gen-ip/bridge/bin/bridge_pkg/generators/slave_adapter_generator.py`
   - `projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_1x2_axi3/s0_adapter.sv`
   - `projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_1x2_axi3_mon/s0_adapter.sv`
   - `projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_2x2_axi3_slaves/ddr_axi3_adapter.sv`
   - `projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_2x2_axi3_slaves/sram_axi3_adapter.sv`
   - `projects/components/fabric-gen-ip/bridge/rtl/generated/bridge_mix_e/ddr_axi3_adapter.sv`

2. `15116ad13` — `test(bridge): AXI3 Review-Focus supplements — chunk, ordering, wideburst, lock (GitHub #97)`
   - `projects/components/fabric-gen-ip/bridge/dv/tbclasses/bridge_levels.py`
   - `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_chunk.py`
   - `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_lock.py`
   - `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_axi3_multioutstanding.py`
   - `projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_2x2_axi3_masters_wideburst.py`
   - `.superpowers/sdd/2026-10-11-bridge-axi3-support/task-6-report.md`

## Constraints observed

- `PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src` used on every
  pytest run.
- Converter RTL under `projects/components/utility-ip/converters/rtl/` was not
  modified.
- Commits use explicit pathspecs; no unrelated files were staged.
- Full-directory regression was not run per instruction; the controller runs it
  separately.
