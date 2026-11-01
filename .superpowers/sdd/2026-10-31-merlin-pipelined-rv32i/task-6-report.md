# Task 6 Report: merlin riscv-formal retire checks

## Status: DONE_WITH_CONCERNS

A working `formal/merlin/riscv-formal/` harness was created, mirroring kestrel's flow.
The full suite runs to completion: **41/42 checks PASS**; `reg_ch0` FAILS with a
counterexample that exposes a real pipeline forwarding bug for CSR-immediate
instructions.

Per the task rule, `merlin_core` was **not patched**.

## Files created

- `formal/merlin/riscv-formal/Makefile`
- `formal/merlin/riscv-formal/checks.cfg`
- `formal/merlin/riscv-formal/formal_merlin.sv`
- `formal/merlin/riscv-formal/.gitignore`

## Harness adaptations vs. kestrel

1. **Pipelined reset/retire timing**: merlin is a 5-stage pipeline plus a
   3-cycle boundary reset synchronizer, so the first instruction retires at
   cycle 7.  Depths were raised from kestrel's `6` to `10` (insn/consistency)
   and liveness/unique trigger at cycle 8:
   ```
   insn       10
   reg        4  10
   pc_fwd     4  10
   pc_bwd     4  10
   liveness   1  8  30
   unique     1  8  30
   ```
2. **MERLIN_ROOT**: the shared `make/formal_flat.mk` does not export
   `MERLIN_ROOT` yet, so the Makefile sets it via `override export` before
   including `formal_flat.mk`.
3. **RVFI source-register masking**: merlin (like kestrel) drives
   `rvfi_rs1_addr`/`rvfi_rs2_addr` from the encoding bits unconditionally.
   In the pipeline this causes riscv-formal's `reg` check to interpret
   encoding-bit coincidences (e.g. LUI bits [19:15]) as architectural reads.
   The wrapper corrects this by zeroing `rvfi_rs1_addr`/`rvfi_rs2_addr` and
   their data for instructions that do not use those sources (LUI/AUIPC/JAL,
   CSR-immediate, FENCE, ECALL/EBREAK/MRET, etc.).
4. **Memory timing**: `mem_wait` is left as a bounded free input, identical to
   kestrel, with at most two consecutive wait cycles.

## Failing check: `reg_ch0`

```
SBY  ...  [reg_ch0] engine_0: BMC failed!
SBY  ...  [reg_ch0] engine_0: Value for anyconst rvfi_testbench.insn_order: 1
SBY  ...  [reg_ch0] engine_0: Value for anyconst rvfi_testbench.register_index: 30
SBY  ...  [reg_ch0] engine_0: Assert failed in rvfi_testbench: rvfi_reg_check.sv:42
```

### Counterexample summary

| Cycle | Retire | Instruction | Effect |
|------:|-------:|-------------|--------|
| 8     | order 0 | `0x81dfff73` = `csrRCI x30, 0x81d, 31` | Writes **0** to `x30` (CSR stub: unknown CSR reads as 0) |
| 9     | —       | stalled by `mem_wait` | pipeline bubble |
| 10    | order 1 | `0x81df3333` = `sltu x6, x30, x29` | Reads `x30`; expected 0, got `0xffe7fffc` |

The `reg` check shadows `x30` = 0 from the CSRRCI write and then asserts that
`sltu`'s `rvfi_rs1_rdata` equals that shadow.  The returned value is the
**garbage ALU output of the CSRRCI instruction** (`0xffffffff + 0xffe7fffd =
0xffe7fffc`), forwarded from EX/MEM to the dependent `sltu` in EX.

### Root cause

For CSR-immediate instructions `merlin_core` sets `csr_stub = 1` and writes
`0` to the destination register in WB, but the ALU still computes
`rs1 + rs2` using the interpreted register operands.  The pipeline's
forwarding path forwards that garbage ALU result (`ex_mem_q.alu_y`) to any
instruction in EX that reads the same destination register.  The dependent
instruction therefore sees the ALU garbage, not the architecturally-correct
`0`.

This is a pipeline-specific bug: kestrel's single-cycle/register-file-read-at-
retire timing reads `x30` after the synchronous write and naturally sees `0`.

### Why this was not caught by rv32ui spike lockstep

CSR instructions are not part of the RV32I base ISA (they belong to Zicsr), so
the `rv32ui` test battery does not exercise them.

## Verification commands

```bash
export PATH=/mnt/data/tools/oss-cad-suite/bin:/mnt/data/tools:$PATH
make -C formal/merlin/riscv-formal clean
make -C formal/merlin/riscv-formal checks
```

Result:
```
riscv-formal merlin: 41/42 checks PASS
NOT PASS: reg_ch0: FAIL
```

## Gate checks

- `python3 bin/check_task_ids.py` — passed.
- `python3 bin/filelist_registry.py --check` — not needed (no new filelists).

## Concerns

- `reg_ch0` exposes a real pipeline forwarding bug for CSR-immediate
  instructions.  The fix belongs in `merlin_core` (e.g. force ALU output to 0
  for `csr_stub`, or forward the WB-stage value for CSR results); it was not
  applied per the "do not patch merlin_core" rule.
- Until that core fix lands, riscv-formal cannot report 42/42 PASS.
