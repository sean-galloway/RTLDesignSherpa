# TASK-001: rv32i_alu -- one adder and one shifter

**Priority:** P2
**Status:** CLOSED (2026-11-19)
**Owner:** Claude (owner: "do the next steps, please", 2026-11-19)
**From:** [ISSUE-001](../../issue/closed/ISSUE-001.md) row 1

## What

`rtl/fub/rv32i_alu.sv` built three 32-bit barrel shifters (SLL, SRL, SRA)
and a 33-bit compare for SLT/SLTU beside the add/sub adder. It is 374 LUT
in every core, the largest single block in each.

The rewrite keeps the ports and the OR-combined result:

- one 33-bit adder serves ADD, SUB, SLT and SLTU; bit 32 of the extended
  difference is the SLT/SLTU result;
- one right shifter serves SRL, SRA and SLL; SLL bit-reverses the operand in
  and the result out.

The `eq` / `lt` / `ltu` flag ports keep their own compares (unconnected in
all three cores).

## Evidence before the change (ISSUE-001 report)

| Core | LUT before | LUT with the variant | WNS before -> after |
|---|---|---|---|
| kestrel | 1,149 | 843 | +0.388 -> +1.233 |
| merlin | 1,583 | 1,378 | -0.141 -> +0.227 |
| gatling | 1,538 | 1,307 | +0.464 -> +0.204 |

Equivalence: 2,001,280 vectors, original vs variant, 0 mismatches; the
mutation (SRA fill disabled) gave 96,990.

## Gates

- [x] Suites, `make clean-all && make run-all-full-parallel`, every build
  dir newer than the edit: common-rv32i 9/9, kestrel 63/63, gatling 42/42,
  merlin 54/54.
- [x] riscv-formal, `make -C formal/<core>/riscv-formal checks`, flats
  regenerated from the tree (they carry `w_sum` / `sh_out_rev`): kestrel
  42/42, merlin 42/42, gatling 42/42.

## Result (routed OOC from the tree, xc7a100t-1, 10 ns)

| Core | LUT before -> after | WNS before -> after |
|---|---|---|
| kestrel | 1,149 -> 843 (-306, -27%) | +0.388 -> +1.233 |
| merlin | 1,583 -> 1,378 (-205, -13%) | -0.141 -> +0.227 |
| gatling | 1,538 -> 1,308 (-230, -15%) | +0.464 -> +0.190 |

The tree numbers match the A/B variant to one LUT. gatling's slack moved
down 0.27 ns; its worst path is outside the ALU (ISSUE-001 report), so the
change is placement, and gatling still meets 10 ns.

Also in this commit: merlin-rv32i `dv/tests/Makefile` and `conftest.py`,
copied from gatling's. merlin was the only riscv-ip core with no area
Makefile, so it could not run `make run-all-full-parallel`.
