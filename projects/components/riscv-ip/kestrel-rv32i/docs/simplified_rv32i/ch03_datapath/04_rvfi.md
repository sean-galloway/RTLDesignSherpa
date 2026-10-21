# The RVFI Retire Interface

## Retirement as the observation channel

kestrel was built RVFI-first: the retire port is not debug instrumentation
bolted on afterward but the core's defined observation channel, present
from the first vertical slice. Every instruction that retires produces
one beat; the halting instruction produces one final trap beat; nothing
else produces anything. A cocotb testbench diffs these beats field by
field against a golden interpreter, and riscv-formal relates them to an
instruction-set model (Chapter 6). Both consumers need the aggregation
rules below to be exact.

## The signal table

| Signal | Width | kestrel semantics |
| --- | --- | --- |
| `rvfi_valid` | 1 | High exactly on cycles a beat retires: `rst_n & ~halt_q & ~mem_wait` |
| `rvfi_order` | 64 | `retire_count`; 0, 1, 2, ... over retired beats |
| `rvfi_pc_rdata` | 32 | The retiring instruction's PC |
| `rvfi_pc_wdata` | 32 | `next_pc` — the architecturally next PC (the misaligned target on a cause-3 halt) |
| `rvfi_insn` | 32 | The instruction word |
| `rvfi_trap` | 1 | `halt_now`: high on the single halting trap beat |
| `rvfi_rs1_addr` / `rvfi_rs2_addr` | 5+5 | Register-file read ports (`insn[19:15]`, `insn[24:20]`) |
| `rvfi_rs1_rdata` / `rvfi_rs2_rdata` | 32+32 | Read data; x0 reads zero naturally |
| `rvfi_rd_addr` / `rvfi_rd_wdata` | 5+32 | Writeback, when `rd_wb`; both zero otherwise |
| `rvfi_mem_addr` | 32 | The word address of a load/store, zero otherwise (and on a misaligned, halting access) |
| `rvfi_mem_rmask` / `rvfi_mem_wmask` | 4+4 | The byte lanes the access covers within that word |
| `rvfi_mem_rdata` / `rvfi_mem_wdata` | 32+32 | The raw word read (loads) / size-truncated store data shifted into its lanes, zero otherwise |

: RVFI signals and their kestrel aggregation

## The three gating rules

Three qualifications turn the raw datapath signals into a clean retire
stream:

1. **x0 reports zero.** `rd_wb = rd_wen & (insn[11:7] != 0) & ~halt`, so
   a beat writing x0 reports `rd_addr = 0` with `rd_wdata = 0`. This is
   not merely tidiness: riscv-formal requires `rd_wdata == 0` whenever
   `rd_addr == 0`, and the early core failed exactly there until the rule
   was pinned. The register file independently discards the x0
   write architecturally.
2. **A wait cycle is silent.** While a block-RAM memory holds the core
   with `mem_wait` (a load's first cycle), `rvfi_valid` is low: the
   instruction reports one beat, on the cycle it completes.
3. **Halt retires one trap beat, then silence.** `rvfi_trap = halt_now`
   marks the halting instruction itself (ecall, ebreak, illegal,
   misaligned target, or misaligned load/store) — a beat with trap set, no rd write, no memory
   fields — after which the latched `halt_q` holds `rvfi_valid` low
   forever. The wrapper used by riscv-formal derives `rvfi_halt =
   rvfi_valid & halt`, which matches the semantic exactly: the trap beat
   is the final retirement.

## Memory-field packing

kestrel follows riscv-formal's `RISCV_FORMAL_ALIGNED_MEM` convention:
`rvfi_mem_addr` is the word address and the masks mark the byte lanes the
access covers inside it, the same lanes the store strobes drive. A load
reports the raw word; a store reports its value truncated to the access
size and shifted into its lanes, not the raw register — leaking the upper
bytes into the payload is a real bug class this encoding prevents. (When
kestrel still completed misaligned accesses in hardware it reported the
unaligned byte address with masks packed from bit 0, riscv-formal's other
convention.)

## Why this pays

Because the rules are few and stated in RTL comments next to the
assignments, the golden interpreter models the same rules in Python and
the two can be diffed beat for beat over tens of thousands of
instructions with zero tolerance. When a diff appears, it names the
cycle, the PC, and the field — which is how the misaligned-jump defect
of Chapter 6 was localized from a formal counterexample in minutes
rather than debugged from waveforms.

**Source:** `rtl/top/kestrel_core.sv` (RVFI aggregation block);
vendor/riscv-formal/docs/rvfi.md; `dv/tbclasses/kestrel/rv32i_interpreter.py`
