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
| `rvfi_valid` | 1 | High exactly on cycles a beat retires: `rst_n & ~halt_q & ~ls_first` |
| `rvfi_order` | 64 | `retire_count`; 0, 1, 2, ... over retired beats |
| `rvfi_pc_rdata` | 32 | The retiring instruction's PC |
| `rvfi_pc_wdata` | 32 | `next_pc` — the architecturally next PC (the misaligned target on a cause-3 halt) |
| `rvfi_insn` | 32 | The instruction word |
| `rvfi_trap` | 1 | `halt_now`: high on the single halting trap beat |
| `rvfi_rs1_addr` / `rvfi_rs2_addr` | 5+5 | Register-file read ports (`insn[19:15]`, `insn[24:20]`) |
| `rvfi_rs1_rdata` / `rvfi_rs2_rdata` | 32+32 | Read data; x0 reads zero naturally |
| `rvfi_rd_addr` / `rvfi_rd_wdata` | 5+32 | Writeback, when `rd_wb`; both zero otherwise |
| `rvfi_mem_addr` | 32 | The unaligned byte address of a load/store (`alu_y`), zero otherwise |
| `rvfi_mem_rmask` / `rvfi_mem_wmask` | 4+4 | Byte lanes touched, packed from bit 0 relative to `mem_addr` |
| `rvfi_mem_rdata` / `rvfi_mem_wdata` | 32+32 | Assembled access data (loads) / size-truncated store data, zero otherwise |

: RVFI signals and their kestrel aggregation

## The three gating rules

Three qualifications turn the raw datapath signals into a clean retire
stream:

1. **x0 reports zero.** `rd_wb = rd_wen & (insn[11:7] != 0) & ~halt`, so
   a beat writing x0 reports `rd_addr = 0` with `rd_wdata = 0`. This is
   not merely tidiness: riscv-formal requires `rd_wdata == 0` whenever
   `rd_addr == 0`, and the early core failed exactly there until the rule
   was pinned (Chapter 6). The register file independently discards the
   x0 write architecturally.
2. **The retry's first cycle is silent.** During the first beat of a
   cross-word access, `rvfi_valid` is low (`ls_first` masks it): no
   partial beat leaks out. The access reports one beat on its final
   cycle, with the full assembled data.
3. **Halt retires one trap beat, then silence.** `rvfi_trap = halt_now`
   marks the halting instruction itself (ecall, ebreak, illegal, or
   misaligned target) — a beat with trap set, no rd write, no memory
   fields — after which the latched `halt_q` holds `rvfi_valid` low
   forever. The wrapper used by riscv-formal derives `rvfi_halt =
   rvfi_valid & halt`, which matches the semantic exactly: the trap beat
   is the final retirement.

## Memory-field packing

For loads and stores, `rvfi_mem_addr` is the *unaligned* byte address
and the masks count byte lanes from bit 0 relative to that address — the
riscv-formal byte-i convention. A store's `rvfi_mem_wdata` is the store
value truncated to the access size (`rs2_data & ls_data_mask`), not the
raw register; leaking the upper bytes into the payload is a real bug
class this encoding exists to prevent, and one kestrel fixed when the
battery's ma_data-shaped vectors arrived.

## Why this pays

Because the rules are few and stated in RTL comments next to the
assignments, the golden interpreter models the same rules in Python and
the two can be diffed beat for beat over tens of thousands of
instructions with zero tolerance. When a diff appears, it names the
cycle, the PC, and the field — which is how the misaligned-jump defect
of Chapter 6 was localized from a formal counterexample in minutes
rather than debugged from waveforms.

**Source:** `rtl/kestrel_core.sv` (RVFI aggregation block);
vendor/riscv-formal/docs/rvfi.md; `dv/tbclasses/kestrel/rv32i_interpreter.py`
