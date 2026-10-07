# IALIGN and the Misaligned-Target Halt

## The rule

With IALIGN=32 — no compressed instructions — every instruction fetch
must be 4-byte aligned. The spec (Volume I, section 2.1.5) therefore
requires an *instruction-address-misaligned* exception when taken
control flow — a taken branch, JAL, or JALR — targets an address whose
low two bits are not `00`. RISC-V's explicit permission to handle
*data* misalignment in hardware does not extend here: executing at a
misaligned instruction address is never an option.

## Why decode cannot catch it

The condition needs the *resolved* next PC: for JALR it depends on a
register value, and for every branch it depends on the taken decision.
Decode sees neither — it produces the control bundle, not the data.
kestrel's `kestrel_pkg` comments state the ownership directly: causes 1,
2, and `F` belong to decode; cause 3 belongs to the core. In
`kestrel_core.sv`:

```
misalign_target = (jump | jalr | branch_taken) & (next_pc[1:0] != 2'b00);
```

— OR-ed into the halt path as `HALT_IALIGN` (`4'h3`), through the same
holding register as every other halt: trap beat, writeback suppressed,
PC frozen, cause on the port.

## The writeback subtlety

JAL and JALR set decode's `rd_wen` — they are link instructions, and a
taken JAL/JALR that *does* align must write `pc+4`. The misaligned case
must not. Rather than teaching decode about alignment, the core gates
both the register write and the RVFI report with `halt` itself:
`rd_wen_eff = rd_wen & ~ls_first & ~halt` and
`rd_wb = rd_wen & (insn[11:7] != 0) & ~halt`. The trap beat reports the
misaligned target on `rvfi_pc_wdata` (it is `next_pc`, and `next_pc` is
the misaligned address), which is exactly what a real trap's state would
record as the faulting target — a detail the formal model checks
explicitly.

## The four halt causes, in context

| Cause | Encoding | Raised in | Spec's name for the event |
| --- | --- | --- | --- |
| ECALL | `4'h1` | decode | environment-call exception |
| EBREAK | `4'h2` | decode | breakpoint exception |
| misaligned control-flow target | `4'h3` | core | instruction-address-misaligned exception |
| illegal encoding | `4'hF` | decode | illegal-instruction exception |

: Halt causes and their spec counterparts

Every row is a case where RV32I mandates a trap and kestrel — having no
trap machinery — substitutes a halt with the cause on a port. The RVFI
trap beat keeps the event architecturally visible: riscv-formal's checks
require exactly this reporting, and the suite's later rungs replace the
halt with real trap delivery. This table is the seam.

## The fence_i connection

rv32ui-p-fence_i is the one battery test whose program modifies its own
instruction stream between fetches. The core's Harvard contract says
nothing about store-to-fetch visibility, so the *testbench* provides it:
one unified memory array serves `imem_rdata` and `dmem_rdata`, and
FENCE.I's NOP retirement is sufficient because there is no cache to
invalidate and no prefetch to refetch. The test passing is evidence of
the testbench's coherence choice, not of a core feature — and the book
says so because the distinction matters the moment a real cache enters
at rung 3.

**Source:** RISC-V Instruction Set Manual, Volume I, sections 1.5,
2.1.5; `rtl/includes/kestrel_pkg.sv` (cause encoding and ownership comment),
`rtl/top/kestrel_core.sv` (misalign_target, writeback gating),
`rtl/fub/kestrel_decode.sv`; task-9 report (the formal CEX that pinned this)
