# Spike Lockstep

## What lockstep adds

The golden interpreter checks kestrel against kestrel's own
understanding of RV32I — same author, same conventions, same blind
spots. Spike, the RISC-V emulator, is an independent implementation:
different code base, different authors, years of field use. Lockstepping
the two means an disagreement is almost certainly kestrel's bug, and the
suite pins spike 1.1.0 for reproducibility. Each battery test runs spike
on the same ELF and the runner walks the two retirement streams
together.

## The mechanics

Spike is invoked as `spike --isa=RV32I -l --log=<file> <elf>` — the `-l`
must accompany `--log`; `--log` alone redirects a disabled log and
produces an empty file. This pinned build's commit line carries pc and
instruction encoding only:

```
core   0: 0x0000000080000000 (0x00000297) auipc   t0, 0x0
```

There are no register-write or memory-access payloads in this build
(checked against the source: `processor_t::disasm` prints pc, insn, and
disassembly only). Consequently the lockstep is layered: the golden
interpreter's full-field beat diff owns rd/rs/mem correctness, and spike
owns the (pc, insn) retirement stream, the exception records, and the
exit code — an independent check that the right instructions executed in
the right order. Four format details are pinned by investigation:

1. **Boot prefix.** fesvr's boot ROM runs 5 instructions at 0x1000
   before jumping to the ELF entry; the diff skips records until the
   first commit at `e_entry`.
2. **`Executed N times` lines.** Spike collapses back-to-back identical
   (pc, insn) commits; the parser expands them before the walk.
3. **Exception records.** `core   0: exception <kind>, epc 0x<pc>` (plus
   a `tval` line) interleave with commits; the trapping instruction
   still gets its own commit line first. The walk verifies each such
   record against the just-matched core beat and spike's resume pc.
4. **Termination.** The core's final beat is the ecall trap beat; spike
   continues with the ecall commit and `trap_user_ecall` at the halt PC,
   then the p-environment's write_tohost tail (length varies per run —
   not diffed). The exit code is the verdict.

## The misaligned-build note

kestrel handles misaligned loads and stores in hardware (Chapter 5);
the *pinned* spike does not. spike 1.1.0 gates hardware misaligned
support behind the compile-time `RISCV_ENABLE_MISALIGNED` — there is no
runtime flag — so on the pinned binary `ma_data` exits 156 with
`trap_load/store_address_misaligned`. The battery therefore uses a
side-by-side rebuild of the *same spike 1.1.0 commit* at
`/mnt/data/tools/spike-misaligned/bin/spike`, configured
`--with-isa=rv32 --enable-misaligned` into its own prefix; the pinned
binary stays untouched. With the rebuild, `ma_data` passes with the
identical exception signature as the other 41 tests, and their streams
are unaffected (the aligned path is unchanged). Both tools live outside
the repository with the rest of the toolchain.

## The mnstatus divergence

Every test's p-environment preamble executes `csrwi mnstatus, 8` — a
Smrnmi CSR, illegal in RV32I per spike's default extension set. Spike
traps it and resumes at `mtvec`, which the p-environment points at the
next instruction; kestrel's CSR stub simply retires it (Chapter 2). The
1:1 stream walk stays aligned because spike logs the trapping
instruction's commit, the exception record is verified against the
just-matched core beat and spike's resume pc, and the event is counted
and reported as `1 stub trap(s) [trap_illegal_instruction]` per test.
Any *other* mid-stream exception is a hard failure — none ever
occurred.

**Source:** task-8 report (spike format notes 1-8, battery table);
`dv/tbclasses/kestrel/rv32ui_battery.py` (spike runner, log parser,
lockstep_diff)
