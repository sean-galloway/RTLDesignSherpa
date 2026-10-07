# The System Layer: Stubs, NOPs, and Halts

## What RV32I surrounds itself with

The thirty-seven base instructions sit inside two opcode classes that
belong to the wider system: MISC-MEM (FENCE and friends, spec Volume I,
section 2.1.7, with FENCE.I split into the Zifencei extension, section
4.1) and SYSTEM (ECALL, EBREAK, and the CSR instructions of Zicsr,
section 4.2, with MRET defined in the privileged Volume II). kestrel has
no memory ordering hardware, no CSR file, and no trap handler, so these
classes retire through documented stubs and NOPs rather than real
machinery. This chapter states exactly what that means — including what
it does not mean.

## FENCE and FENCE.I retire as NOPs

kestrel's imem and dmem are separate, combinational-read ports on a
single-cycle core: there is no write buffer to drain, no cache to
invalidate, no instruction prefetch to refetch. Fence semantics are
therefore vacuous at this rung, and decode retires FENCE (MISC-MEM
funct3 000) and FENCE.I (funct3 001) as NOPs — one cycle each, no
architectural effect. MISC-MEM funct3 2-7 are reserved and halt as
illegal instructions.

One subtlety is worth pinning down because it surprises people: the
*core* is Harvard, but the *testbench memory* is a single unified array
that serves both fetch and load/store. That unification is a testbench
choice, made so rv32ui-p-fence_i's self-modifying code works with no
coherence path (see Chapter 6). It is not a core property, and the
book does not pretend otherwise: kestrel the core never sees its own
stores land in the instruction stream unless the memory system chooses
to show them.

## ECALL and EBREAK halt

ECALL and EBREAK exist to transfer control to an execution environment
(spec Volume I, section 2.1.8). kestrel has no execution environment
beyond halt-and-observe, so both halt the core: ECALL with cause
`4'h1`, EBREAK with cause `4'h2`. The halting instruction retires as an
RVFI trap beat. In practice ECALL is the suite's program-termination
convention: every riscv-tests program ends in the p-env's
`RVTEST_PASS`/`RVTEST_FAIL` sequence, whose final `ecall` is how kestrel
knows the program is done (Chapter 6 reads the verdict off the `gp`
register's last writeback).

## MRET falls through

MRET (SYSTEM funct3 000, imm12 `0x302`) returns from a machine trap. It
is meaningful only when traps exist — trap state, `mepc`, privilege
transfers, all of which are rung-3 machinery (privileged Volume II,
chapter 3). kestrel retires MRET as a documented NOP-with-fall-through:
the PC advances to pc+4. That choice is not arbitrary: the riscv-tests
p-environment points `mepc` at the instruction following its trap stub
in the configurations kestrel runs, so pc+4 is exactly what the test
expects. This is stated plainly so nobody mistakes it for trap support.

## The CSR class retires as a bounded stub

The six Zicsr instruction forms — CSRRW, CSRRS, CSRRC and their
immediate variants (SYSTEM funct3 001/010/011/101/110/111) — retire
through a stub: `csr_stub` in decode raises `rd_wen`, and the writeback
mux substitutes a hard zero. Reads return zero; writes drop on the
floor. SYSTEM funct3 100 is reserved and halts as illegal.

Say it plainly: **this is not CSR support.** There is no CSR file, no
`mstatus`, no `mtvec`, no counters, and nothing the instructions do has
architectural effect beyond a zero written to rd. The stub exists for
one bounded reason: the riscv-tests p-environment preamble executes
about a dozen CSR instructions plus an MRET before every test body, and
without the stub the battery cannot run at all. On the battery programs
the only CSR read with rd != x0 is `mhartid` (value 0), which the stub
matches. Anything needing real CSR state — trap handlers, counters,
feature probing — is out of contract at this rung and fails loudly
either as a zero where a nonzero was expected or as a program that
halts where it should have trapped.

The honesty matters for the ladder: merlin inherits the same stub, and
peregrine replaces it with a real machine-mode CSR file. The seam is
deliberately visible in the decode table.

## Halt causes, collected

| Cause | Name | Raised by | Spec would say |
| --- | --- | --- | --- |
| `4'h1` | HALT_ECALL | decode, ECALL | environment call |
| `4'h2` | HALT_EBREAK | decode, EBREAK | breakpoint |
| `4'h3` | HALT_IALIGN | core, misaligned taken control transfer | instruction-address-misaligned trap |
| `4'hF` | HALT_ILL | decode, default row | illegal instruction |

: The four halt causes (encoding centralized in `rtl/includes/kestrel_pkg.sv`)

Causes 1, 2, and `F` come from decode; cause 3 can only be raised by the
core, because it needs the resolved next PC and the branch decision that
decode cannot see. Chapter 5 develops cause 3 and the IALIGN rule behind
it.

**Source:** RISC-V Instruction Set Manual, Volume I, sections 2.1.7,
2.1.8, 4.1, 4.2; Volume II, chapter 3 (MRET, machine trap state);
`rtl/fub/kestrel_decode.sv`, `rtl/top/kestrel_core.sv`, `rtl/includes/kestrel_pkg.sv`
