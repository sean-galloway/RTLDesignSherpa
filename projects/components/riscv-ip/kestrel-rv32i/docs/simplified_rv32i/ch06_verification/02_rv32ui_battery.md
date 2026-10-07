# The rv32ui Battery

## What the battery is

The `rv32ui-p-*` programs from the riscv-tests suite are the classic
RISC-V architectural conformance battery: 42 self-checking RV32I tests,
each linking the same p-environment preamble and ending in
`RVTEST_PASS`/`RVTEST_FAIL`. kestrel runs all 42 at `func` level in a
single Verilator build — the runner asserts reset, backdoor-loads the
normalized image, releases reset, runs to halt, and scores — and three
of them (simple, add, addi) again at `gate` as a smoke level. The
summary table is the record (beats = RVFI retire beats; records = spike
commit-log records, lockstep-checked as section 3 describes):

| Test (rv32ui-p-*) | Beats (RVFI retire) | Spike records (commit log) | Result (battery verdict) |
| ----------- | -------------- | ------------------ | -------------- |
| add | 500 | 5507 | PASS / lockstep ok |
| addi | 277 | 5284 | PASS / lockstep ok |
| and | 520 | 5527 | PASS / lockstep ok |
| andi | 233 | 5240 | PASS / lockstep ok |
| auipc | 93 | 5107 | PASS / lockstep ok |
| beq | 326 | 5333 | PASS / lockstep ok |
| bge | 344 | 5351 | PASS / lockstep ok |
| bgeu | 369 | 5376 | PASS / lockstep ok |
| blt | 326 | 5333 | PASS / lockstep ok |
| bltu | 351 | 5358 | PASS / lockstep ok |
| bne | 326 | 5333 | PASS / lockstep ok |
| fence_i | 331 | 5338 | PASS / lockstep ok |
| jal | 90 | 5097 | PASS / lockstep ok |
| jalr | 150 | 5157 | PASS / lockstep ok |
| lb | 288 | 5295 | PASS / lockstep ok |
| lbu | 288 | 5295 | PASS / lockstep ok |
| ld_st | 998 | 6005 | PASS / lockstep ok |
| lh | 304 | 5311 | PASS / lockstep ok |
| lhu | 313 | 5320 | PASS / lockstep ok |
| lui | 100 | 5107 | PASS / lockstep ok |
| lw | 318 | 5325 | PASS / lockstep ok |
| ma_data | 415 | 5422 | PASS / lockstep ok |
| or | 523 | 5530 | PASS / lockstep ok |
| ori | 240 | 5247 | PASS / lockstep ok |
| sb | 489 | 5496 | PASS / lockstep ok |
| sh | 542 | 5549 | PASS / lockstep ok |
| simple | 76 | 5083 | PASS / lockstep ok |
| sll | 528 | 5535 | PASS / lockstep ok |
| slli | 276 | 5283 | PASS / lockstep ok |
| slt | 494 | 5501 | PASS / lockstep ok |
| slti | 272 | 5279 | PASS / lockstep ok |
| sltiu | 272 | 5279 | PASS / lockstep ok |
| sltu | 494 | 5501 | PASS / lockstep ok |
| sra | 547 | 5554 | PASS / lockstep ok |
| srai | 291 | 5298 | PASS / lockstep ok |
| srl | 541 | 5548 | PASS / lockstep ok |
| srli | 285 | 5292 | PASS / lockstep ok |
| st_ld | 518 | 5525 | PASS / lockstep ok |
| sub | 492 | 5499 | PASS / lockstep ok |
| sw | 549 | 5556 | PASS / lockstep ok |
| xor | 522 | 5529 | PASS / lockstep ok |
| xori | 242 | 5249 | PASS / lockstep ok |

: rv32ui battery at func level — 42/42 with lockstep; every test halts
on ecall (cause 1) with gp = 1

Gate level reruns simple, add, and addi — 3/3 pass, lockstep not
applicable at that level by design.

## The verdict protocol

The p-environment reports through a `tohost` mailbox: `RVTEST_PASS`
stores 1 to tohost (via the trap-vector path, since a real core traps
the terminating ecall), and the fesvr front end converts a tohost write
into the emulator's exit code. kestrel works differently, and the
difference is deliberate:

- The core halts *on* the terminating ecall (cause 1) by design, before
  any trap-vector `sw gp, tohost` can execute. The DUT never writes
  tohost — so the store port is watched for one anyway (the run
  contract is run-to-halt, tohost-write, or timeout, whichever first).
- The verdict is `gp`'s last RVFI writeback — x3 is exactly the
  register the p-environment would have stored, so its final value is
  the same information: 1 means pass, an odd value greater than 1 is a
  fail code.
- tohost is discovered per image, not hardcoded: a pure-Python ELF32
  symbol reader finds it at `0x80001000` in 41 images and `0x80002000`
  in `ld_st` (its larger data section pushes `.tohost` past the usual
  address); `fromhost` follows at tohost + 0x40.
- Spike's exit code independently confirms tohost == 1 for every test
  on the lockstep side (next section), so the battery's verdict does not
  rest on its own convention alone.

## What the battery proves — and its seam

Forty-two self-checking programs with a second emulator agreeing on
every retired instruction is strong evidence of ISA conformance. Its
seam is the p-environment preamble: every test runs the same ~12 CSR
instructions and an MRET before its body, which is why the bounded CSR
stub of Chapter 2 exists at all. And as Chapter 6's final section
records, forty-two directed tests still missed a real core bug that
formal methods found in an afternoon — the battery tells you the
programs you thought of pass; it says nothing about the ones you didn't.

**Source:** task-8 report (battery table, tohost map, verdict protocol);
`dv/tbclasses/kestrel/rv32ui_battery.py`, `dv/tests/test_kestrel_rv32ui.py`;
`logs/rv32ui_battery/rv32ui_battery_summary_func.txt`
