# Testbench and Golden Model

## The harness

kestrel's testbench is deliberately thin — the core is the design under
test and RVFI is the only observation channel it needs.
`kestrel_tb_top` wraps the core in a behavioral 64 KiB word memory with
combinational reads, loaded at time 0 from `+imem=<hex>` (and
`+dmem=<hex>`) plusargs via `$readmemh`. The memory is *unified*: one
array serves fetch and load/store, the testbench choice that lets
rv32ui-p-fence_i's self-modifying code work with no coherence path
(Chapter 5). The store port honors `dmem_wstrb` per byte — the contract
that pins the rotated-strobe convention.

Two additions serve the battery (Chapter 6's next sections): a backdoor
write port (`tb_mem_we`/`tb_mem_addr`/`tb_mem_wdata`, one word per
cycle, deliberately not reset-gated) so all 42 vendor images stream
through one Verilator build, and a tohost watch on the store port.

The cocotb side (`kestrel_tb.py`) owns the clock/reset choreography and
the RVFI capture, and it enforces a sampling contract that took one real
bug to learn: reset is released *right after a posedge* and beats are
sampled on *falling edges*. Post-edge release plus negedge sampling
captures every retiring instruction exactly once — including the first
`RESET_ADDR` beat, which lives only in the partial cycle before the
first posedge and was entirely missed by the naive post-edge sampling.
The halting cycle is sampled too: the trap beat (`rvfi_valid=1`,
`rvfi_trap=1`) is recorded, after which `rvfi_valid` stays low.

After halt, the TB samples four more cycles pinning halt-hold: `halt`
stays raised, `rvfi_valid` stays low, `rvfi_pc_rdata` frozen.

## The golden interpreter

`rv32i_interpreter.py` is a ~90-line Python model of RV32I that emits
the same RVFI beat format as the core — one record per retired
instruction, none for anything that doesn't retire, plus the halt state.
Its memory model mirrors the core's conventions exactly: word-based,
rotated-strobe stores, architectural two-word misaligned loads/stores,
the CSR stub's zero writeback, MRET fall-through, FENCE NOPs, and the
cause-3 halt with the misaligned target on `pc_wdata`. When the RTL and
the model disagree, the diff is a named field at a named beat at a named
PC — minutes to localize, not a waveform archeology session.

The diff is total: every sampled beat is compared field by field across
the entire RVFI bundle — pc, insn, order, trap, rs addresses and data,
rd address and data, and all four memory channels. There is no sampled
subset and no tolerance.

## Programs and the hex pipeline

Hand-written assembly programs (`focus`, `rv32ui_ops`, branch/jump
vectors, load/store vectors, system tests) are built by a small script:

```
as -> objdump (provenance) -> objcopy -O verilog -> normalize_hex.py -> <name>.hex
```

`objcopy -O verilog` emits *bytes* with byte-addressed `@` records,
which the testbench's *word* arrays cannot load directly (an
`@80000000` record would index out of bounds), so `normalize_hex.py`
packs little-endian words and emits sparse word-indexed records, with a
`--base` option that subtracts the battery images' `0x80000000` link
address. Vendor riscv-tests hexes go through the same normalizer.

## The run grammar

Every test runs at two Verilator build levels through the rds-dv
framework, sources always from the filelists:

```
make -C projects/components/riscv-ip/kestrel-rv32i/dv/tests run-<testroot>-<gate|func>[-serial]
```

`gate` is the fast smoke level; `func` runs the full matrix. The
battery, lockstep, and formal layers of the next sections all sit on
top of this harness and reuse its contracts rather than re-deriving
them.

**Source:** `dv/tb/kestrel_tb_top.sv`, `dv/tbclasses/kestrel/kestrel_tb.py`,
`dv/tbclasses/kestrel/rv32i_interpreter.py`,
`dv/tests/programs/build_progs.sh`, `dv/tests/programs/normalize_hex.py`;
task-5 report (sampling contract, fail-first evidence)
