# Descriptor fetch drives ARSIZE=64B on a 32B bus

**Status:** Active / Filed, not yet fixed
**Severity:** Medium — benign in the current testbenches, but it is an AXI
protocol violation on the wire and it over-reads 32 bytes past every
extended-descriptor chunk 1.

## Defect

`descriptor_engine_beats.sv:925` drives a fixed burst size of 64 bytes:

```systemverilog
assign ar_size = 3'b110;         // 64 bytes (512-bit)
```

The descriptor bus is **256 bits / 32 bytes**, fixed on both sides:
`descriptor_engine_beats.sv:114` (`input logic [255:0] r_data`) and
`rapids_beats_top.sv:136/158` (`src_m_axi_desc_rdata`, `snk_m_axi_desc_rdata`).

AXI requires `ARSIZE` to be no larger than the data bus width, so a 256-bit
bus caps it at `3'b101` (32 bytes). The trailing comment ("512-bit") is a
leftover from a wider bus and is what makes the value look intentional.

The neighbouring `ctrlrd_engine.sv` gets this right (`ar_size = 3'b010` on its
32-bit bus), which shows the field is meant to track the bus and simply was
not updated when the descriptor bus narrowed.

## Same defect in STREAM

`projects/components/dmas/stream/rtl/fub/descriptor_engine.sv:925` carries the
identical line against the identical `[255:0] r_data`, with the same stale
comment. RAPIDS was ported from STREAM, so both need the same one-line change.

## Evidence

A compliant slave sizes its read from ARSIZE, so it fetches 64 bytes where 32
were intended. Extended descriptors put chunk 0 at `desc_addr` and chunk 1 at
`desc_addr + 0x20`, so the chunk-1 fetch reads `0x20`-`0x5F` and runs 32 bytes
past the descriptor. That is directly observable: every EXT run, **including
passing ones**, logs exactly 32 uninitialized-memory reads at addresses
`0x40`-`0x5F`:

```
cocotb_log_rapids_beats_top - WARNING - Reading uninitialized memory at address 0x40
... (through 0x5F)
```

The over-read is also visible from the other side, as the TB's 256-bit
descriptor field masking a 64-byte value back down to 32 bytes:

```
WARNING: Value 0x4000...0100000 exceeds bit width for field 'data', masked to 0x40005...
```

The masking discards the upper 32 bytes, so the descriptor the scheduler sees
is correct and the over-read is harmless *in this testbench*. A slave that
answers the request as issued, or an interconnect that checks ARSIZE, need not
be so forgiving.

## Not the cause of the EXT addressing failure

Filed separately and deliberately: this is unconditional (it happens on every
EXT fetch, passing runs included) whereas the extended-addressing run-boundary
failure is seed-dependent. The two are unrelated; do not close one by fixing
the other.

That run-boundary defect was found and fixed in `c09207c42` (the engine valids
now stall between runs, restoring STREAM's `!w_*_need_base` terms). It does not
touch this issue: the ARSIZE constant is in the DESCRIPTOR ENGINE, while that
fix is in the scheduler. This one is still open.

## Proposed fix

One line per file, `3'b110` -> `3'b101`, plus the stale comment. Needs its own
validation, because the framework's `axi4_compliance_checker.py` does **not**
cover this: its `BURST_SIZE_VIOLATION` rule only rejects `burst_size > 7`, an
encoding-range check, not size-versus-bus-width. Negative validation would be
asserting on the AR packet's `size` field in the descriptor slave, which fails
before the change and passes after.

## Provenance

Pre-existing, not introduced by the extended-addressing work: `git blame` puts
the line at `3c308050bf` (2026-01-11). The adjacent `ar_valid`/`ar_addr` lines
were changed by `8741c4c040` for the chunk-1 fetch, which is what brought the
over-read into view.
