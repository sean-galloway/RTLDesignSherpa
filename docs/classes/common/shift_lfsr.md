# Shifters and LFSRs — Class Overview

**Category:** Shift registers / PRNG
**Scope:** `rtl/common/shifter_*.sv` (5 modules)
**Status:** Production-ready

---

## What this is

The shifter family: a combinational barrel shifter for arbitrary single-cycle shifts, a clocked universal shift register (load/left/right/hold), and three pseudo-random LFSR variants (generic, Fibonacci, Galois) with configurable tap polynomials and cycle-completion detection.

## Why use this class

Barrel shifters show up in arithmetic normalization, byte aligners, and crossbar permutations. Universal shift registers cover serial/parallel conversion. LFSRs provide cheap pseudo-random sequences for traffic generators, dithering, scrambling, BIST patterns, and stimulus randomization — all without consuming a full PRNG IP.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`shifter_universal.sv`](../../../rtl/common/shifter_universal.sv) | Clocked left/right/load/hold shift register | Serial-parallel conversion, generic register file |
| [`shifter_barrel.sv`](../../../rtl/common/shifter_barrel.sv) | Combinational barrel shifter — logical / arithmetic / wrap, controlled by a 3-bit op | Single-cycle multi-position shifts, normalization |
| [`shifter_lfsr.sv`](../../../rtl/common/shifter_lfsr.sv) | Generic LFSR with configurable tap positions and cycle-done flag | Custom PRNG polynomial, traffic stimulus |
| [`shifter_lfsr_fibonacci.sv`](../../../rtl/common/shifter_lfsr_fibonacci.sv) | Fibonacci-style LFSR (feedback to MSB only) | Classic textbook LFSR, smallest XOR footprint |
| [`shifter_lfsr_galois.sv`](../../../rtl/common/shifter_lfsr_galois.sv) | Galois LFSR with distributed XOR taps | High-frequency PRNG, better timing than Fibonacci |

## Picking guide

For a clocked shift register with parallel load, use `shifter_universal`. For arbitrary single-cycle shifts (normalization, alignment), use `shifter_barrel`. For pseudo-random sequences: `shifter_lfsr_galois` is the default — distributed XORs give the cleanest timing. Pick `shifter_lfsr_fibonacci` if you want the simpler topology or are matching a reference implementation. Use `shifter_lfsr` when you need to drop in a custom polynomial without picking a topology.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_shifter_*.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — one `.md` per module. Use those for tap-polynomial tables, parameter descriptions, and port lists.

## Source

[`rtl/common/`](../../../rtl/common/) (`shifter_*.sv`)
