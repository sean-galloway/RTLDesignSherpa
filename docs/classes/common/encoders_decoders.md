# Encoders, Decoders, and Sort — Class Overview

**Category:** Combinational logic
**Scope:** `encoder*.sv`, `decoder.sv`, `sort.sv`, plus `find_first_set.sv` / `find_last_set.sv` (5 modules)
**Status:** Production-ready

---

## What this is

The one-hot ↔ binary conversion primitives — basic encoder, decoder, and a priority encoder with explicit MSB-first search and enable — plus the related bit-search helpers (`find_first_set`, `find_last_set`) and the pipelined odd-even sort engine for sorting a fixed-size vector of values per cycle.

## Why use this class

Anywhere you have valid/select vectors, request bitmaps, or priority structures, you reach for an encoder or decoder. The priority variant with enable is the workhorse for arbitration and grant generation. `find_first_set` / `find_last_set` are the standard helpers for scanning bitmaps (e.g., free-list lookups, leading-zero count). The `sort` engine covers cases where small arrays must be ordered every cycle without falling back to a software-style multi-cycle sort.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`encoder.sv`](../../../rtl/common/encoder.sv) | One-hot N-bit → log2(N) binary | Standard one-hot to binary |
| [`decoder.sv`](../../../rtl/common/decoder.sv) | M-bit binary → 2^M one-hot | Address decode, select fan-out |
| [`encoder_priority_enable.sv`](../../../rtl/common/encoder_priority_enable.sv) | Priority encoder, MSB-first, with enable | Arbitration grant, top-priority pick |
| [`find_first_set.sv`](../../../rtl/common/find_first_set.sv) | Index of lowest set bit | LSB-favored bitmap scan |
| [`find_last_set.sv`](../../../rtl/common/find_last_set.sv) | Index of highest set bit | MSB-favored bitmap scan |
| [`sort.sv`](../../../rtl/common/sort.sv) | Pipelined odd-even sort of a fixed-size vector (descending) | New input each cycle, predictable latency |

## Picking guide

Use `encoder` / `decoder` for the plain one-hot conversions. Use `encoder_priority_enable` when more than one input may be hot and you want a deterministic priority pick — this is what most arbiters internally rely on. Use `find_first_set` for LSB-favored scans (free-list, lowest-priority request), `find_last_set` for MSB-favored (highest-priority request, leading-set position). Pull in `sort` only when you actually need a per-cycle sorted vector — it is heavier than the other primitives.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_encoder*.py`, `test_decoder.py`, `test_find_*.py`, `test_sort.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — one `.md` per module. Use those for parameter descriptions, port lists, and latency notes (notably for `sort`).

## Source

[`rtl/common/`](../../../rtl/common/) (`encoder*.sv`, `decoder.sv`, `find_first_set.sv`, `find_last_set.sv`, `sort.sv`)
