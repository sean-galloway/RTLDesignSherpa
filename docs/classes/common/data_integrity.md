# Data Integrity — Class Overview

**Category:** Error detection / correction
**Scope:** `rtl/common/dataint_*.sv` (7 modules)
**Status:** Production-ready

---

## What this is

The data-integrity primitives: parameterized CRC (configurable polynomial, data width, reflection, with single-bit and 8-bit cascade leaf cells), Hamming SECDED encode/decode (single-error correct, double-error detect), a multi-segment parity generator/checker (even or odd), and a simple accumulating checksum.

## Why use this class

Storage paths, link-layer protocols, packet interfaces, and on-chip RAMs all need integrity checks. These modules give you the standard answers: CRC for link/storage protocols, Hamming SECDED for memory protection, parity for cheap single-bit detection, and an accumulating checksum for lightweight verification — without having to re-derive polynomials or syndrome decoders.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`dataint_parity.sv`](../../../rtl/common/dataint_parity.sv) | Multi-chunk parity generator and checker (even/odd) | Cheapest single-bit error detection |
| [`dataint_checksum.sv`](../../../rtl/common/dataint_checksum.sv) | Accumulating additive checksum | Lightweight running integrity value |
| [`dataint_crc_xor_shift.sv`](../../../rtl/common/dataint_crc_xor_shift.sv) | Single-bit CRC step (XOR-and-shift leaf) | Building block — not normally instantiated directly |
| [`dataint_crc_xor_shift_cascade.sv`](../../../rtl/common/dataint_crc_xor_shift_cascade.sv) | 8-bit cascade of the single-bit step | Byte-per-cycle CRC chunk |
| [`dataint_crc.sv`](../../../rtl/common/dataint_crc.sv) | Full configurable CRC engine (polynomial, width, reflect) | Protocol/storage CRC, any standard polynomial |
| [`dataint_ecc_hamming_encode_secded.sv`](../../../rtl/common/dataint_ecc_hamming_encode_secded.sv) | Hamming SECDED encoder | Memory write path with ECC |
| [`dataint_ecc_hamming_decode_secded.sv`](../../../rtl/common/dataint_ecc_hamming_decode_secded.sv) | Hamming SECDED decoder, corrects 1, flags 2 | Memory read path with ECC |

## Picking guide

For a single bit of detection on a bus, use `dataint_parity` — cheap and synchronous. For memory protection (SRAM, register files, on-chip storage) use the Hamming SECDED pair. For link / storage protocols (Ethernet, USB, PCIe-style framing, NVMe-style storage) use `dataint_crc` with the appropriate polynomial — the `_xor_shift*` leaves are exposed for building custom CRC topologies. Use `dataint_checksum` only when a running additive sum is sufficient — it does not match CRC strength.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_dataint_*.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — one `.md` per module. Use those for polynomial tables, parameter descriptions, and syndrome decoding details.

## Source

[`rtl/common/`](../../../rtl/common/) (`dataint_*.sv`)
