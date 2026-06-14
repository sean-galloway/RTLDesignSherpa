<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Address XOR / Hash (`addr_mapper_fub`)

**Module:** `addr_mapper_fub.sv`
**Location:** `rtl/fub/`
**Category:** FUB (combinational; no clock)
**Parent:** `ddr2_lpddr2_ctrl`
**Status:** Skeleton

---

## Purpose

`addr_mapper_fub` decodes a flat `AXI_ADDR_WIDTH`-bit address into the DRAM-layer `(rank, bank, row, column)` tuple per the currently-active address-mapping scheme. The XOR / hash happens **here** — upstream of the read/write CAMs — so that the CAMs store the decoded tuple and not the raw AXI address.

The FUB is **pure combinational** — there is no clock, no flop, no FSM. The output is valid the same cycle as the input. The path is one of the timing-critical signatures in the design and is treated as a multi-cycle path only if synthesis cannot meet timing.

## Mirror to the Python `AddressMapping` Class

This RTL is the mirror of the `AddressMapping` Python class in the DV repository (`CocoTBFramework.components.dfi.address_mapping`). Both produce **bit-for-bit identical** decoded outputs for the same input. The mirror is enforced by:

- Same scheme list (ROW_MAJOR, BANK_INTERLEAVE, XOR_HASH)
- Same field-bit positions per scheme
- Same XOR_HASH seed and tap matrix

The shared decode function eliminates a common class of bugs where simulation passes (because the BFM decodes one way) but RTL fails (because the controller decodes a different way).

## Interface

| Signal             | Direction | Width    | Description                                            |
|--------------------|-----------|----------|--------------------------------------------------------|
| `axi_addr_i`       | input     | `AW`     | Flat AXI byte address                                  |
| `scheme_active_i`  | input     | 2        | Runtime scheme select from `ADDR_MAP_TUNING.scheme_or` |
| `xor_seed_i`       | input     | 8        | Runtime seed for XOR_HASH (from CSR)                   |
| `bg_field_pos_i`   | input     | 3        | Bank-group field bit position (unused in DDR2/LPDDR2; reserved) |
| `rank_o`           | output    | `$clog2(NR)` | Decoded rank                                       |
| `bank_o`           | output    | `BA`     | Decoded bank                                           |
| `row_o`            | output    | `ROW_WIDTH` | Decoded row                                         |
| `col_o`            | output    | `COL_WIDTH` | Decoded column (byte-aligned within burst)          |

## Scheme Decode

### Scheme 1: ROW_MAJOR

The simplest mapping; one contiguous row per rank/bank stride. Bit layout:

```
| ... reserved ... | rank | row [ROW_WIDTH-1:0] | bank [BA-1:0] | col [COL_WIDTH-1:0] | byte_in_dq |
```

The byte-in-DQ field is the controller's column-byte offset and is consumed by `wr_data_path_fub` for `wstrb` masking; it is **not** part of the decoded `col_o` (which is column-word aligned).

ROW_MAJOR is best for sequential streaming workloads where a long burst stays in one row.

### Scheme 2: BANK_INTERLEAVE

```
| ... reserved ... | rank | row [ROW_WIDTH-1:0] | col_hi [...] | bank [BA-1:0] | col_lo [...] | byte_in_dq |
```

Bank bits are placed **between** column-low and column-high bits, so consecutive cache lines round-robin across banks. This is the recommended default for general-purpose workloads with mixed access patterns; it produces higher bank-parallelism in the scheduler.

### Scheme 3: XOR_HASH

Same layout as BANK_INTERLEAVE, but the bank field and (a subset of) the column-high bits are XOR-hashed with row bits:

```
bank_hashed[i] = bank_raw[i] XOR row_raw[i] XOR row_raw[i + BA] XOR xor_seed[i]
```

The XOR_HASH scheme defeats pathological row-conflict patterns (e.g., a power-of-two stride that lands on the same bank in BANK_INTERLEAVE). The seed `xor_seed_i` is runtime-modifiable so a bring-up engineer can change the hash without rebuilding.

## Runtime Scheme Mux

The output is multiplexed across the synthesized schemes per `scheme_active_i`. Only schemes in `ADDR_MAP_SCHEMES_SYNTH` are routed to the mux; un-synthesized schemes tie off and writing them via CSR returns `pslverr`.

```
                  axi_addr_i [AW-1:0]
                       │
       ┌───────────────┼───────────────────┐
       ▼               ▼                   ▼
  ROW_MAJOR     BANK_INTERLEAVE      XOR_HASH
  decoder        decoder              decoder
       │               │                   │
       └───────┬───────┴───────────────────┘
               ▼
           scheme_active_i ──► 3:1 mux
               │
               ▼
        (rank, bank, row, col) ────► CAMs
```

## Timing Budget

The decoder is purely combinational. The longest path in XOR_HASH is the XOR of (a) several address bits, (b) the seed, and (c) the row bits — about 5–6 levels of XOR gates plus a 3:1 mux. At 500 MHz this is comfortably within 0.5 ns of MC clock cycle time.

| Path                          | Estimate (gate-level) |
|-------------------------------|-----------------------|
| `axi_addr_i` → `bank_o` (ROW_MAJOR)        | 2 levels of MUX       |
| `axi_addr_i` → `bank_o` (BANK_INTERLEAVE)  | 2 levels of MUX       |
| `axi_addr_i` → `bank_o` (XOR_HASH)         | 5 levels XOR + 2 MUX  |
| `axi_addr_i` → `row_o`                     | 1 level MUX           |

If XOR_HASH does not meet timing at the target frequency, the FUB can be re-fitted with a single pipeline stage (the seed-XOR can absorb a flop without changing the per-tuple invariant — the seed only changes on quiet points anyway).

## Verification

The RTL decoder and the Python `AddressMapping` class are co-validated by a small cocotb test that picks 10000 random addresses, asks each side to decode, and asserts bit-equality on the (rank, bank, row, col) tuple. This is the primary regression for `addr_mapper_fub`.

## TODO

- Tap matrix for XOR_HASH — the exact bit mapping
- Synthesis hint for the XOR_HASH critical path
- Edge cases for `AW < (ROW_WIDTH + COL_WIDTH + BA + clog2(NR))` (under-decoded address — should it tie-off or error?)
