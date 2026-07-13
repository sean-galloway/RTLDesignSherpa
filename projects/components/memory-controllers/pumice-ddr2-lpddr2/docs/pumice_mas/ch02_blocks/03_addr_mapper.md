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

# Address Mapper (`addr_mapper`)

**Module:** `addr_mapper.sv`
**Location:** `rtl/fub/`
**Category:** FUB (combinational; no clock)
**Parent:** `pumice_wr_intake` / `pumice_rd_intake`
**Status:** Implemented

> **Rearchitected:** the SWAG described a three-scheme decoder
> (ROW_MAJOR / BANK_INTERLEAVE / XOR_HASH) selected by a runtime `scheme_active_i`
> mux. That is retired. The live `addr_mapper` has **one** placement knob —
> `bank_lsb_i` — that slides the bank field through the (byte-stripped) column
> region, plus an optional bank XOR-hash. The classic schemes are now just
> settings of `bank_lsb`. There is no scheme selector, no `SYNTH_*` param, and
> no un-synthesized-scheme tie-off.

---

## Purpose

`addr_mapper` decodes a flat `AXI_ADDR_WIDTH`-bit address into the DRAM-layer
`(rank, bank, row, col)` tuple. It is **pure combinational** — no clock, no flop,
no FSM. The output is valid the same cycle as the input. One instance sits at the
head-address decode of each intake (`pumice_wr_intake`, `pumice_rd_intake`), so
the CAMs store the decoded tuple rather than the raw AXI address.

The mapper is driven entirely from the `ADDR_MAP` CSR register (see
[`rtl/macro/pumice_csr.rdl`](../../rtl/macro/pumice_csr.rdl)) via three runtime
inputs; there are no per-scheme build parameters.

## Parameters

| Parameter           | Default | Purpose                                              |
|---------------------|---------|------------------------------------------------------|
| `AXI_ADDR_WIDTH`    | 32      | Flat AXI byte-address width                           |
| `NUM_RANKS`         | 1       | 1, 2, or 4 (rank field width `KW`)                   |
| `NUM_BANKS`         | 8       | 4 or 8 (bank field width `BW = $clog2(NUM_BANKS)`)   |
| `ROW_WIDTH`         | 14      | Row field width `RW`                                 |
| `COL_WIDTH`         | 10      | Column field width `CW`                              |
| `BYTE_OFFSET_WIDTH` | 3       | `log2(beat byte size)`; low bits stripped to word addr |

## Interface

| Signal        | Direction | Width                    | Description                                        |
|---------------|-----------|--------------------------|----------------------------------------------------|
| `axi_addr_i`  | input     | `AXI_ADDR_WIDTH`         | Flat AXI byte address                              |
| `bank_lsb_i`  | input     | 5                        | Bank-field LSB in the word address (`ADDR_MAP.bank_lsb`) |
| `hash_en_i`   | input     | 1                        | Enable the bank XOR-hash (`ADDR_MAP.hash_en`)      |
| `hash_seed_i` | input     | 8                        | XOR-hash seed (`ADDR_MAP.hash_seed`)               |
| `rank_o`      | output    | `$clog2(max(NR,2))`      | Decoded rank                                       |
| `bank_o`      | output    | `$clog2(NUM_BANKS)`      | Decoded bank                                       |
| `row_o`       | output    | `ROW_WIDTH`              | Decoded row                                        |
| `col_o`       | output    | `COL_WIDTH`              | Decoded column                                     |

## The single-knob layout

The address is first stripped of its byte offset to a **word address**:

```
w_word = axi_addr_i[AXI_ADDR_WIDTH-1 : BYTE_OFFSET_WIDTH]   (zero-extended to 32b)
```

The bank field is `BW` bits wide and sits at bit position `bank_lsb` inside the
word address. The column is split **around** the bank into a low part below it
and a high part above it; the row and rank stack above the whole column region at
**invariant** positions:

```
word address (low → high):
  [ col_lo(bank_lsb) | bank(BW) | col_hi(CW - bank_lsb) | row(RW) | rank(KW) ]

  col = { col_hi, col_lo }
  row LSB is always at bit CW + BW      (only the bank slides; the column
                                         auto-splits around it)
```

### Field extraction (variable-base shifts/masks)

The RTL clamps `bank_lsb` to `[0, COL_WIDTH]` first (`w_blsb`), so `col_hi`'s
width `CW - bank_lsb` never goes negative and the row/rank slices stay legal.
Then, over 32-bit intermediates:

```
col_lo = w_word & ((1 << bank_lsb) - 1)
bank   = (w_word >> bank_lsb) & ((1 << BW) - 1)
col_hi = (w_word >> (bank_lsb + BW)) & ((1 << (CW - bank_lsb)) - 1)
row    = (w_word >> (CW + BW)) & ((1 << RW) - 1)
rank   = (w_word >> (CW + BW + RW)) & ((1 << KW) - 1)   // 0 when NUM_RANKS == 1
col    = col_lo | (col_hi << bank_lsb)
```

## The classic schemes are just `bank_lsb` settings

| Legacy scheme          | Equivalent setting                                             |
|------------------------|----------------------------------------------------------------|
| ROW_MAJOR              | `bank_lsb == COL_WIDTH` — bank sits **above** the whole column |
| max BANK_INTERLEAVE    | `bank_lsb == log2(cols/burst)` — minimal `col_lo`, so a burst's column walk stays inside one bank while consecutive lines round-robin banks |
| partial interleave     | any `bank_lsb` in between                                      |
| XOR_HASH               | `hash_en == 1`, folded on top of **any** placement above       |

The default `ADDR_MAP.bank_lsb = 0x0A = COL_WIDTH` is therefore ROW_MAJOR.
Software is expected to keep `log2(cols/burst) <= bank_lsb <= COL_WIDTH` so a
DRAM burst's column walk never crosses a bank boundary; the RTL clamp enforces
the upper edge.

## Bank XOR-hash

When `hash_en_i` is set, each bank bit is XOR-folded with two row slices and the
seed (a `genvar` loop of width `BW`):

```
bank_hashed[i] = bank_raw[i] ^ row[i] ^ row[MID] ^ hash_seed[i]
  where MID = (i + BW < ROW_WIDTH) ? (i + BW) : (ROW_WIDTH - 1)   // clamped
w_bank = hash_en ? bank_hashed : bank_raw
```

This is the identical fold to the legacy XOR_HASH scheme and defeats
power-of-two-stride hot-banking. `hash_seed_i` is runtime-modifiable, so a
bring-up engineer can change the hash without rebuilding.

## Mirror to the DV address model

This RTL is the bit-exact mirror of the DV-side address model; both must produce
identical `(rank, bank, row, col)` for the same input and the same
`bank_lsb`/`hash_en`/`hash_seed`. The mirror eliminates the class of bugs where
the BFM decodes one way and the controller decodes another. It is exercised by
the `addr_mapper` FUB test, which sweeps addresses and `bank_lsb` values and
asserts bit-equality against the model.

## Timing

Purely combinational. The longest path is the hash fold (a few XOR levels) plus
the variable-base shift/mask extraction. At the board target this is comfortably
within a cycle; if a future high-frequency target cannot meet timing, the mapper
can be treated as a multi-cycle path (the placement knob only changes at quiet
points).

## Notes / flags

- `bank_lsb_i` is 5 bits wide, matching `ADDR_MAP.bank_lsb[4:0]`.
- `rank_o` width uses `$clog2(NUM_RANKS > 1 ? NUM_RANKS : 2)` so a single-rank
  build still has a legal 1-bit port; `rank_o` is tied to `'0` when
  `NUM_RANKS == 1`.
- There is **no** `bg_field_pos` / bank-group input (DDR2/LPDDR2 have no bank
  groups), no `scheme_active_i`, and no CSR `pslverr` path for unsupported
  schemes — those SWAG concepts are gone.
