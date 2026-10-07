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

# Address Mapper (`scoria_addr_mapper`)

**Module:** `scoria_addr_mapper.sv`
**Location:** `rtl/fub/`
**Category:** address decode
**Parent:** `scoria_axi4_layer` (instantiated by the intakes)
**Status:** complete, sim-verified, formal-proven

---

## Purpose

`scoria_addr_mapper` turns a flat AXI byte address into the `{rank, bank, row, col}` tuple the scheduling CAMs store. It is pure combinational: one cycle of barrel-shift and mask logic, with no state. The mapping is controlled at runtime by a single CSR knob, `bank_lsb_i`, which decides where the bank field sits in the byte-offset-stripped word address. That one knob generates every common mapping scheme, so there is no scheme mux.

The block is instantiated once on the write path and once on the read path, inside `scoria_axi4_layer`.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `AXI_ADDR_WIDTH` | int | — | 32 | host byte-address width |
| `NUM_RANKS` | int | 1, 2, 4 | 1 | ranks per channel |
| `NUM_BANKS` | int | 4, 8 | 8 | banks per rank |
| `ROW_WIDTH` | int | — | 14 | row address width |
| `COL_WIDTH` | int | — | 10 | column address width |
| `BYTE_OFFSET_WIDTH` | int | — | 3 | `log2(device bytes per beat)`; 3 for a 64-bit data path |

: Table 2.11.1: Address mapper parameters

`BYTE_OFFSET_WIDTH` strips the beat byte offset. What remains is a device-word address; the column walk of one DRAM burst must stay inside a single bank, which is what constrains `bank_lsb_i`.

## Interface

### Address and configuration ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `axi_addr_i` | in | `AXI_ADDR_WIDTH` | host byte address (AW or AR channel) |
| `bank_lsb_i` | in | 5 | bank field LSB in the word address |
| `hash_en_i` | in | 1 | enable bank XOR-hash |
| `hash_seed_i` | in | 8 | XOR-hash seed |
| `rank_o` | out | `$clog2(NUM_RANKS > 1 ? NUM_RANKS : 2)` | decoded rank |
| `bank_o` | out | `$clog2(NUM_BANKS)` | decoded bank, optionally hashed |
| `row_o` | out | `ROW_WIDTH` | decoded row |
| `col_o` | out | `COL_WIDTH` | decoded column |

: Table 2.11.2: Address mapper interface

## Microarchitecture internals

### Byte-offset strip and `bank_lsb` clamp

The mapper first strips the beat byte offset and zero-extends to 32 bits:

```text
w_word = axi_addr_i[AXI_ADDR_WIDTH-1 : BYTE_OFFSET_WIDTH]
```

`bank_lsb_i` is clamped to `[0, COL_WIDTH]` so every field slice stays legal:

```text
w_blsb = (bank_lsb_i > COL_WIDTH) ? COL_WIDTH : bank_lsb_i
```

`bank_lsb == COL_WIDTH` places the bank above the whole column, giving a row-major mapping. Any value below `COL_WIDTH` splits the column around the bank, producing interleaving.

### Field extraction

The word address is sliced into four variable-base fields:

```text
col_lo = w_word & ((1 << w_blsb) - 1)
bank   = (w_word >> w_blsb) & ((1 << BW) - 1)
col_hi = (w_word >> (w_blsb + BW)) & ((1 << (COL_WIDTH - w_blsb)) - 1)
row    = (w_word >> (COL_WIDTH + BW)) & ((1 << ROW_WIDTH) - 1)
rank   = (NUM_RANKS > 1) ? (w_word >> (COL_WIDTH + BW + ROW_WIDTH)) : 0
```

The column is reassembled from the low and high pieces:

```text
col = col_lo | (col_hi << w_blsb)
```

Row and rank stack above the column region; their LSB positions are invariant. Only the bank position moves with `bank_lsb_i`.

### Bank XOR-hash

When `hash_en_i` is high, each bank bit is folded with row bits and the seed:

```text
bank_hashed[i] = bank_raw[i] ^ row[i] ^ row[MID] ^ seed[i]
MID = (i + BW < ROW_WIDTH) ? (i + BW) : (ROW_WIDTH - 1)
```

The `MID` index is clamped so it never runs past `ROW_WIDTH`. The fold matches the legacy `XOR_HASH` scheme and breaks power-of-two-stride hot-spots.

## FSM policy

There is no FSM. The block is a single combinational stage.

## Timing

All outputs are combinational from the inputs. The critical path is the barrel-shift/mask chain plus the optional XOR-hash. The block is duplicated on the AW and AR paths, so read and write addresses decode in parallel.

## Notes

- **Bank-LSB bound.** Software must keep `bank_lsb_i >= log2(DRAM_BL)`, where `DRAM_BL` is the JEDEC burst length in device words. That bound keeps one DRAM burst inside a single bank. The RTL only clamps the upper bound to `COL_WIDTH`; the lower bound is a software contract.
- **Measured, not derived.** The lower bound was established by measurement rather than by formula. Two earlier versions of the constraint existed in the tree: `log2(cols/burst)` (too restrictive) and `log2(BL/DFI_RATE)` (too permissive and unsafe). Commit `f60e5ba1d` replaced both with the measured bound `log2(DRAM_BL)`; see the RTL header and the test `dv/tests/fub/test_scoria_addr_mapper.py::minimum_bank_lsb_is_measured`.
- **Formal proof.** The block is proven in `formal/scoria/addr_mapper/scoria_addr_mapper.sby`.
- **Rank degeneration.** With `NUM_RANKS == 1`, `rank_o` is tied to zero.
