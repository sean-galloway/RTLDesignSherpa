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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Address Mapper (`andesite_addr_mapper`)

**Module:** `andesite_addr_mapper.sv`
**Location:** `rtl/fub/` (planned)
**Category:** FUB
**Parent:** `scheduler_layer` / `cmd_arbiter`
**Status:** specified — no RTL exists (HAS v0.1 posture)

---

## Purpose

`addr_mapper` turns the system address into the rank, bank-group, bank, row and column fields the scheduler and formatter need. The andesite change is one bounded addition: bank group (`BG0/BG1`) sits between chip select and bank. scoria's decode was rank, bank, row, column; andesite inserts bank group above bank for DDR4. LPDDR4 has no bank groups, so the group field is constant — degenerate, not special-cased.

## Parameters

| Parameter | Type | Range | Default | Meaning | Source |
|---|---|---|---|---|---|
| `SYS_ADDR_WIDTH` | int | 32..48 | 32 | host/system address width | design point |
| `RANK_WIDTH` | int | 1..2 | 1 | rank/chip-select bits | design point |
| `BG_WIDTH` | int | 0..2 | 2 | bank-group bits (0 for LPDDR4) | design point |
| `BANK_WIDTH` | int | 2..3 | 2 | bank bits (3 for LPDDR4) | design point |
| `ROW_WIDTH` | int | 14..18 | 16 | row bits | design point |
| `COL_WIDTH` | int | 10..12 | 10 | column bits (without burst offset) | design point |
| `HASH_EN` | bit | 0/1 | 0 | enable address hashing | CSR |

: Table 2.9: Address mapper parameters

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| — | — | — | (no clock port: the mapper is pure combinational, carried from scoria) |
| — | — | — | (no reset port for the same reason) |
| `axi_addr_i` | in | `AXI_ADDR_WIDTH` | incoming system address |
| `bank_lsb_i` | in | 5 | bank field LSB in the word address (field-boundary knob) |
| `rank_o` | out | `RANK_WIDTH` | decoded rank / chip select |
| `bg_o` | out | `BG_WIDTH` | decoded bank group (constant for LPDDR4) |
| `bank_o` | out | `BANK_WIDTH` | decoded bank |
| `row_o` | out | `ROW_WIDTH` | decoded row |
| `col_o` | out | `COL_WIDTH` | decoded column (burst offset stripped) |
| `byte offset` | in | — | `BYTE_OFFSET_WIDTH` parameter; log2 of the beat byte size |
| `hash_en_i` | in | 1 | bank XOR-hash enable (carried from pumice) |
| `hash_seed_i` | in | 8 | hash seed |

: Table 2.10: Address mapper ports

## Microarchitecture internals

### Decode structure

The decode is parameterized and runtime-programmable via the `ADDR_MAP`-style CSR. Field boundaries reset to the design-point geometry and can be moved by firmware for characterization.

```text
sys_addr -> { cs[CS-1:0],
              bg[BG-1:0]       (DDR4: BG0/BG1; LPDDR4: constant 0),
              bank[BANK-1:0]   (DDR4: 2 bits; LPDDR4: 3 bits),
              row[ROW-1:0],
              col[COL-1:0] }

Field boundaries are runtime CSRs (ADDR_MAP-style), reset to the design point's
geometry; hash-en/hash-seed carried from pumice if enabled.
```

: Figure 2.2: Address decode structure (citation anchor)

`memtype_i` is deliberately absent: the decode is geometry-parameterized,
not memtype-branched (the LPDDR4 degeneration is bg_o tied to zero by the
consumer, per the note below the table). The `ADDR_MAP`-style field
boundary is the `bank_lsb_i` knob, runtime-set, exactly as scoria's mapper.
The `bg_o` delta is the andesite change; every other port is scoria's.

### Scheduler-visible outputs

The mapper computes the group identity the arbiter gates on. For each candidate command, the scheduler sees `{rank, bg, bank}` and uses it for the same-group / cross-group checks described in `ch02_blocks/05_scheduler.md`. LPDDR4 has no bank groups, so `bg_o` is constant zero and the same-group check collapses to rank+bank — graceful degeneration, not a special case. The long/short timing pairs (`tCCD_L`/`tCCD_S`, `tRRD_L`/`tRRD_S`) still apply structurally; LPDDR4 simply makes L equal S.

### Hashing

Address hashing is inherited from pumice and carried in scoria. When `hash_en_i` is set, a subset of the row/column bits is XOR-scrambled with `hash_seed_i` before the final field extraction. This spreads row-buffer contention across banks. The hash function is unchanged from the landed pumice implementation; andesite only widens the address path to include bank group.

## FSM policy

There is no FSM. The block is pure combinational decode plus optional registered outputs to the scheduler. The fixed-form caution applies: this module inherits scoria's tested decode and extends it only in the named dimension — bank group between chip select and bank. No new hashing modes, no new address rearrangements.

## Timing

Decode is combinational. Registered outputs add one controller-clock delay if needed to meet scheduler timing. Geometry is build-time per HAS Ch 2.4/5; field-boundary CSRs are runtime.

## Notes

- The `bg_o` width is 2 for DDR4 and 0 for LPDDR4 at the parameter level. If zero-width ports are awkward in your RTL style, tie the LPDDR4 path to constant zero inside the module and keep the port width at 2 — but don't make the scheduler special-case it.
- The design point fixes DDR4-1600 x8 with 4 bank groups × 4 banks and LPDDR4-1600 x16 with 8 ungrouped banks per channel. Reset the `ADDR_MAP` CSRs to those geometries so firmware doesn't have to.
- scoria's decode equations are the starting point; the kmap book's first address-map targets are the verification targets for andesite.
