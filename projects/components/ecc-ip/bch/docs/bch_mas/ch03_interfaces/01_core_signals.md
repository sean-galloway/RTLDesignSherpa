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

# Core Signals

This page presents the valid/ready core signals as a contract table rather
than restating the prose interface description in
`../bch_has/ch04_interfaces/01_core_interface.md`. The direction, reset value,
and creator block for each signal are the source of truth here.

## Reset strategy

All core logic uses **synchronous active-low reset** (`aresetn`), the house
clocking convention. Reset clears block state, counters, the LFSR, syndrome
registers, solver arrays, and the Chien position counter. The block buffer
itself is not reset; its read/write pointers are reset, which makes the buffer
contents logically invalid until overwritten.

## `bch_encoder_core` signal contract

| Signal | Dir | Width | Reset value | Creates / consumes | Contract | Source block page |
|---|---|---|---|---|---|---|
| `aclk` | in | 1 | — | clock source | one clock for the whole core | — |
| `aresetn` | in | 1 | — | reset source | synchronous active-low reset | — |
| `in_valid` | in | 1 | — | upstream | stable until `in_ready` high | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_ready` | out | 1 | 0 | encoder core | combinational `!r_valid || m_ready` gated by parity-drain | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_data` | in | `BITS_PER_BEAT` | — | upstream | data bits, low-aligned; partial final beat qualified by `in_keep` | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_keep` | in | `BITS_PER_BEAT` | — | upstream | present-bit mask, low-aligned; partial only on final beat | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_last` | in | 1 | — | upstream | this beat carries the `K_BITS`-th data bit | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_valid` | out | 1 | 0 | encoder core | registered pipeline flag; data beats then parity beats | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_ready` | in | 1 | — | downstream | may depend on `out_valid` | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_data` | out | `BITS_PER_BEAT` | 0 | encoder core | data while `!w_parity_phase`, parity while `w_parity_phase` | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_keep` | out | `BITS_PER_BEAT` | 0 | encoder core | full except on final data and final parity beats | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_last` | out | 1 | 0 | encoder core | this beat carries the `N_BITS`-th coded bit | [encoder core](../ch02_blocks/01_encoder.md) |
| `frame_err` | out | 1 | 0 | encoder core | pulse when `in_last` does not coincide with `K_BITS` data bits | [encoder core](../ch02_blocks/01_encoder.md) |

: Table 3.1: `bch_encoder_core` signal contract

## `bch_decoder_core` signal contract

| Signal | Dir | Width | Reset value | Creates / consumes | Contract | Source block page |
|---|---|---|---|---|---|---|
| `in_valid` | in | 1 | — | upstream | stable until `in_ready` high | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `in_ready` | out | 1 | 0 | decoder core | high while buffer has space; drops when full | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `in_data` | in | `BITS_PER_BEAT` | — | upstream | received bits, low-aligned | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `in_keep` | in | `BITS_PER_BEAT` | — | upstream | present-bit mask; partial only on final beat | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `in_last` | in | 1 | — | upstream | this beat carries the `N_BITS`-th received bit | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `in_erase` | in | `BITS_PER_BEAT` | — | upstream | (only with `ENABLE_ERASURES`) known-bad bits | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_valid` | out | 1 | 0 | decoder core | high once the block verdict is final | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_ready` | in | 1 | — | downstream | may depend on `out_valid` | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_data` | out | `BITS_PER_BEAT` | 0 | decoder core | corrected data bits; parity lanes dropped | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_keep` | out | `BITS_PER_BEAT` | 0 | decoder core | present-bit mask; partial only on final beat | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_last` | out | 1 | 0 | decoder core | this beat carries the `K_BITS`-th data bit | [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_status_ok` | out | 1 | 0 | decoder core | held for every beat: block had no errors | [syndrome unit](../ch02_blocks/02_syndrome_unit.md), [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_status_corrected` | out | `$clog2(T_BITS+1)` | 0 | decoder core | held for every beat: bits corrected (0 .. `T_BITS`) | [Chien search](../ch02_blocks/04_chien_search.md), [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_status_uncorrectable` | out | 1 | 0 | decoder core | held for every beat: correction failed; data pass through unchanged | [Chien search](../ch02_blocks/04_chien_search.md), [decoder core](../ch02_blocks/05_decoder_core.md) |
| `out_status_frame_err` | out | 1 | 0 | decoder core | held for every beat: block length was not `N_BITS` | [decoder core](../ch02_blocks/05_decoder_core.md) |

: Table 3.2: `bch_decoder_core` signal contract

## Timing rules

- `in_last` is the sole block boundary; the cores do not infer boundaries by
  counting.
- `out_status_*` describe the block being emitted and are valid on every beat
  of it, first to last. A consumer may sample them with `out_last` or with the
  first beat.
- An uncorrectable block leaves exactly as received; the corrector is disabled
  by `w_release_passthrough`.
