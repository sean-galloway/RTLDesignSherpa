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

# Core Signals

This page presents the valid/ready core signals as a contract table rather
than restating the prose interface description in
`../reed_solomon_has/ch04_interfaces/01_core_interface.md`. The direction,
reset value, and creator block for each signal are the source of truth here.

## Reset strategy

All core logic uses **synchronous active-low reset** (`aresetn`), the house
clocking convention. Reset clears block state, counters, and control flags;
the data-carrying arrays themselves are not reset. In `rs_encoder_core.sv`
the reset block clears `r_drain`, `r_count`, `r_drain_left`, and `frame_err`
(`rs_encoder_core.sv:191-195`); the LFSR parity registers and the output skid
buffer contents are not reset, and their pointers make the old contents
logically invalid until overwritten. In `rs_decoder_core.sv` reset clears the
stage-A receive counters, the descriptor skid and FIFO control flags, the
stage-B solver handshake state, and the stage-C walk/output/status pipeline
(`rs_decoder_core.sv:279-290`, `461-484`, `538-566`, `735-754`, `799-843`,
`849-862`); the block FIFO and output FIFO data arrays are not reset.

## `rs_encoder_core` signal contract

| Signal | Dir | Width | Reset value | Creates / consumes | Contract | Source block page |
|---|---|---|---|---|---|---|
| `aclk` | in | 1 | — | clock source | one clock for the whole core | — |
| `aresetn` | in | 1 | — | reset source | synchronous active-low reset | — |
| `in_valid` | in | 1 | — | upstream | stable until `in_ready` high | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_ready` | out | 1 | 0 | encoder core | combinational `!r_drain && w_skid_wr_ready`; low during parity drain | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_data` | in | `DATA_WIDTH` | — | upstream | data symbols, low-aligned; partial final beat qualified by `in_keep` | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_keep` | in | `SYMBOLS_PER_BEAT` | — | upstream | present-symbol mask, low-aligned; partial only on final beat | [encoder core](../ch02_blocks/01_encoder.md) |
| `in_last` | in | 1 | — | upstream | this beat carries the k-th data symbol | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_valid` | out | 1 | 0 | encoder core | registered skid output; data beats then parity beats | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_ready` | in | 1 | — | downstream | may depend on `out_valid` | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_data` | out | `DATA_WIDTH` | 0 | encoder core | data while `!r_drain`, parity while `r_drain` | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_keep` | out | `SYMBOLS_PER_BEAT` | 0 | encoder core | full except on final data and final parity beats | [encoder core](../ch02_blocks/01_encoder.md) |
| `out_last` | out | 1 | 0 | encoder core | this beat carries the n-th coded symbol | [encoder core](../ch02_blocks/01_encoder.md) |
| `frame_err` | out | 1 | 0 | encoder core | pulse when `in_last` does not coincide with k data symbols | [encoder core](../ch02_blocks/01_encoder.md) |

: Table 3.1: `rs_encoder_core` signal contract

## `rs_decoder_core` signal contract

| Signal | Dir | Width | Reset value | Creates / consumes | Contract | Source block page |
|---|---|---|---|---|---|---|
| `in_valid` | in | 1 | — | upstream | stable until `in_ready` high | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `in_ready` | out | 1 | 0 | decoder core | high while block FIFO and A->B descriptor skid have space | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `in_data` | in | `DATA_WIDTH` | — | upstream | received symbols, low-aligned | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `in_keep` | in | `SYMBOLS_PER_BEAT` | — | upstream | present-symbol mask; partial only on final beat | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `in_last` | in | 1 | — | upstream | this beat carries the n-th received symbol | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `in_erasure` | in | `SYMBOLS_PER_BEAT` | — | upstream | per-lane known-bad symbol flags; dead unless `ERASURE_SUPPORT` | [erasure unit](../ch02_blocks/07_erasure_unit.md), [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_valid` | out | 1 | 0 | decoder core | high once the block verdict is final | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_ready` | in | 1 | — | downstream | may depend on `out_valid` | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_data` | out | `DATA_WIDTH` | 0 | decoder core | corrected data symbols; parity lanes dropped | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_keep` | out | `SYMBOLS_PER_BEAT` | 0 | decoder core | present-symbol mask; partial only on final beat, data lanes only | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_last` | out | 1 | 0 | decoder core | this beat carries the k-th data symbol | [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_status_ok` | out | 1 | 0 | decoder core | held for every beat: block had no errors | [syndrome unit](../ch02_blocks/02_syndrome_unit.md), [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_status_corrected` | out | `STATUS_CNT_WIDTH` | 0 | decoder core | held for every beat: symbols corrected (0 .. t, or 0 .. 2t with erasures) | [Chien search](../ch02_blocks/05_chien_search.md), [Forney evaluator](../ch02_blocks/06_forney_evaluator.md), [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_status_uncorrectable` | out | 1 | 0 | decoder core | held for every beat: correction failed; data pass through unchanged | [Chien search](../ch02_blocks/05_chien_search.md), [Forney evaluator](../ch02_blocks/06_forney_evaluator.md), [decoder core](../ch02_blocks/08_decoder_core.md) |
| `out_status_frame_err` | out | 1 | 0 | decoder core | held for every beat: block length was not n | [decoder core](../ch02_blocks/08_decoder_core.md) |

: Table 3.2: `rs_decoder_core` signal contract

`STATUS_CNT_WIDTH` is `ERASURE_SUPPORT ? $clog2(2*T_SYMBOLS+1) : $clog2(T_SYMBOLS+1)`
(`rs_decoder_core.sv:133-134`).

## Timing rules

- `in_last` is the sole block boundary; the cores do not infer boundaries by
  counting.
- `out_status_*` describe the block being emitted and are valid on every beat
  of it, first to last. A consumer may sample them with `out_last` or with the
  first beat.
- An uncorrectable block leaves exactly as received; the corrector is disabled
  by `out_status_uncorrectable` at the output mux (`rs_decoder_core.sv:931-933`).
