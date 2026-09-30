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

# Core Interface

Both cores present the house valid/ready streaming contract
(`vault/handbook/design/valid-ready-contracts.md`) at each end: `valid` and
`data` are held stable until `ready`, `ready` may depend on `valid`,
`valid` must not depend on `ready`. Widths are in bits; `S` is
`SYMBOLS_PER_BEAT` and `m` is `SYMBOL_WIDTH`.

## Clock and reset

| Port | Dir | Width | Description |
|---|---|---|---|
| `aclk` | in | 1 | one clock for the whole core |
| `aresetn` | in | 1 | active-low asynchronous reset, per the repository convention |

: Table 4.1: Clock and reset

## `rs_encoder_core`

| Port | Dir | Width | Description |
|---|---|---|---|
| `in_valid` | in | 1 | a beat of data symbols is offered |
| `in_ready` | out | 1 | the core takes it this cycle |
| `in_data` | in | S x m | S data symbols, symbol 0 in the low bits |
| `in_keep` | in | S | which symbols of the beat are present: low-aligned, all ones except possibly the final beat of a block |
| `in_last` | in | 1 | this beat carries the k-th data symbol of the block |
| `out_valid` | out | 1 | a beat of coded symbols is offered |
| `out_ready` | in | 1 | the consumer takes it |
| `out_data` | out | S x m | S coded symbols: the data beats as received, then the 2t parity symbols in ceil(2t/S) beats |
| `out_keep` | out | S | present-symbol mask of the beat: partial at the end of the data and at the end of the parity when S divides neither k nor 2t |
| `out_last` | out | 1 | this beat carries the n-th coded symbol of the block |
| `frame_err` | out | 1 | pulse: a block ended with other than k data symbols; it was still encoded as given |

: Table 4.2: Encoder core ports

## `rs_decoder_core`

| Port | Dir | Width | Description |
|---|---|---|---|
| `in_valid` / `in_ready` | in / out | 1 | as the encoder |
| `in_data` | in | S x m | S received symbols |
| `in_keep` | in | S | present-symbol mask |
| `in_last` | in | 1 | this beat carries the n-th received symbol |
| `in_erase` | in | S | (only with `ENABLE_ERASURES`) symbol is a known erasure |
| `out_valid` / `out_ready` | out / in | 1 | as the encoder |
| `out_data` | out | S x m | S corrected data symbols; parity lanes are dropped, so the block is k symbols in ceil(k/S) beats |
| `out_keep` | out | S | present-symbol mask, low-aligned, partial only on the block's final beat |
| `out_last` | out | 1 | this beat carries the k-th data symbol of the block |
| `out_status_ok` | out | 1 | held for every beat of the block: it had no errors |
| `out_status_corrected` | out | log2(t)+1 | held for every beat of the block: symbols corrected (0 .. t) |
| `out_status_uncorrectable` | out | 1 | held for every beat of the block: correction failed; the data are exactly as received |
| `out_status_frame_err` | out | 1 | held for every beat of the block: block length was not n; the block passes through uncorrected, its first length - 2t symbols as data |

: Table 4.3: Decoder core ports

## Timing rules

- `in_last` is the block boundary. The core does not infer boundaries by
  counting; it checks the count against n (or k) and reports a mismatch.
- The encoder holds `in_ready` low while it drains the parity of the
  previous block, ceil(2t/S) cycles (chapter 3.2); a consumer wanting no gap
  buffers that many beats upstream.
- `keep` masks are low-aligned. A partial beat anywhere but a block's last
  is a framing error on the decoder and a count mismatch on the encoder.
- The decoder accepts the next block while it is still correcting the
  previous one, up to the depth of its block buffer; `in_ready` falls only
  when the buffer is full, which under sustained back-pressure on `out_ready`
  it will be.
- Status outputs describe the block being emitted and are valid on every
  beat of it, first to last; a consumer may sample them with `out_last` or
  with the first beat. A block is not released until its verdict is final, so
  an uncorrectable verdict is never preceded by altered symbols.
- Reset clears block state and the syndrome and parity registers; the block
  buffer is not reset (its contents are indexed by pointers that are).

## Erasures (`ENABLE_ERASURES`, PRD D5 TBD)

When enabled, `in_erase` marks symbols the consumer already knows are bad
(a failed device, a dropped packet). Each erasure costs one parity symbol
instead of two: the decoder corrects e errors and f erasures with
2e + f <= 2t. When disabled the port does not exist and the erasure-locator
logic is not generated.
