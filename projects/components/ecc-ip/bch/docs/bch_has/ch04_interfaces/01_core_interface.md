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
`valid` must not depend on `ready`. Widths are in bits; `B` is
`BITS_PER_BEAT` (PRD D9 TBD).

## Clock and reset

| Port | Dir | Width | Description |
|---|---|---|---|
| `aclk` | in | 1 | one clock for the whole core |
| `aresetn` | in | 1 | active-low reset, per the component convention (chapter 4.5) |

: Table 4.1: Clock and reset

## `bch_encoder_core`

| Port | Dir | Width | Description |
|---|---|---|---|
| `in_valid` | in | 1 | a beat of data bits is offered |
| `in_ready` | out | 1 | the core takes it this cycle |
| `in_data` | in | B | B data bits, bit 0 in the low bit **TBD / D9** |
| `in_keep` | in | B | which bits of the beat are present: low-aligned, all ones except possibly the final beat of a block **TBD / D9** |
| `in_last` | in | 1 | this beat carries the k-th data bit of the block |
| `out_valid` | out | 1 | a beat of coded bits is offered |
| `out_ready` | in | 1 | the consumer takes it |
| `out_data` | out | B | B coded bits: the data beats as received, then the n - k parity bits **TBD / D9** |
| `out_keep` | out | B | present-bit mask of the beat: partial at the end of the data and at the end of the parity **TBD / D9** |
| `out_last` | out | 1 | this beat carries the n-th coded bit of the block |
| `frame_err` | out | 1 | pulse: a block ended with other than k data bits; it was still encoded as given |

: Table 4.2: Encoder core ports

## `bch_decoder_core`

| Port | Dir | Width | Description |
|---|---|---|---|
| `in_valid` / `in_ready` | in / out | 1 | as the encoder |
| `in_data` | in | B | B received bits **TBD / D9** |
| `in_keep` | in | B | present-bit mask **TBD / D9** |
| `in_last` | in | 1 | this beat carries the n-th received bit |
| `in_erase` | in | B | (only with `ENABLE_ERASURES`) bit is a known erasure **TBD / D5** |
| `out_valid` / `out_ready` | out / in | 1 | as the encoder |
| `out_data` | out | B | B corrected data bits; parity lanes are dropped, so the block is k bits **TBD / D9** |
| `out_keep` | out | B | present-bit mask, low-aligned, partial only on the block's final beat **TBD / D9** |
| `out_last` | out | 1 | this beat carries the k-th data bit of the block |
| `out_status_ok` | out | 1 | held for every beat of the block: it had no errors |
| `out_status_corrected` | out | log2(t)+1 | held for every beat of the block: bits corrected (0 .. t) |
| `out_status_uncorrectable` | out | 1 | held for every beat of the block: correction failed; the data are exactly as received |
| `out_status_frame_err` | out | 1 | held for every beat of the block: block length was not n; the block passes through uncorrected, its first length - (n - k) bits as data |

: Table 4.3: Decoder core ports

## Timing rules

- `in_last` is the block boundary. The core does not infer boundaries by
  counting; it checks the count against n (or k) and reports a mismatch.
- The encoder holds `in_ready` low while it drains the parity of the
  previous block. A consumer wanting no gap buffers that many beats upstream.
- Keep masks are low-aligned. A partial beat anywhere but a block's last
  is a framing error on the decoder and a count mismatch on the encoder.
- The decoder accepts the next block while it is still correcting the
  previous one, up to the depth of its block buffer; `in_ready` falls only
  when the buffer is full, which under sustained back-pressure on `out_ready`
  it will be.
- Status outputs describe the block being emitted and are valid on every
  beat of it, first to last; a consumer may sample them with `out_last` or
  with the first beat. A block is not released until its verdict is final, so
  an uncorrectable verdict is never preceded by altered bits.
- Reset clears block state and the parity and syndrome registers; the block
  buffer is not reset (its contents are indexed by pointers that are).

## Erasures (`ENABLE_ERASURES`, PRD D5 TBD)

When enabled, `in_erase` marks bits the consumer already knows are bad
(a known-bad page region). Each erasure costs one parity bit instead of two:
  the decoder corrects e errors and f erasures with 2e + f <= 2t. The exact
mapping of a per-beat or per-job erasure bitmap to `in_erase` is part of the
D5 / D9 adapter work. When disabled the port does not exist and the
erasure-locator logic is not generated.
