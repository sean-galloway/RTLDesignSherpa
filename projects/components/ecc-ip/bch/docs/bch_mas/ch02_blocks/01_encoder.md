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

# Encoder Core (`bch_encoder_core`)

**Module:** `bch_encoder_core.sv`
**Location:** `rtl/macro/`
**Category:** streaming datapath
**Parent:** `bch_top` / standalone encoder wrapper
**Status:** landed — `rtl/macro/bch_encoder_core.sv`, gate DV green on the three standing profiles

---

## Purpose

`bch_encoder_core` systematically encodes a `K_BITS`-bit data block into an
`N_BITS`-bit BCH codeword. Data bits pass through unchanged; the block then
appends the `N_BITS - K_BITS` parity bits produced by a GF(2^m) LFSR whose taps
come from the generator polynomial computed by `gf_pkg`. The output stream is
longer than the input stream, so the encoder is not a pure back-to-back
pipeline: it holds `in_ready` low while parity drains.

### Figure 2.1: Encoder core block diagram

![Encoder core block diagram](../assets/graphviz/bch_encoder_core.png)

## Parameters

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `FIELD_DIM` | int | 3..16 | **TBD** | `m`; field is GF(2^m) | D1 |
| `T_BITS` | int | 1..(2^m-1)/2 | **TBD** | correctable bit errors | D2 |
| `N_BITS` | int | 2t+1 .. 2^m-1 | **TBD** | codeword length in bits | D3 |
| `BITS_PER_BEAT` | int | 1 .. K_BITS | **TBD** | bits per valid/ready beat | D9 |

: Table 2.1: Encoder core parameters

Derived: `K_BITS = N_BITS - DEGREE_G`, where `DEGREE_G` is the degree of the
generator polynomial computed by `gf_pkg` from `m`, `t`, and the profile
parameters. `DEGREE_G` is at most `m * T_BITS` and equals `N_BITS - K_BITS`.

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `aclk` | in | 1 | one clock for the whole core |
| `aresetn` | in | 1 | active-low synchronous reset |
| `in_valid` | in | 1 | a beat of data bits is offered |
| `in_ready` | out | 1 | the core takes it this cycle |
| `in_data` | in | `BITS_PER_BEAT` | data bits, bit 0 in the low bit; partial final beat uses `in_keep` |
| `in_keep` | in | `BITS_PER_BEAT` | present-bit mask, low-aligned; partial only on the block's final beat |
| `in_last` | in | 1 | this beat carries the `K_BITS`-th data bit |
| `out_valid` | out | 1 | a beat of coded bits is offered |
| `out_ready` | in | 1 | the consumer takes it |
| `out_data` | out | `BITS_PER_BEAT` | data bits while `!w_parity_phase`, parity bits while `w_parity_phase` |
| `out_keep` | out | `BITS_PER_BEAT` | present-bit mask; partial at the end of data and at the end of parity |
| `out_last` | out | 1 | this beat carries the `N_BITS`-th coded bit |
| `frame_err` | out | 1 | pulse: a block ended with other than `K_BITS` data bits |

: Table 2.2: Encoder core ports

## Microarchitecture internals

### Beat-parallel LFSR parity generator

The core works on whole B-bit beats; there is no serialiser. The parity
register `r_lfsr` holds deg(g) lanes of m bits over GF(2^m), with the
generator polynomial's coefficients (computed by `bch_pkg` from `FIELD_DIM`,
`PRIM_POLY`, `T_BITS` and `FIRST_ROOT`) on its taps. Its next-state logic is
a chain of B `lfsr_step()` evaluations, one per bit of the beat (bit 0
first), built as an unpacked array `w_chain[0..B]`; the keep count of the
beat selects `w_chain[keep count]`, so a partial final data beat advances
the register by exactly the bits present. The multiplies use `gf_mul_fn`
from the imported `gf_pkg`; no `gf_lfsr_encoder` instance is used.

The register loads on every accepted data beat. During the parity drain it
shifts left by one beat's worth of lanes each emitted beat, so it is all-zero
again when the drain ends and the next block needs no explicit clear.

### Parity mux

The output mux selects data bits while the block is in the data phase and
parity bits once the data phase completes:

```
w_parity_phase = (r_bit_count >= K_BITS) && w_beat_is_parity
```

`w_beat_is_parity` is true whenever the current output position is inside the
parity region; it is derived from the same bit counter:

```
w_beat_is_parity = (r_bit_count + BITS_PER_BEAT - 1) >= K_BITS
```

The mux output is `out_data = w_parity_phase ? w_parity_bits : w_data_bits`.

### Output skid

There is no bit packer. `{last, keep, data}` from the output select goes into
one `gaxi_skid_buffer` (`u_out_skid`, depth `SKID_DEPTH`, 2..8), whose read
side is the output port. `out_keep` is full except on the final data beat
and the final parity beat, where it marks the partial beat. `out_last` raises
on the beat that carries the `N_BITS`-th coded bit:

```
w_enc_out_last = w_parity_phase &&
                 (r_parity_count + w_par_beat_len - 1 == N_BITS - K_BITS - 1)
```

## FSM policy

This block carries **no FSM** (per `vault/handbook/design/streaming-no-fsm.md`).
The sequencing that another design might put in a state machine is replaced by:

- `r_bit_count`: counts input/output bit position in the block, 0 .. `N_BITS-1`
- `r_parity_count`: counts parity bits emitted, 0 .. `N_BITS-K_BITS-1`
- `r_drain`: set by the accepted `in_last` beat, cleared by the last parity beat
- `w_parity_phase`: combinational qualifier selecting parity vs data
- `w_last`: combinational qualifier marking the final output beat

`in_ready` is combinational: `!r_drain && w_skid_wr_ready`, the output
skid's write-side ready qualified by the drain flag.

## Timing

- One input beat is accepted per cycle while `in_ready` is high.
- The data phase is `ceil(K_BITS / BITS_PER_BEAT)` beats.
- The parity phase is `ceil((N_BITS - K_BITS) / BITS_PER_BEAT)` beats.
- `in_ready` is held low during the parity phase; back-to-back blocks need an
  upstream FIFO sized for at least `N_BITS - K_BITS` bits.
- The exact blocks-per-cycle numbers are placeholders tied to PRD D6 and D9.

## Notes

- **Wrong-length block handling:** If `in_last` arrives before or after the
  `K_BITS`-th data bit, `frame_err` pulses and the block is still encoded as
  given (systematic data pass-through with parity appended to whatever data
  arrived). This is the encoder-side analog of the decoder's
  `out_status_frame_err` (R1/R2):

  ```
  w_frame_err = in_last && (r_data_count + keep_count != K_BITS)
  ```
- **OFF-state testing convention:** For tests that need to verify the core
  tolerates idle cycles, the LFSR drains to zero with the last parity beat and
  the output skid stalls cleanly when `out_ready` is low.
- The LFSR is configured by the same `FIELD_DIM`, `T_BITS`, `N_BITS`,
  `PRIM_POLY`, and `FIRST_ROOT` parameters as the rest of the codec; its
  generator polynomial comes from `bch_pkg` (PRD D3/D8).
