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

# Resources

Analytic counts at revision 0.1, from `docs/rs_fub_catalog.md`; no synthesis
has been run. Chapter 6.5 is the plan that replaces this table with
measurements.

## GF primitives per core, reference profile

| Primitive | Encoder | Decoder (riBM) | Decoder (Euclid) | Formula |
|---|---:|---:|---:|---|
| `gf_mul_const` | 16 | 33 | 33 | encoder 2t; decoder 2t + (t+1) + t |
| `gf_mul` | 0 | 52 | 66 | riBM 2(3t+1) + 2; Euclid 8t + 2; + t with erasures |
| `gf_inv` | 0 | 1 | 1 | one, in Forney |
| GF symbol registers | 16 | 75 | 89 | encoder 2t; decoder 2t + (t+1) + solver array |

: Table 5.5: GF primitive counts, RS(255,239), t = 8, m = 8, S = 1

## Storage

| Item | Size | Formula |
|---|---|---|
| block FIFO | 512 x 8 bits (one BRAM) | (n + 2t + 8, rounded up) x m (+1 erasure bit when built) |
| output FIFO | 512 x 18 bits (one BRAM) | (2k + 8, rounded up) x (2m + 2): received symbol, correction, hit, last |
| re-check syndromes | 2t cells | a second `syndrome_unit` over the corrected stream |
| log / antilog tables (`gf_inv`) | 2 x 256 x 8 bits | 2 x 2^m x m; LUT ROM at m = 8, BRAM at m = 10 |
| skid buffers | 2 (encoder), 3 (decoder), 2 deep | stage boundaries |

: Table 5.6: Storage

## Order of magnitude

A `gf_mul_const` at m = 8 is at most 8 XOR trees of up to 8 inputs; a
`gf_mul` is an 8 x 8 AND array with reduction, on the order of 60-80 LUT6
equivalents. That puts the reference decoder's arithmetic near 4-5 k LUTs on
a 7-series part before control and the buffer, and the encoder near 200. The
converters-area dwidth blocks and the bridge's monitors give the repository
calibration points for what a block of this size does on Artix-7 and
Kintex-7; the first out-of-context run will say where the RS decoder lands.

## Scaling

- CCSDS RS(255,223), t = 16: every 2t-scaled row doubles (32 syndrome cells,
  49 riBM elements, 17 Chien cells); plus the dual-basis conversion at both
  boundaries.
- 802.3 RS(544,514), m = 10: every multiplier grows from 8 x 8 to 10 x 10,
  the tables to 1024 entries, the buffer to 1024 deep; S > 1 is a
  requirement, not an option, at those rates.
- S symbols per beat: syndrome and Chien cells x S; solver unchanged.
