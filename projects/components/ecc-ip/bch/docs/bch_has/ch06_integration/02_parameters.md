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

# Parameter Configuration

Every parameter of the two cores and the standalone tops. **TBD** marks a
PRD decision not yet taken; the value shown is a placeholder, not a default.

## Code

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `FIELD_DIM` | int | 3..16 | **TBD** | m; the field is GF(2^m) | D1 |
| `T_BITS` | int | 1..(2^m-1)/2 | **TBD** | correctable bit errors per block | D2 |
| `N_BITS` | int | 2t+1 .. 2^m-1 | **TBD** | block length in bits; < 2^m-1 is a shortened code | D3 |
| `PRIM_POLY` | int | irreducible of degree m | **TBD** | primitive polynomial; selects the field representation | D8 |
| `FIRST_ROOT` | int | 0 .. 2^m-2 | **TBD** | b, first root of g(x); narrow-sense when b = 1 | D8 |
| `ENABLE_ERASURES` | bit | | 0 **TBD** | erasure input and erasure-locator logic (decoder) | D5 |
| `KES_ALGO` | string | `"RIBM"`, `"EUCLID"`, `"SMALL_T"` | **TBD** | key-equation solver | D11 |

: Table 6.1: Code parameters

Derived: `K_BITS = N_BITS - DEGREE_G`, where `DEGREE_G` is the degree of the
generator polynomial computed by `gf_pkg` from m, t, `PRIM_POLY` and
`FIRST_ROOT`; elaboration fails if `K_BITS` is below 1.

Every code parameter is fixed at elaboration (PRD D1-D3). There is no
run-time t or n: the arrays are generate loops sized by t, the generator
polynomial is computed by `gf_pkg` when the design elaborates, and a block
format change is a rebuild.

## Interface / build shape

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `BITS_PER_BEAT` | int | 1 .. k | **TBD** | number of bits per valid/ready beat; the bus is a slice of one codeword | D9 |
| `BUILD_ENCODER` | bit | | 1 **TBD** | include the encoder core | D4 |
| `BUILD_DECODER` | bit | | 1 **TBD** | include the decoder core | D4 |
| `INTAKE_IF` | string | `"NONE"`, `"AXIS"`, `"AXI4"` | `"NONE"` | intake adapter (standalone tops) | D9 |
| `OUTLET_IF` | string | `"NONE"`, `"AXIS"`, `"AXI4"` | `"NONE"` | outlet adapter | D9 |

: Table 6.2: Interface parameters

Adapter-specific parameters are in tables 4.5 and 4.7.

## Open decisions in one place

| Decision | What fixes it | Effect if left at the placeholder |
|---|---|---|
| D1 field dimension m | the first consumer's page or frame size | GF cell width, table size, Chien length are unresolved |
| D2 correctable bits t | the consumer's error model | parity count, solver size, Chien width are unresolved |
| D3 shortening | the consumer's block length | zero-fill on encode, position offset on decode are unresolved |
| D4 encoder/decoder mix | transmit-only, receive-only, or both | both cores are built; a consumer instantiates what it needs |
| D5 erasures | storage / RAID consumer says yes | no erasure port, smaller decoder |
| D6 throughput architecture | the consumer's clock and rate | the whole microarchitecture is unresolved |
| D8 generator conventions | the standard | field representation and generator taps are unresolved |
| D9 bits per beat and partial-beat mask | the consumer's datapath width | core port widths and adapter mapping are unresolved |
| D11 key-equation solver | area / latency target | solver cell counts and cycles are unresolved |
| D10 first consumer | you | none of the above changes until it appears |

: Table 6.3: Open PRD decisions and their placeholders
