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
PRD decision not yet taken; the value shown is the working default the
reference profile uses.

## Code

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `SYMBOL_WIDTH` | int | 3..16 | 8 | m; the field is GF(2^m) | D1 decided |
| `T_SYMBOLS` | int | 1..(2^m-1)/2 | 8 | correctable symbols per block; 2t parity | D2 decided |
| `N_SYMBOLS` | int | 2t+1 .. 2^m-1 | 2^m - 1 | block length; < 2^m-1 is a shortened code | D3 decided |
| `PRIM_POLY` | int | irreducible of degree m | 0x11D | primitive polynomial; selects the field representation | D8 per profile |
| `FIRST_ROOT` | int | 0 .. 2^m-2 | 0 **TBD** | b, first root of g(x); DVB 0, CCSDS 112 | D8 |
| `DUAL_BASIS` | bit | | 0 | CCSDS dual-basis symbol representation at the boundaries | D8 |
| `ENABLE_ERASURES` | bit | | 0 **TBD** | erasure input and erasure-locator logic (decoder) | D5 |
| `KES_ALGO` | string | `"RIBM"`, `"EUCLID"` | `"RIBM"` | key-equation solver | D11 decided |

: Table 6.1: Code parameters

Derived: `K_SYMBOLS = N_SYMBOLS - 2*T_SYMBOLS`; elaboration fails if it is below 1.

Every code parameter is fixed at elaboration (Sean, 2026-09-30). There is no
run-time t or n: the arrays are generate loops sized by t, the generator
polynomial is computed by `gf_pkg` when the design elaborates, and a block
format change is a rebuild. A consumer that must mix formats in one instance
would need a `T_MAX` sizing parameter and a `cfg_t` register, which is not in
this specification.

## Interface

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `DATA_WIDTH` | int | multiple of `SYMBOL_WIDTH` | 8 | beat width; elaboration fails if not a multiple | D1 decided |
| `SYMBOLS_PER_BEAT` | derived | | 1 | `DATA_WIDTH / SYMBOL_WIDTH`, the throughput factor | D6 |
| `INTAKE_IF` | string | `"NONE"`, `"AXIS"`, `"AXI4"` | `"NONE"` | intake adapter (standalone tops) | D9 decided |
| `OUTLET_IF` | string | `"NONE"`, `"AXIS"`, `"AXI4"` | `"NONE"` | outlet adapter | D9 decided |
| `ENABLE_SCRAMBLER` | bit | | 0 | line scrambler stage | D12 decided |
| `SCRAMBLER_POLY`, `SCRAMBLER_SEED`, `SCRAMBLER_AFTER_ENCODER` | int, int, bit | | DVB values | the standard's PRBS | D12 |

: Table 6.2: Interface parameters

Adapter-specific parameters are in tables 4.5 and 4.7.

## Open decisions in one place

| Decision | What fixes it | Effect if left at the default |
|---|---|---|
| D4 encoder-only | a transmit-only or RAID-write consumer | both cores are built; a consumer instantiates what it needs |
| D5 erasures | storage / RAID consumer says yes | no erasure port, smaller decoder |
| D8 conventions | the standard | b = 0, no dual basis |
| D10 first consumer | you | none of the above changes until it appears |

: Table 6.3: Open PRD decisions and their defaults
