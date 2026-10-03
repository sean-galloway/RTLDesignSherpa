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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Block Inventory

The MAS documents the target blocks below. Each page follows the FUB-page
skeleton from the pumice MAS: header metadata, purpose, parameters, interface,
microarch internals, timing, and notes. The GF(2^m) primitives are imported
from the reed-solomon component per PRD D7 and are not re-documented here.

| Block | RTL target | Role | MAS page |
|---|---|---|---|
| `bch_encoder_core` | `rtl/bch_encoder_core.sv` | Systematic encoder: bit serialiser, GF LFSR parity generator, parity mux, bit packer | [01_encoder.md](../ch02_blocks/01_encoder.md) |
| `bch_syndrome_unit` | `rtl/bch_syndrome_unit.sv` | Computes the `t` odd syndromes `S_1 ... S_2t-1` over the serial bit stream using `t` parallel GF MAC lanes | [02_syndrome_unit.md](../ch02_blocks/02_syndrome_unit.md) |
| `bch_key_equation_solver` | `rtl/bch_key_equation_solver.sv` | Inverts the key equation from odd syndromes to error-locator `Lambda(x)`; D11 selects riBM, Euclid, or step-by-step/PGZ | [03_key_equation_solver.md](../ch02_blocks/03_key_equation_solver.md) |
| `bch_chien_search` | `rtl/bch_chien_search.sv` | Evaluates `Lambda(x)` at all `N_BITS` bit positions, flags roots, flips bits; no Forney stage | [04_chien_search.md](../ch02_blocks/04_chien_search.md) |
| `bch_decoder_core` | `rtl/bch_decoder_core.sv` | Block buffer + stage sequencer between syndrome, solver, Chien, and corrector; exactly one minimal control FSM | [05_decoder_core.md](../ch02_blocks/05_decoder_core.md) |

: Table 1.1: MAS block inventory

The GF layer is imported, not duplicated:

| Primitive | Source in `projects/components/ecc-ip/reed-solomon/rtl/fub/gf/` | Used by |
|---|---|---|
| `gf_pkg` | `gf_pkg.sv` | all blocks (tables, constants, generator polynomial) |
| `gf_mul` | `gf_mul.sv` | syndrome unit, key-equation solver, Chien search |
| `gf_mul_const` | `gf_mul_const.sv` | LFSR encoder taps, Chien Horner cells |
| `gf_inv` | `gf_inv.sv` | Euclidean solver only (if D11 selects EUCLID) |

: Table 1.2: Imported GF primitives

The adapter blocks (`axis_adapter`, `axi4_job_adapter`, register block) are
specified in `../bch_has/ch04_interfaces/` and are not taken to the signal
level in this MAS.
