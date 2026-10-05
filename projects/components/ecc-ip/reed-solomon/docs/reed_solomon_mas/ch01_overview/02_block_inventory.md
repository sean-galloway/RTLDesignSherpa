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

# Block Inventory

The MAS documents the landed blocks below. Each page follows the FUB-page
skeleton from the pumice and BCH MASes: header metadata, purpose, parameters,
interface, microarchitecture internals, FSM policy, timing, and notes. The
landed RTL is the ground truth; the pre-RTL FUB catalog is the plan this
inventory checks it against (drift collected in Table 1.3).

| Block | RTL | Role | MAS page |
|---|---|---|---|
| `rs_encoder_core` | `rtl/macro/rs_encoder_core.sv` | Systematic encoder core, valid/ready at both ends: data beats pass through, `gf_lfsr_encoder` computes parity, parity drains behind the data | [01_encoder.md](../ch02_blocks/01_encoder.md) |
| `syndrome_unit` | `rtl/fub/syndrome_unit.sv` | The 2t syndromes `S_i = r(alpha^(b+i))` computed by `gf_syndrome_cell` Horner lanes as the block streams in; all-zero flag | [02_syndrome_unit.md](../ch02_blocks/02_syndrome_unit.md) |
| `key_equation_solver_ribm` | `rtl/fub/key_equation_solver_ribm.sv` | Default solver (D11): 3t+1 `ribm_pe` cells, 2t iterations, locator + evaluator out | [03_key_equation_solver_ribm.md](../ch02_blocks/03_key_equation_solver_ribm.md) |
| `key_equation_solver_euclid` | `rtl/fub/key_equation_solver_euclid.sv` | Alternative solver (D11): inversionless modified Euclidean, top-aligned polynomials, early stop | [04_key_equation_solver_euclid.md](../ch02_blocks/04_key_equation_solver_euclid.md) |
| `chien_search` | `rtl/fub/chien_search.sv` | Locator root search over the n positions, S lanes per cycle; root flags and the odd-index derivative sum for Forney | [05_chien_search.md](../ch02_blocks/05_chien_search.md) |
| `forney_evaluator` | `rtl/fub/forney_evaluator.sv` | Error magnitude per lane: Omega and the derivative at each located root, one inverse and multiply per lane | [06_forney_evaluator.md](../ch02_blocks/06_forney_evaluator.md) |
| `rs_erasure_unit` | `rtl/fub/rs_erasure_unit.sv` | Erasure support (D5): builds the erasure locator during receive and combines it with the syndrome locator for the solver; generated only when `ERASURE_SUPPORT = 1` | [07_erasure_unit.md](../ch02_blocks/07_erasure_unit.md) |
| `rs_decoder_core` | `rtl/macro/rs_decoder_core.sv` | Decoder integration: block buffer, descriptor skids, solve bypass, Chien/Forney correct walk, second syndrome unit, verdict and release | [08_decoder_core.md](../ch02_blocks/08_decoder_core.md) |

: Table 1.1: MAS block inventory

The GF(2^m) leaf primitives are documented inside their parent pages rather
than given pages of their own; they are collected here so the inventory is
complete:

| Primitive | RTL | Used by |
|---|---|---|
| `gf_pkg` | `rtl/fub/gf/gf_pkg.sv` | all blocks (constant functions: multiply, powers, inverse, log, primitivity check) |
| `gf_mul` | `rtl/fub/gf/gf_mul.sv` | riBM/Euclid solver arrays, Forney |
| `gf_mul_const` | `rtl/fub/gf/gf_mul_const.sv` | syndrome cells, encoder taps, Chien load/step, Forney constants |
| `gf_inv` | `rtl/fub/gf/gf_inv.sv` | Forney (log/negate/antilog tables; Itoh-Tsujii above m = 12) |
| `gf_syndrome_cell` | `rtl/fub/gf/gf_syndrome_cell.sv` | `syndrome_unit` (2t instances) |
| `gf_lfsr_encoder` | `rtl/fub/gf/gf_lfsr_encoder.sv` | `rs_encoder_core` |
| `ribm_pe` | `rtl/fub/gf/ribm_pe.sv` | `key_equation_solver_ribm` (3t+1 instances) |

: Table 1.2: GF leaf primitives

Support blocks that are not taken to the signal level in this MAS:

| Block | RTL | Why it has no page here |
|---|---|---|
| `rs_beat_packer` | `rtl/fub/rs_beat_packer.sv` | Adapter-side repacker; the HAS (chapter 4.2/4.3) specifies its job, its header documents its own contract |
| `error_injector` | `projects/components/utility-ip/misc/rtl/error_injector.sv` | DV stimulus (shared with BCH), documented in its header; not part of the deliverable datapath |
| `rs_pkg` | `rtl/fub/rs_pkg.sv` | shared types/parameters package |
| AXIS/AXI4 tops and engines | `rtl/top/*.sv` | specified at the interface level in `../reed_solomon_has/ch04_interfaces/` |

: Table 1.3: Support blocks covered elsewhere

## Drift from the pre-RTL catalog

The FUB catalog (`docs/rs_fub_catalog.md`, 2026-09-29) was the build plan.
The landed tree decomposed a few planned blocks differently:

| Catalog plan | Landed reality | Where |
|---|---|---|
| `erasure_locator` leaf building the erasure polynomial | `rs_erasure_unit`: erasure locator and solver combination in one generated block riding the A→B descriptor | chapter 2.7 |
| `symbol_unpack` / `symbol_pack` / `parity_mux` leaves | beat slicing, keep handling, and the parity append are inline in the two cores; contiguous repacking is the separate `rs_beat_packer` at the adapter boundary | chapters 2.1, 2.8 |
| `chien_cell` leaf, `euclid_pe` as generate-loop logic | same structure as planned: per-coefficient cells live inside `chien_search` and `key_equation_solver_euclid` as generate loops | chapters 2.5, 2.4 |
| `line_randomizer` scrambler (D12, decided) | not landed yet; no scrambler RTL exists in the tree as of this revision | — |

: Table 1.4: Catalog-to-RTL drift

Where a block page and the catalog disagree on internals, the page wins —
it was written against the `.sv` file.
