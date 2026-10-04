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

# Binary BCH Codec Component

**Status:** RTL landed 2026-10-03 -- fub blocks (syndrome, key-equation solver, Chien search) + encoder/decoder macro cores, dv gate tests running; PRD v0.1, HAS v0.1 and MAS v0.1 alongside
**Tracker:** `vault/Tasks/projects/components/ecc-ip/bch/` (TASK-005 is the RTL bring-up)

## What this is

A binary BCH encoder / decoder component: GF(2^m) arithmetic, systematic
cyclic encoding, syndrome computation, key-equation solving (Berlekamp-Massey,
Euclidean, or the small-t direct/PGZ family), Chien search with plain bit-flip
correction -- behind a valid/ready streaming interface in the house style. It
is its own component rather than a mode of the reed-solomon codec because the
code is different in kind (bit-oriented, no symbol framing, no Forney stage)
even though the field arithmetic is shared; that separation was decided with
the RS PRD's D7 (2026-09-29, Sean).

## What is here today

| Path | What |
|---|---|
| [`PRD.md`](PRD.md) | requirements draft v0.1: the decisions that pick the code (m, t, shortening, solver, throughput, consumer) and the candidate profiles from the standards and papers in `References/` |
| [`References/`](References/README.md) | the papers and standards, with source and licence for each: both Massey BCH papers from his ETH archive, the CCSDS TC Blue Book (the free standard whose coding is a BCH code), the Guruswami-Rudra-Sudan coding-theory draft, the flash-memory reliability literature (Cai/Mutlu, Nabipour); plus a cited list of the classic papers and the open-source implementations worth a reuse survey |
| [`docs/`](docs/) | HAS v0.1 (target architecture, one chapter per open PRD decision) and MAS v0.1 per-block specs (encoder, syndrome unit, KES, Chien search, decoder core) |
| [`rtl/`](rtl/) | fub blocks (`bch_pkg`, `bch_syndrome_unit`, `bch_key_equation_solver`, `bch_chien_search`) + macro cores (`bch_encoder_core`, `bch_decoder_core`), filelists, lint reports; the GF(2^m) layer is imported from reed-solomon per PRD D7 |
| [`dv/`](dv/) | cocotb gate tests per block (`dv/tests/fub/`), parametrized over the (m, n, t, s) matrix (e.g. m13/n4224/t8, m06/n63/t2) |
| [`CLAUDE.md`](CLAUDE.md) | area facts for a session working here |

## Where to start

1. Read `References/README.md` in the order it suggests: Massey 1969 for
   the key-equation algorithm, Massey 1965 for the no-key-equation
   alternative, the CCSDS TC Blue Book section 3 for a worked (63,56)
   generator, then the Guruswami-Rudra-Sudan chapters on finite fields and
   BCH codes as the theory backbone.
2. Read the PRD's decision table. BCH's open questions mirror RS's, plus two
   that are BCH-specific: the binary evenness shortcut (only t odd syndromes
   are independent) and the absence of a Forney stage (all error values are 1).
3. Reuse survey before any RTL, per the root conventions: the GF(2^m)
   primitives live in the reed-solomon component (`gf_pkg`, `gf_mul`,
   `gf_inv`), written for exactly this reuse; the BCH-specific blocks are new
   ground.
