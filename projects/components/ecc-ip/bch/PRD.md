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

# Binary BCH Codec -- Product Requirements (DRAFT)

**Version:** 0.1 (draft, 2026-10-03)
**Status:** decisions pending -- this page records the questions and the
candidates, not answers. It becomes v1.0 when a consumer fixes section 3,
the same posture as the reed-solomon PRD.
v0.1: stand-up mirror of the reed-solomon component. Where Sean's existing
direction (recorded in the RS PRD) binds BCH too, the decision is carried
over by reference; everything else is open with candidates.

## 1. Purpose

A parameterised binary BCH encoder and decoder over GF(2^m) for use by a
Sherpa consumer (flash/memory ECC first in line, telecommand second), verified
against a software golden model, documented with a HAS, and characterised for
FPGA cost the way the rest of the repo is. The reed-solomon PRD section 1
says why both codecs exist: symbol-oriented correction is what burst-error
channels want, and bit-oriented correction -- a binary BCH code needs no
symbol framing, corrects t bit errors anywhere in the block, and its decoder
needs no error-value computation -- is what raw bit-error channels like
flash pages and multi-bit memory failures want. BCH is its own component
rather than a mode of RS (RS PRD D7, 2026-09-29, Sean); the GF(2^m)
primitives are shared, nothing BCH-specific lives in the RS tree.

## 2. Background (from `References/`)

A binary BCH(n, k) code is a cyclic code over GF(2) with codeword length
n <= 2^m - 1 (primitive codes; 2^m + 1 exists but is exotic), designed
minimum distance delta = 2t + 1, and corrects any t bit errors. The
generator g(x) is the lcm of the minimal polynomials of alpha^b through
alpha^(b+2t-1) over GF(2^m). The decoder differs from the RS decoder in
three structural ways:

- **Only t syndromes are independent.** S_2j = S_j^2 in a characteristic-2
  field, so the 2t syndromes collapse to the t odd ones S_1, S_3, ..., S_2t-1
  (the BCH evenness shortcut; Lin & Costello derive it). A syndrome unit
  computes t GF values, not 2t.
- **No Forney stage.** Every error value in a binary code is 1, so Chien
  search positions are simply flipped. The fourth RS decoder stage vanishes.
- **Correction is bit-level.** Chien evaluates the locator at n bit positions
  (n up to 2^m - 1, e.g. 16383 at m = 14), not n/S symbol positions.

The encoder is a GF(2^m) LFSR with the parity bits as feedback -- the same
shape as the RS encoder's, tapped from g(x). The key-equation solvers are the
same algorithms as RS (BM, Euclid) seeded with the odd syndromes only;
step-by-step decoding (Massey 1965) and the Peterson-Gorenstein-Zierler direct
solve are the small-t candidates RS never needed. Everything scales with m
and t; the references span the practical range.

## 3. Decisions that pick the design

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| D1 | Field dimension m | OPEN. Reed-solomon precedent: its own elaboration parameter, NOT derived from the bus width. Values in the wild: m = 6 (CCSDS (63,56)), m = 13/14/15/16 (flash controllers, sized so n >= page-plus-spare bits; see the Nabipour paper) | GF table sizes, syndrome cell width, Chien length |
| D2 | Correctable bits t | OPEN, elaboration-time per the RS D2 precedent (no run-time t). Values in the wild: t = 1 (CCSDS TC), t = 4..8 (NOR), t = 12..72 class (MLC/TLC NAND pages, per the Cai survey) | parity count 2t <= n - k <= m*t, key-equation iterations, Chien width |
| D3 | Shortening | OPEN, elaboration-time per the RS D3 precedent: any n from 2t + 1 up to 2^m - 1, k = n - deg g derived. Flash profiles are shortened by construction (page + spare area is not a primitive length) | zero-fill on encode, position offset on decode |
| D4 | Encoder only, or encoder + decoder | OPEN; RS D4 precedent says ship both shapes and let the integration choose | roughly the area ratio between them |
| D5 | Erasure decoding | OPEN, default out. Binary erasure information (a known-bad page region) is real for flash but no standard profile exercises it the way RAID exercises RS erasures; revisit when a consumer names one | modified syndromes / erasure locator, extra interface |
| D6 | Throughput | OPEN. The syndrome pass is the throughput cost (n bit-positions against t GF accumulators); candidates: bit-serial (1 bit/cycle, t parallel GF MACs), page-parallel unrolled syndrome trees, or symbol-parallel beats with per-beat serial bits. RS D6's lesson: decide from the consumer's clock and rate, and the rate contract must be written down before DV | the whole microarchitecture |
| D7 | GF(2^m) primitive source | **CARRIED 2026-09-29 (Sean, RS PRD D7): share the reed-solomon component's GF layer** -- `gf_pkg` (constant functions over m and the primitive polynomial), `gf_mul`, `gf_mul_const`, `gf_inv` are written for reuse and are imported, not copied. Nothing BCH-specific (binary syndromes, the evenness shortcut, bit-level Chien/flip) lives in the RS tree | one GF layer for both codecs; BCH tree holds only the codec |
| D8 | Generator polynomial / primitive element / first root | OPEN, per profile: CCSDS 231.0-B-4 section 3 fixes the (63,56) modified BCH generator; flash profiles are custom per controller vendor and page geometry; DVB-T2/S2/C2 fix their own | a fixed choice per profile, parameterised in the encoder taps |
| D9 | Interface | OPEN with a recorded direction: mirror RS D9 (2026-09-29, Sean) -- a core with plain valid/ready at both ends, AXIS/AXI4 as optional wrapper adapters, the bare core the primary test target. BCH-specific sub-question with no RS analog: the data interface is a BIT stream with a block-end flag, and bits-per-beat is a new parameter (there is no SYMBOLS_PER_BEAT; a beat carries a slice of one codeword) | the core is what a consumer instantiates; the adapters are for standalone use |
| D10 | First consumer | **DIRECTION 2026-10-02 (Sean, recorded in RS PRD D10 and TASK-003): consumers are expected from a future memory controller project.** No profile is pinned until one lands; BCH tracks the same wake condition as reed-solomon TASK-003. Candidates: a NAND/NOR flash ECC layer in that controller (the Cai and Nabipour papers size it), a TC link | picks D1-D9 |
| D11 | Key-equation solver | OPEN. Candidates: inversionless BM seeded with the odd syndromes (Massey 1969; the RS riBM adapts directly), the modified Euclidean array (Sugiyama 1975; the RS EUCLID branch adapts), and the small-t family -- PGZ direct solve or Massey's step-by-step (Massey 1965) -- which binary BCH makes attractive because t is often <= 8 while m is large. Two solvers agreeing as the cross-check, per the RS D11 philosophy | key-equation cell counts, cycles; DV runs every candidate against one golden model |
| D12 | Scrambler / randomizer | OUT unless a named standard consumer needs one (the DVB-T2/S2/C2 scramblers live outside the BCH block in those standards, as the CCSDS randomizer lives outside RS in the TM Blue Book) | one optional FUB per top if ever |

## 4. Candidate profiles (each fixes D1-D3 and D8)

| Profile | Code | Field | Source in `References/` | Notes |
|---|---|---|---|---|
| CCSDS telecommand | (63,56) modified BCH, t = 1, concatenated with the (7,1/2) convolutional code | GF(2^6) | CCSDS 231.0-B-4 section 3 (stored); the generator is figure 3-2 | the classic command link: small t, but a fully worked generator in a free standard -- the natural first RTL profile even if no consumer adopts it |
| NAND flash ECC | shortened BCH, page-plus-spare geometry, t in the 12-72 class | GF(2^m), m = 13-16 per controller | Cai et al. 2017 (stored) for the error landscape; Nabipour & Javidan 2023 (stored) for (m,t) selection against cell level | the profile the memory-controller consumer is expected to name; n runs to thousands of bits, so D6 and the Chien length dominate |
| DVB-T2 / S2 / C2 | BCH outer of an LDPC concatenation | GF(2^m), m per standard | ETSI EN 302 755 / 302 307 / 302 769 (linked in References) | BCH cleans the LDPC error floor; interesting only if a broadcast consumer ever appears |

## 4a. Where the block sits

Same argument as RS PRD 4a, one level down in the memory hierarchy: a BCH
code protects a block of bits, not a wire -- the encoder needs all k bits
before parity and the decoder needs all n before it can correct one -- so the
code lives at an ENDPOINT where the block boundary already exists. For the
expected consumer that is the flash/memory controller: encode on the write
path as the page+spare image is assembled, decode (and correct, and report)
on the read path before the data leaves. The parity rides the spare area; the
correction belongs right after the channel that corrupts.

## 5. Requirements that hold for every profile

- R1 Encoder is systematic: data bits pass through unchanged, parity follows.
- R2 Decoder reports per block: corrected bit count, uncorrectable flag,
  and (if D5) erasure count used; it never silently passes a failed block.
- R3 Every GF constant (primitive polynomial, generator polynomial, first
  root b) is a parameter or a generated table, never a literal in the
  datapath.
- R4 Verification is against a software golden model on the same block
  (`galois` first candidate; AFF3CT as the cross-check), across random data,
  random error patterns up to t and beyond t (to prove R2), and every profile
  in section 4 that D1-D3 admit.
- R5 FPGA cost is reported the way the repo does it (an out-of-context
  synthesis fixture), per profile, before the HAS claims a number.
- R6 No assertions in RTL (`vault/handbook/design/`); properties go in
  `formal/` blocks. The binary evenness shortcut (S_2j = S_j^2) and the
  no-Forney structural collapse are natural formal targets.

## 6. Out of scope until a decision says otherwise

Soft-decision decoding (the flash read-retry and LLR literature in the
survey papers is a channel technique, not a codec change), list decoding
(the Guruswami-Sudan material in the stored draft is theory), concatenation
with convolutional or LDPC codes (the standards do this outside the BCH
block), and interleaving beyond a bit-address permutation at the boundary.
