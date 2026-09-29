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

# Reed-Solomon Codec -- Product Requirements (DRAFT)

**Version:** 0.1 (draft, 2026-09-29)
**Status:** decisions pending -- this page records the questions and the
candidates, not answers. It becomes v1.0 when a consumer fixes section 3.

## 1. Purpose

A parameterised Reed-Solomon encoder and decoder over GF(2^m) for use by a
Sherpa consumer (storage, link, or memory ECC), verified against a software
golden model, documented with a MAS, and characterised for FPGA cost the way
the rest of the repo is. RS is chosen over the binary BCH special case
because symbol-oriented correction is what burst-error channels and
multi-bit memory failures want; whether BCH is also delivered from the same
GF machinery is decision D7.

## 2. Background (from `References/`)

An RS(n, k) code over GF(2^m) has n <= 2^m - 1 symbols of m bits, k data
symbols, 2t = n - k parity symbols, and corrects any t symbol errors, or
e errors plus f erasures with 2e + f <= 2t. The decoder is four stages:
syndromes (2t of them, one GF multiply-accumulate each per symbol), the key
equation (Berlekamp-Massey or Euclidean, 2t iterations), Chien search
(evaluate the locator at every position) and Forney evaluation (the error
values). The encoder is an LFSR over GF(2^m) with 2t taps. Everything scales
with t and m; the standards below span the practical range.

## 3. Decisions that pick the design

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| D1 | Symbol width m | 8 (CCSDS, DVB, storage) or 10 (802.3 RS-FEC) | GF table sizes, symbol datapath width |
| D2 | Correctable symbols t | 8 (DVB), 15 or 16 (CCSDS), 16 (KP4 RS(544,514)) | parity count, BM iterations, Chien width |
| D3 | Shortening | full n = 2^m - 1, or shortened (DVB 204 of 255, 802.3 544 of 1023) | zero-fill on encode, position offset on decode |
| D4 | Encoder only, or encoder + decoder | a transmit-only or RAID-write consumer needs only the LFSR | roughly 10x the area between them |
| D5 | Erasure decoding | with (RAID, known-bad columns) or without (link codes) | modified syndromes / erasure locator, extra interface |
| D6 | Throughput | 1 symbol/cycle (serial) up to n symbols/block in a few cycles (parallel Chien, unrolled BM) | the whole microarchitecture; decide from the consumer's clock and rate |
| D7 | BCH | out (RS only), or in as the m-bit-symbol-with-binary-field special case sharing the GF layer | scope of the GF layer and the DV matrix |
| D8 | Generator polynomial / primitive element / first root | per standard: CCSDS uses a dual basis and `b = 112`, DVB uses `b = 0`, 802.3 its own | a fixed choice per profile, parameterised in the encoder taps and Forney |
| D9 | Interface | AXI4-Stream in the house style (TDATA = one or more symbols, TLAST on block end, TUSER for erasure flags / status) | how consumers attach; monitor-able with the existing axis observers |
| D10 | First consumer | none named yet. Candidates in-repo: none today. External: a NAND/DDR ECC layer, a serial link | picks D1-D9 |
| D11 | Key-equation solver | **DECIDED 2026-09-29 (Sean): riBM** -- the reformulated inversionless Berlekamp-Massey of Sarwate and Shanbhag (References, classic paper 7). Euclidean (Sugiyama) rejected: it needs a GF inverse in the loop or a longer systolic array. | 3t + 1 GF multipliers, 2t iterations, no inverse until Forney |

## 4. Candidate profiles (each fixes D1-D3 and D8)

| Profile | Code | Field | Source in `References/` | Notes |
|---|---|---|---|---|
| CCSDS telemetry | RS(255,223), t = 16; also RS(255,239), t = 8 | GF(2^8), dual (Berlekamp) basis, interleave depth 1-8 | CCSDS 131.0-B-5 section 4; 130.1-G-3 for rationale | the classic deep-space code; the dual-basis symbol representation is a conversion at the boundary |
| DVB cable / terrestrial | RS(204,188), t = 8, shortened from RS(255,239) | GF(2^8), primitive poly x^8+x^4+x^3+x^2+1, b = 0 | ETSI EN 300 429 / EN 300 744 (links in References) | the MPEG-2 transport packet code; the most-implemented RS in open-source RTL |
| Ethernet RS-FEC | RS(528,514) "KR4" and RS(544,514) "KP4", t = 7 / 15 | GF(2^10) | IEEE 802.3 Clause 91 / 108 (cited, not stored) | high-rate; drives the parallel-decoder branch of D6 |
| RAID erasure | RS over GF(2^8) or GF(2^16), erasures only (D5), any n <= 2^m - 1 | Vandermonde or Cauchy generator | Plank 1997 + 2003 correction | encoder plus erasure-only decoder; no Chien search |

## 5. Requirements that hold for every profile

- R1 Encoder is systematic: data symbols pass through unchanged, parity follows.
- R2 Decoder reports per block: corrected symbol count, uncorrectable flag,
  and (if D5) erasure count used; it never silently passes a failed block.
- R3 Every GF constant (primitive polynomial, generator roots, first root b,
  dual-basis matrices) is a parameter or a generated table, never a literal
  in the datapath.
- R4 Verification is against a software golden model on the same block
  (`reedsolo` or `galois`), across random data, random error patterns up to t
  and beyond t (to prove R2), and every profile in section 4 that D1-D3 admit.
- R5 FPGA cost is reported the way the repo does it (an out-of-context
  synthesis fixture like `projects/components/bridge/fpga/` or the
  timing_characterization sweeps), per profile, before the MAS claims a number.
- R6 No assertions in RTL (`vault/handbook/design/`); properties go in
  `formal/` blocks. The key-equation solver's invariants are a natural formal
  target.

## 6. Out of scope until a decision says otherwise

Soft-decision or list decoding (the arXiv literature in References is theory,
not hardware), concatenation with convolutional codes (CCSDS does this outside
the RS block), and interleaving beyond a symbol-address permutation at the
boundary.
