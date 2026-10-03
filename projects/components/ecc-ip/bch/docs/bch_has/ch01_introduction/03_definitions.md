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

# Definitions and Acronyms

| Term | Meaning |
|---|---|
| BCH(n, k) | Binary Bose-Chaudhuri-Hocquenghem code with n coded bits per block, k of them data |
| GF(2^m) | the Galois field with 2^m elements; internal symbols and all codec arithmetic live in it |
| m | field dimension; each internal symbol is m bits |
| t | the number of bit errors the code corrects per block |
| designed distance | 2t + 1, the guaranteed minimum Hamming distance of the code |
| minimal polynomial | the monic irreducible polynomial over GF(2) having alpha^i as a root in GF(2^m); g(x) is the lcm of the minimal polynomials of the consecutive roots alpha^b ... alpha^(b+2t-1) |
| narrow-sense | a BCH code whose first root b = 1; non-narrow-sense has b != 1 (for example CCSDS uses b = 112 in its field representation) |
| primitive BCH | n = 2^m - 1, the full-length cyclic code |
| shortened BCH | n < 2^m - 1, derived from the full-length code by treating the missing leading bits as zero |
| evenness shortcut | in characteristic 2, S_2j = S_j^2, so only the t odd syndromes S_1, S_3, ..., S_2t-1 are independent; the syndrome unit computes t GF values, not 2t |
| systematic | the k data bits pass through unchanged and the n - k parity bits follow them |
| syndrome | S_i = R(alpha^(b+i)), the received polynomial evaluated at a generator root; all zero if and only if the block is a codeword |
| key equation | the relation the solver inverts to find Lambda(x) from the odd syndromes |
| riBM | reformulated inversionless Berlekamp-Massey, the default key-equation solver candidate (Sarwate and Shanbhag 2001) |
| Euclid / ME | the modified Euclidean algorithm in its inversionless systolic form (Shao et al. 1985), the alternative solver candidate |
| step-by-step decoding | Massey's 1965 procedure that corrects syndromes one error position at a time, attractive for small t |
| PGZ | Peterson-Gorenstein-Zierler direct matrix solve over the syndromes, another small-t candidate |
| Chien search | evaluating Lambda at every one of the n bit positions to find the roots, hence the error locations |
| Forney stage | the RS decoder stage that computes error magnitudes; absent in a binary BCH decoder because every error value is 1 |
| bit-level correction | the Chien search walks n bit positions and flips the bit wherever it finds a root; it does not evaluate symbol positions |
| erasure | a bit whose position is known to be unreliable (flagged at the input); not currently enabled (PRD D5 TBD) |
| AXIS | AXI4-Stream |
| PRD | Product Requirements Document (`../../PRD.md`) |
| MAS | Micro-Architecture Specification (companion, not yet written) |
| FUB | functional unit block |

: Table 1.1: Definitions and acronyms
