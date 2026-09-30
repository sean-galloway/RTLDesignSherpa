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
| RS(n, k) | Reed-Solomon code with n coded symbols per block, k of them data |
| GF(2^m) | the Galois field with 2^m elements; symbols and all codec arithmetic live in it |
| t | the number of symbol errors the code corrects per block; 2t = n - k |
| erasure | a symbol whose position is known to be unreliable (flagged at the input); costs one parity symbol to fix instead of two |
| shortened code | RS(n', k') with n' < 2^m - 1, derived from the full-length code by treating the missing leading symbols as zero (DVB's RS(204,188) from RS(255,239)) |
| systematic | the k data symbols pass through unchanged and the 2t parity symbols follow them |
| syndrome | S_i = R(alpha^(b+i)), the received polynomial evaluated at a generator root; all zero if and only if the block is a codeword |
| key equation | the relation the solver inverts to find Lambda(x) and Omega(x) from the syndromes |
| riBM | reformulated inversionless Berlekamp-Massey, the default key-equation solver (Sarwate and Shanbhag 2001) |
| Euclid / ME | the modified Euclidean algorithm in its inversionless systolic form (Shao et al. 1985), the alternative solver |
| Chien search | evaluating Lambda at every position to find the roots, hence the error locations |
| Forney | computing each error's magnitude from Omega and Lambda' at the located root |
| dual basis | the alternative field representation CCSDS uses for its symbols; a fixed linear map at the boundary |
| scrambler / PRBS | the binary LFSR sequence a standard XORs onto the data for energy dispersal or sync; not part of the RS code |
| AXIS | AXI4-Stream |
| PRD | Product Requirements Document (`../../PRD.md`) |
| MAS | Micro-Architecture Specification (companion, not yet written) |
| FUB | functional unit block |

: Table 1.1: Definitions and acronyms
