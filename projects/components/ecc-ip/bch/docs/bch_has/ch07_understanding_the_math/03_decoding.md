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

# Syndromes, the Key Equation, and Correction

## Received polynomial and syndromes

The channel flips some bits. The decoder receives a polynomial $R(x)$ that is the transmitted codeword $c(x)$ plus an error polynomial $e(x)$:

$$R(x) = c(x) + e(x)$$

The error polynomial has a $1$ at every flipped bit position and $0$ everywhere else. If no errors occurred, $e(x) = 0$ and $R(x) = c(x)$.

The specification writes the syndromes as $S_i = R(\alpha^{b+i})$ for $i = 0 \dots 2t - 1$, where $b$ is the first root. For narrow-sense codes $b = 1$, and it is often cleaner to index by the exponent itself. In the rest of this chapter we use

$$S_i = R(\alpha^i), \quad i = 1 \dots 2t$$

This is the same set of values, just renumbered. Because $c(x)$ is divisible by $g(x)$, every root of $g(x)$ is also a root of $c(x)$, so evaluating $c(x)$ at those roots gives zero. The syndromes therefore depend only on the error polynomial:

$$S_i = R(\alpha^i) = c(\alpha^i) + e(\alpha^i) = e(\alpha^i)$$

All syndromes are zero if and only if $R(x)$ is a valid codeword. That is the first test the decoder performs, and it is the reason the syndrome unit of chapter 3.2 exists.

The unit evaluates $R(x)$ at the $t$ independent roots as the bits stream in. It does not store the whole block and then substitute. Instead it uses Horner's rule:

$$S_i = (\dots((r_{n-1} \alpha^i + r_{n-2}) \alpha^i + r_{n-3}) \dots ) \alpha^i + r_0$$

Bits arrive most-significant first, so $r_{n-1}$ is the first transmitted bit. Each arriving bit $r_j$ triggers one multiply by the constant $\alpha^i$ and one XOR into the accumulator. After the last bit the accumulator holds $S_i$. The multiply-by-constant is a fixed XOR network, so the syndrome cell is small and fast.

## The evenness shortcut

In characteristic $2$, the freshman's dream from section 7.1 gives:

$$(a + b)^2 = a^2 + b^2$$

Apply this to a syndrome. If $e(x)$ has errors at polynomial exponents $j_1, j_2, \dots$, then

$$S_i = \alpha^{i j_1} + \alpha^{i j_2} + \dots$$

Squaring the syndrome doubles every exponent:

$$S_i^2 = \alpha^{2 i j_1} + \alpha^{2 i j_2} + \dots = S_{2i}$$

So the even-indexed syndromes are not independent. For $t = 2$:

$$S_2 = S_1^2, \qquad S_4 = S_2^2 = S_1^4$$

Once $S_1$ and $S_3$ are known, $S_2$ and $S_4$ come for free by squaring. The syndrome unit in chapter 3.2 therefore has only $t$ cells, not $2t$; each cell accumulates one odd-exponent syndrome. That is the evenness shortcut defined in chapter 1.3.

## The key equation

The error-locator polynomial $\Lambda(x)$ is the monic polynomial whose roots are the error locators $\alpha^{j_1}, \alpha^{j_2}, \dots$, where each $j_l$ is a polynomial exponent:

$$\Lambda(x) = (x + \alpha^{j_1})(x + \alpha^{j_2}) \cdots$$

It satisfies the key equation:

$$\Lambda(x) \cdot S(x) \equiv \Omega(x) \pmod{x^{2t}}$$

where $S(x)$ is the syndrome polynomial and $\Omega(x)$ is the error-evaluator polynomial. In words: $\Lambda(x)$ is the smallest polynomial that, when multiplied by the syndrome polynomial, leaves only low-degree terms. Its roots tell us where the errors are.

In a reed-solomon decoder, $\Omega(x)$ is also needed because the error magnitude at each location can be any field element. In a binary BCH decoder the magnitude is always $1$, so once the Chien search finds the positions the corrector simply flips the bits. The solver only has to deliver $\Lambda(x)$.

The key equation can be inverted by several algorithms. Chapter 3.3 compares three candidates for this design:

- **riBM** (reformulated inversionless Berlekamp-Massey) is the default general-purpose choice.
- **Euclidean / ME** (modified Euclidean) is a readable alternative that avoids division.
- **PGZ / step-by-step** is attractive for small $t$ because it solves a small linear system directly.

For the worked example below we use the Peterson-Gorenstein-Zierler direct solve. It is the same algorithm the `SMALL_T` solver candidate would use, and every step is visible in the field arithmetic. Berlekamp-Massey iteratively builds $\Lambda(x)$ by inspecting one syndrome discrepancy at a time; the Euclidean algorithm repeatedly cross-multiplies two polynomials until one of them becomes the locator; PGZ writes the syndrome identities as a small linear system and solves it directly with field operations.

## Chien search and binary correction

After the solver produces $\Lambda(x)$, the Chien search evaluates it at every polynomial exponent:

$$\Lambda(\alpha^0), \Lambda(\alpha^1), \dots, \Lambda(\alpha^{n-1})$$

If $\Lambda(\alpha^j) = 0$, the coefficient of $x^j$—that is, bit $j$ in polynomial-exponent form—is in error. The Chien search walks the $n$ positions in lock-step with the block buffer read-out, one position per cycle in the serial architecture or several positions per cycle if the throughput profile selects a parallel evaluation tree. Because the code is binary, every error value is $1$, so correction is a pure flip: the corrector XORs a $1$ into that bit as it leaves the block buffer. There is no Forney stage and no magnitude computation. That is the main mathematical difference between this binary BCH decoder and the reed-solomon decoder, which must also compute how much each symbol was corrupted.

## Worked example: correcting two errors

**Position convention.** In this example, "bit $j$" means the coefficient of $x^j$ in the codeword polynomial. The RTL counts transmission-order positions $p = 0, 1, \dots$ starting with the first transmitted bit, so coefficient $x^j$ corresponds to position

$$p = n - 1 - j$$

For the two flipped bits, exponents $j = \{10, 3\}$ map to RTL positions $p = \{4, 11\}$.

We start with the 15-bit codeword from section 7.2:

$$c = 1001101\,11000010$$

Flip the bits whose polynomial exponents are $10$ and $3$—that is, add $x^{10} + x^3$ to $c(x)$. The received polynomial is:

$$R(x) = c(x) + x^{10} + x^3$$

In bit order $R_{14} \dots R_0$ the received word is:

$$R = 100100111001010$$

### Computing the odd syndromes

We need $S_1 = R(\alpha)$ and $S_3 = R(\alpha^3)$. Using Table 7.2 from section 7.1 to replace each power of $\alpha$ by its 4-bit vector and XORing the terms that are present in $R(x)$:

| Syndrome | Exponent sum | Vector | Value |
|----------|--------------|--------|-------|
| S_1      | alpha^12     | 1111   | alpha^12 |
| S_3      | alpha^7      | 1011   | alpha^7  |
: Table 7.7: Odd syndromes of the received word

The value $S_1 = 1111$ comes from XORing the vectors for every set bit exponent in $R(x)$: $\alpha^{14} = 1001$, $\alpha^{11} = 1110$, $\alpha^8 = 0101$, $\alpha^7 = 1011$, $\alpha^6 = 1100$, $\alpha^3 = 1000$, and $\alpha^1 = 0010$. Chasing the accumulating XOR gives $1111 = \alpha^{12}$. For $S_3$ we use the same exponents but with tripled values mod $15$, which is what the syndrome cell with root $\alpha^3$ accumulates.

The even syndromes follow from the shortcut:

$$S_2 = S_1^2 = (\alpha^{12})^2 = \alpha^9 = 1010$$
$$S_4 = S_2^2 = (\alpha^9)^2 = \alpha^3 = 1000$$

So the syndrome unit only had to compute two 4-bit values, $S_1$ and $S_3$; the other two syndromes came from two field squarings.

### Solving the t = 2 Peterson system

For two errors the recurrence is:

$$S_{j+2} + \Lambda_1 S_{j+1} + \Lambda_2 S_j = 0, \qquad j = 1, 2$$

which gives the linear system over $\mathrm{GF}(2^4)$:

$$\Lambda_1 S_2 + \Lambda_2 S_1 = S_3$$
$$\Lambda_1 S_3 + \Lambda_2 S_2 = S_4$$

Substitute the syndrome values $S_1 = \alpha^{12}$, $S_2 = \alpha^9$, $S_3 = \alpha^7$, $S_4 = \alpha^3$:

$$\Lambda_1 \alpha^9 + \Lambda_2 \alpha^{12} = \alpha^7$$
$$\Lambda_1 \alpha^7 + \Lambda_2 \alpha^9 = \alpha^3$$

The determinant is:

$$\Delta = S_2^2 + S_1 S_3 = \alpha^3 + \alpha^4 = \alpha^7$$

Using Cramer's rule over the field:

$$\Lambda_1 = \frac{S_2 S_3 + S_1 S_4}{\Delta} = \frac{\alpha^9 \cdot \alpha^7 + \alpha^{12} \cdot \alpha^3}{\alpha^7} = \frac{\alpha + 1}{\alpha^7} = \frac{\alpha^4}{\alpha^7} = \alpha^{12}$$

$$\Lambda_2 = \frac{S_2 S_4 + S_3^2}{\Delta} = \frac{\alpha^9 \cdot \alpha^3 + (\alpha^7)^2}{\alpha^7} = \frac{\alpha^{12} + \alpha^{14}}{\alpha^7} = \frac{\alpha^5}{\alpha^7} = \alpha^{13}$$

So the error-locator polynomial is:

$$\Lambda(x) = x^2 + \alpha^{12} x + \alpha^{13}$$

Any nonzero scalar multiple of $\Lambda(x)$ has the same roots, so the Chien search and the corrector do not care about the exact scale. The riBM hardware in section 7.5 produces a scaled reciprocal of this form; the verdict logic only counts roots and checks degree, both of which are scale-invariant.

### Chien search

Now evaluate $\Lambda(x)$ at $\alpha^j$ for $j = 0 \dots 14$.

| j | alpha^j vector | Lambda(alpha^j) | Note |
|---|----------------|-----------------|------|
| 0  | 0001 | 0011 | |
| 1  | 0010 | 0100 | |
| 2  | 0100 | 0111 | |
| 3  | 1000 | 0000 | ROOT |
| 4  | 0011 | 1010 | |
| 5  | 0110 | 1110 | |
| 6  | 1100 | 1010 | |
| 7  | 1011 | 0111 | |
| 8  | 0101 | 1001 | |
| 9  | 1010 | 1001 | |
| 10 | 0111 | 0000 | ROOT |
| 11 | 1110 | 0011 | |
| 12 | 1111 | 1101 | |
| 13 | 1101 | 0100 | |
| 14 | 1001 | 1110 | |
: Table 7.8: Chien search over the 15 bit positions

The zeros occur at $j = 3$ and $j = 10$, exactly the exponents we flipped (RTL positions $p = 11$ and $p = 4$). No other position yields zero, so the decoder does not invent extra errors. The corrector XORs those two bits, restoring:

$$1001101\,11000010$$

A final syndrome check over the corrected block gives all four syndromes $S_1 = S_2 = S_3 = S_4 = 0$, confirming the result is a valid 15-bit codeword. The corrected bit vector matches the original codeword from section 7.2 exactly.

## When correction fails

Not every received block can be corrected. The decoder declares a block uncorrectable when the math does not line up. Two common cases:

- The locator polynomial $\Lambda(x)$ has degree $v$ but fewer than $v$ distinct roots in the field. Then the error count implied by the degree does not match the actual root count.
- The locator has degree greater than $t$. Even if it has roots, the code was only designed to correct $t$ errors, so those roots are not trustworthy.

Chapter 3.2 describes how the verdict logic flags these cases. Some blocks with more than $t$ errors happen to produce a locator with the right number of roots but the wrong positions; the decoder catches those by running a second syndrome check over the corrected stream. An uncorrectable block leaves the buffer unchanged; the status port reports the failure with the final bit.

## From math to hardware

| Math step | Hardware block | Where it lives |
|-----------|----------------|----------------|
| Syndrome evaluation S_i = R(alpha^i) | syndrome unit | chapter 3.2 |
| Key-equation solve for Lambda(x) | key-equation solver | chapter 3.3 |
| Root search Lambda(alpha^j) = 0 | Chien search + corrector | chapter 3.2 |
| Block storage and playback | block buffer | chapter 3.2 |
| Final verdict and status | status ports | chapter 3.2 |
: Table 7.9: Mapping the decode math to the decoder blocks

The syndrome unit and Chien search are pure field arithmetic pipelines. The solver is the only block whose internal algorithm varies across the candidate profiles; everything downstream sees only the locator polynomial and the syndromes. That separation is what lets the architecture in chapter 3.1 swap riBM, Euclidean, or PGZ without touching the buffer, the corrector, or the interface in chapter 4.1.
