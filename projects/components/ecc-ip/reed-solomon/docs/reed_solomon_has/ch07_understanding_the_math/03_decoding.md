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

## The received polynomial

The channel adds an error polynomial to the codeword:

$$R(x) = c(x) + e(x).$$

Each coefficient of $e(x)$ is a field element. A nonzero coefficient $e_j$ means the polynomial coefficient $c_j$ — and therefore the symbol the RTL transmits at position $n-1-j$ — is wrong, and the value can be any nonzero field element. This is the fundamental difference from binary BCH, where every error value is implicitly $1$. Reed-Solomon correction must find both the positions and the values.

Because an error value can be any of $2^m - 1$ nonzero symbols, an RS decoder does more work than a binary decoder. Binary BCH only needs to know where the errors are; RS also needs to know by how much. That is why the decoder has both a locator polynomial and an evaluator polynomial, and why the final stage is a Forney computation rather than a simple bit flip.

## Syndromes

A received word is a valid codeword if and only if it has every root of $g(x)$ as a root. We define the syndromes as the received polynomial evaluated at those roots. For narrow-sense $b = 1$:

$$S_i = R(\alpha^i), \quad i = 1, 2, \ldots, 2t.$$

Equivalently, $S_i = R(\alpha^{b+i-1})$ for $i = 1 \ldots 2t$, matching the definition in chapter 1.3. All $2t$ syndromes are used: the evenness shortcut of binary BCH does not apply, because for symbol errors the error values are arbitrary field elements and $e^2 \neq e$ in general, so $S_{2j} \neq S_j^2$. If every syndrome is zero, the block is a codeword and the decoder passes it through unchanged. If any syndrome is nonzero, correction begins.

The syndrome cells in chapter 3.2 compute each $S_i$ by Horner evaluation as the block streams in:

$$S_i \leftarrow \alpha^i \cdot S_i + R_j.$$

Here $R_j$ is the symbol that just arrived, where arrival 0 is the first-transmitted (highest-degree) coefficient. One multiply-accumulate per syndrome, per symbol. The constant $\alpha^i$ is a known field element, so the multiplier is a fixed XOR network rather than a general field multiplier. With $S$ symbols per beat, the syndrome cell performs $S$ such updates in parallel, each at a different power of $\alpha$ corresponding to the symbol's position within the beat.

## The key equation

Let the syndrome polynomial be

$$S(x) = S_1 + S_2 x + S_3 x^2 + \ldots + S_{2t} x^{2t-1}.$$

The error locator polynomial is

$$\Lambda(x) = \prod_{k=1}^{\nu} (1 - X_k x),$$

where $X_k = \alpha^{j_k}$ is the locator for an error at position $j_k$, and $\nu$ is the number of errors. The error evaluator polynomial is $\Omega(x)$. They satisfy the key equation:

$$\Lambda(x) S(x) \equiv \Omega(x) \pmod{x^{2t}}.$$

The solver inverts this equation: given the syndromes, it finds $\Lambda(x)$ and $\Omega(x)$. The default implementation in this codec is riBM, described in chapter 3.3; the alternative is the inversionless Euclidean algorithm. The math here is the same for both. We only need to know that the solver outputs $\Lambda(x)$ and $\Omega(x)$.

The locator polynomial carries the positions: its roots are the reciprocals of the error locators. The evaluator polynomial carries the magnitudes: combined with the derivative of $\Lambda$, it yields each error value. The key equation ties them together through the syndromes, which are the only thing the decoder can measure directly.

## Chien search

Once $\Lambda(x)$ is known, the decoder finds its roots. A root at $x = \alpha^{-j}$ means an error at position $j$:

$$\Lambda(\alpha^{-j}) = 0 \quad \Longleftrightarrow \quad \text{position } j \text{ is in error.}$$

The Chien search evaluates $\Lambda(x)$ at $\alpha^0, \alpha^{-1}, \ldots, \alpha^{-(n-1)}$, one position per cycle, while the block buffer reads out the same positions. This is the root-finding step described in chapter 3.2.

The evaluation is done incrementally. If the current value is $\Lambda(\alpha^{-j})$, then the next value is $\Lambda(\alpha^{-(j+1)}) = \Lambda(\alpha^{-j} \cdot \alpha^{-1})$, which is obtained by multiplying each register by the appropriate constant. That constant multiply is again a fixed XOR network. A root is detected when the evaluated value is exactly zero, which is just an $m$-bit zero test.

## The Forney formula

For each located root $X_k^{-1} = \alpha^{-j_k}$, the error value is

$$e_{j_k} = -\frac{\Omega(X_k^{-1})}{\Lambda'(X_k^{-1})}.$$

The formal derivative $\Lambda'(x)$ drops the even-powered terms and halves the exponent of each odd-powered term. In characteristic 2, halving an odd exponent is just reduction modulo 2, so

$$\frac{d}{dx} x^{2i+1} = x^{2i}, \qquad \frac{d}{dx} x^{2i} = 0.$$

For our $t = 2$ example, $\Lambda(x) = 1 + \Lambda_1 x + \Lambda_2 x^2$, so $\Lambda'(x) = \Lambda_1$ is a single constant. The minus sign also vanishes in characteristic 2 because $-1 = 1$, so the formula becomes

$$e_{j_k} = \frac{\Omega(\alpha^{-j_k})}{\Lambda'(\alpha^{-j_k})}.$$

The evaluator $\Omega(x)$ encodes the error magnitudes because it absorbs the syndrome information that depends on how wrong each symbol is; the derivative $\Lambda'(x)$ removes the weight of the located root, leaving the bare error value. If $\Lambda'(X_k^{-1}) = 0$ while $\Omega(X_k^{-1}) \neq 0$, the Forney formula divides by zero and the decoder cannot resolve the magnitude. That is the "derivative was zero at a root" verdict in chapter 3.2.

## Erasure math

When `ENABLE_ERASURES` is set, the decoder accepts symbols flagged as known bad. Each erasure costs one parity symbol instead of two. If $\nu$ erasures and $\mu$ errors are present, the code corrects them when

$$2\mu + \nu \leq 2t.$$

The erasure port is described in chapter 4.1. As of chapter 6.2 the default parameter value is `ENABLE_ERASURES = 0`, so the port is absent and the erasure-locator logic is not generated unless a consumer enables it. The math is worth knowing anyway: erasures turn known-bad positions into extra correctable errors. A RAID controller that knows which drive failed, or a link layer that marks a dropped packet, can recover twice as many known failures as unknown ones with the same parity budget.

## Worked decode of RS(15,11)

We take the codeword from section 7.2 and inject exactly two symbol errors:

- position $j = 3$: add $\alpha^5$;
- position $j = 11$: add $\alpha^9$.

In this example, $j$ is the polynomial coefficient index: the table lists $c_0, c_1, \ldots, c_{14}$ from low degree to high degree. The RTL transmits the high-degree end first, so the syndrome cell sees $c_{14}$ as arrival 0, $c_{13}$ as arrival 1, and so on down to $c_0$. The syndrome values below are computed from the polynomial coefficient order shown; if you stream the symbols through the hardware, reverse the table order.

The received word in polynomial coefficient order is:

| Position | Received |
|---:|---|
| 0 | alpha^0 |
| 1 | alpha^6 |
| 2 | alpha^1 |
| 3 | alpha^12 |
| 4 | 0 |
| 5 | 1 |
| 6 | alpha |
| 7 | alpha^4 |
| 8 | alpha^2 |
| 9 | alpha^8 |
| 10 | alpha^5 |
| 11 | alpha^13 |
| 12 | alpha^3 |
| 13 | alpha^14 |
| 14 | alpha^9 |
: Table 7.9: Received word with two injected errors

### Computing the syndromes

Evaluating $R(x)$ at $\alpha, \alpha^2, \alpha^3, \alpha^4$ gives:

| Syndrome | Value | Vector |
|---|---|---|
| S_1 | alpha^4 | 0011 |
| S_2 | alpha^6 | 1100 |
| S_3 | alpha^5 | 0110 |
| S_4 | alpha^0 | 0001 |
: Table 7.10: Syndromes of the received word

All four are nonzero, so the block is not a codeword. Notice that each syndrome is a field element, not a single bit, because the error values are field elements. The syndrome pattern encodes both where the errors are and how large they are.

### Peterson solve for t = 2

For two errors we can solve directly. Let $\Lambda(x) = 1 + \Lambda_1 x + \Lambda_2 x^2$. The Newton identities are

$$\Lambda_1 S_2 + \Lambda_2 S_1 = S_3,$$
$$\Lambda_1 S_3 + \Lambda_2 S_2 = S_4.$$

In matrix form,

$$\begin{pmatrix} S_2 & S_1 \\ S_3 & S_2 \end{pmatrix} \begin{pmatrix} \Lambda_1 \\ \Lambda_2 \end{pmatrix} = \begin{pmatrix} S_3 \\ S_4 \end{pmatrix}.$$

The determinant is $S_2^2 + S_1 S_3 = \alpha^8$, whose inverse is $\alpha^7$. Solving gives

| Coefficient | Value | Vector |
|---|---|---|
| Lambda_1 | alpha^5 | 0110 |
| Lambda_2 | alpha^14 | 1001 |
: Table 7.11: Error locator polynomial coefficients

So

$$\Lambda(x) = 1 + \alpha^5 x + \alpha^{14} x^2.$$

Any nonzero scalar multiple of this locator has the same roots, so the riBM solver in section 7.5 may output a scaled version. The Forney stage there carries the same scale, and its `off = 2t` factor absorbs it, so the recovered error values stay identical.

### Chien search in the example

We evaluate $\Lambda(\alpha^{-j})$ for $j = 0, 1, \ldots, 14$, still using the polynomial coefficient index from the table above. The RTL labels the transmitted position of $c_j$ as $n-1-j$, but the set of roots is the same.

| j | alpha^{-j} | Lambda(alpha^{-j}) |
|---:|---|---|
| 0 | alpha^0 | alpha^11 |
| 1 | alpha^14 | alpha^13 |
| 2 | alpha^13 | alpha^11 |
| 3 | alpha^12 | 0 |
| 4 | alpha^11 | alpha^12 |
| 5 | alpha^10 | alpha^4 |
| 6 | alpha^9 | alpha^6 |
| 7 | alpha^8 | alpha^13 |
| 8 | alpha^7 | alpha^4 |
| 9 | alpha^6 | alpha^0 |
| 10 | alpha^5 | alpha^6 |
| 11 | alpha^4 | 0 |
| 12 | alpha^3 | alpha^1 |
| 13 | alpha^2 | alpha^1 |
| 14 | alpha^1 | alpha^12 |
: Table 7.12: Chien search over the 15 positions

The zeros occur at $j = 3$ and $j = 11$, exactly the injected error positions. The degree of $\Lambda(x)$ is $2$, matching the root count. If the search had found fewer roots than the degree — one root for a degree-2 locator, say — the error locators would not be distinct, and the block would be uncorrectable because the math does not describe a consistent error pattern.

### Error evaluator and Forney

The syndrome polynomial is

$$S(x) = \alpha^4 + \alpha^6 x + \alpha^5 x^2 + x^3.$$

Multiplying by $\Lambda(x)$ and reducing modulo $x^4$ gives

$$\Omega(x) = \alpha^4 + \alpha^5 x.$$

The formal derivative is $\Lambda'(x) = \alpha^5$. Applying the Forney formula at each root:

| Position j | Omega(alpha^{-j}) | Lambda'(alpha^{-j}) | e_j |
|---:|---|---|---|
| 3 | alpha^10 | alpha^5 | alpha^5 |
| 11 | alpha^14 | alpha^5 | alpha^9 |
: Table 7.13: Forney error magnitudes

The computed magnitudes match the injected errors. At $j = 3$ the received symbol is $\alpha^{12}$ and the computed error is $\alpha^5$; adding them gives $\alpha^{12} + \alpha^5 = \alpha^{14}$, which is the original $c_3$. At $j = 11$ the received symbol is $\alpha^{13}$ and the computed error is $\alpha^9$; adding them gives $\alpha^{13} + \alpha^9 = \alpha^{10}$, which is the original $c_{11}$. Adding them back (which is XOR in characteristic 2) restores the original codeword.

### Verification

After correction, the four syndromes are all zero:

| Syndrome | Corrected value |
|---|---|
| S_1 | 0 |
| S_2 | 0 |
| S_3 | 0 |
| S_4 | 0 |
: Table 7.14: Post-correction syndromes

The corrected word matches the codeword from section 7.2 exactly.

## The decoder's final verdict

The second syndrome pass in chapter 3.2 is the mathematical check that the corrected word has zero syndromes. It is the last line of defense. Some patterns with more than $t$ errors still produce a locator of the right degree with the right number of roots; the degree and root checks pass, but the corrected word is not a codeword. The recomputed syndromes catch those miscorrections.

A block is uncorrectable when any of the following holds:

- $\deg(\Lambda) > t$ or $\deg(\Lambda) = 0$ after the solver. A locator of degree zero means no errors were found despite nonzero syndromes, which is impossible. A locator of degree greater than $t$ means the error pattern needs more parity than the code has.
- the number of roots found by Chien search differs from $\deg(\Lambda)$. The fundamental theorem of algebra for this finite field says a degree-$\nu$ polynomial has exactly $\nu$ roots counting multiplicity; if fewer distinct roots are found, the error locators are not distinct, which is not a correctable error pattern.
- $\Lambda'(X^{-1}) = 0$ at a located root while $\Omega(X^{-1}) \neq 0$. The Forney formula divides by the derivative, so a zero derivative with nonzero evaluator is a structural failure.
- the corrected word's syndromes are not all zero. This catches the otherwise-undetectable miscorrections where the locator happens to have the right degree and root count but describes the wrong error pattern.

## From math to hardware

| Math step | Hardware block | Cross-reference |
|---|---|---|
| syndrome evaluation | syndrome unit | chapter 3.2 |
| key-equation solver | riBM (default) or Euclid/ME | chapter 3.3 |
| root finding | Chien search | chapter 3.2 |
| error magnitude | Forney stage | chapter 3.2 |
| correction + replay | block buffer / corrector | chapter 3.2 |
| final zero-syndrome check | second syndrome unit + status | chapter 3.2 |
: Table 7.15: Mathematical operations mapped to decoder blocks

This is the loop that chapter 3.2 describes as data flow: syndromes in, locator out, Chien and Forney walk the block, the corrector replays it, and the second syndrome unit signs the verdict.
