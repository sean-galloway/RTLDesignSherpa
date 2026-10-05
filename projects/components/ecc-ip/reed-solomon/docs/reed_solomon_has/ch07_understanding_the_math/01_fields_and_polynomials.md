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

# Fields and Polynomials

## Why error correction needs a finite field

Every arithmetic step inside the Reed-Solomon codec uses a finite field. The reason is not abstract: correction has to divide, and ordinary integer division does not behave well inside a hardware pipeline. A field is a number system where addition, subtraction, multiplication, and division (except by zero) all stay inside the same set and obey the rules we expect. If the set is finite, every operation has a fixed width, every result fits in an m-bit register, and there are no rounding or overflow surprises. That is why the symbols, the coefficients, the syndromes, and the error magnitudes all live in $\mathrm{GF}(2^m)$.

## What a field is

A field has four operations, each closed inside the set, with identities and inverses:

- addition has an identity $0$ and every element has a negative;
- multiplication has an identity $1$ and every nonzero element has a reciprocal;
- multiplication distributes over addition.

The rational numbers are a field, but they are infinite. Integers modulo $n$ are finite, yet they are a field only when $n$ is prime. Take $n = 6$: the element $2$ has no multiplicative inverse because no integer $x$ satisfies $2x \equiv 1 \pmod{6}$. Worse, $2 \cdot 3 = 0$ in this system, so zero can be factored out of nonzero elements. That breaks division. When $n$ is prime, every nonzero residue has an inverse, and the system is the field $\mathrm{GF}(p)$.

For hardware we use characteristic 2: the field has $2^m$ elements, written $\mathrm{GF}(2^m)$. The smallest such field is $\mathrm{GF}(2)$, the two-element field $\{0, 1\}$.

## GF(2): the two-element field

In $\mathrm{GF}(2)$, addition and subtraction are the same operation: exclusive OR.

| a | b | a + b | a * b |
|---|---|---|---|
| 0 | 0 | 0 | 0 |
| 0 | 1 | 1 | 0 |
| 1 | 0 | 1 | 0 |
| 1 | 1 | 0 | 1 |
: Table 7.1: Operations in GF(2)

Multiplication is the same as logical AND. The only nonzero element is $1$, and it is its own inverse. This is the arithmetic that every digital gate already does.

## Polynomials over GF(2) and irreducibility

A polynomial over $\mathrm{GF}(2)$ has coefficients that are only $0$ or $1$, and its arithmetic follows the table above. For example,

$$p(x) = x^4 + x + 1$$

has coefficients $1$, $0$, $0$, $1$, $1$. In binary this is `10011`. We add two such polynomials by XORing their coefficient vectors; there are no carries.

A polynomial is irreducible if it cannot be factored into lower-degree polynomials over the same field. The polynomial $x^4 + x + 1$ is irreducible over $\mathrm{GF}(2)$, while $x^4 + x^2 + 1$ factors as $(x^2 + x + 1)^2$ and is therefore not. Irreducibility is the analogue of primeness for integers: it is what lets us build a field by taking polynomials modulo $p(x)$.

## Building GF(2^m)

To build $\mathrm{GF}(2^4)$, we take all polynomials over $\mathrm{GF}(2)$ of degree less than $4$, modulo an irreducible degree-4 polynomial. There are $2^4 = 16$ such polynomials, one for every 4-bit pattern. Addition is XOR. Multiplication is ordinary polynomial multiplication followed by reduction modulo $p(x)$, which just means replacing every $x^4$ that appears with $x + 1$ (because $x^4 \equiv x + 1 \pmod{x^4 + x + 1}$) until the degree drops below $4$.

The residue of $x$ is called the primitive element $\alpha$. Because $p(x)$ is primitive, the powers of $\alpha$ generate every nonzero field element before they repeat. That gives us a compact multiplicative description of the whole field: every nonzero element is $\alpha^i$ for some $i$, and $\alpha^{15} = 1$.

## The GF(2^4) log/antilog table

The following table is the reference for every worked example in this chapter. It uses $p(x) = x^4 + x + 1$ (`10011`). Each row shows one power of $\alpha$ as both a 4-bit vector and a polynomial in $\alpha$.

| i | alpha^i (binary) | alpha^i (polynomial) |
|---:|---|---|
| 0 | 0001 | 1 |
| 1 | 0010 | alpha |
| 2 | 0100 | alpha^2 |
| 3 | 1000 | alpha^3 |
| 4 | 0011 | alpha + 1 |
| 5 | 0110 | alpha^2 + alpha |
| 6 | 1100 | alpha^3 + alpha^2 |
| 7 | 1011 | alpha^3 + alpha + 1 |
| 8 | 0101 | alpha^2 + 1 |
| 9 | 1010 | alpha^3 + alpha |
| 10 | 0111 | alpha^2 + alpha + 1 |
| 11 | 1110 | alpha^3 + alpha^2 + alpha |
| 12 | 1111 | alpha^3 + alpha^2 + alpha + 1 |
| 13 | 1101 | alpha^3 + alpha^2 + 1 |
| 14 | 1001 | alpha^3 + 1 |
: Table 7.2: Powers of alpha in GF(2^4) with p(x) = x^4 + x + 1

To multiply two nonzero elements, add their exponents modulo $15$. To divide, subtract exponents modulo $15$. The zero element has no log; anything multiplied by $0$ is $0$.

## Worked multiplies in GF(2^4)

We will use the table in two ways: by adding exponents, and by expanding vectors when an intermediate step needs to be visible.

| Product | Exponent form | Vector form | Result |
|---|---|---|---|
| alpha^4 * alpha^8 | alpha^12 | 0011 * 0101 | 1111 = alpha^12 |
| alpha^10 * alpha^7 | alpha^17 = alpha^2 | 0111 * 1011 | 0100 = alpha^2 |
| alpha^5 * alpha^13 | alpha^18 = alpha^3 | 0110 * 1101 | 1000 = alpha^3 |
: Table 7.3: Sample multiplications in GF(2^4)

The second column shows the rule: add exponents and reduce modulo $15$. The third column shows the same operation as vector XOR products, with each partial product shifted and reduced by `10011`. Both views are the same operation; the exponent view is faster by hand, and the vector view is what the gates implement.

## A worked reduction

It is worth seeing once how the vector view produces the same answer as the exponent view. Multiply $\alpha^4$ (`0011`) by $\alpha^8$ (`0101`). As polynomials these are $(\alpha + 1)$ and $(\alpha^2 + 1)$. Their product is

$$(\alpha + 1)(\alpha^2 + 1) = \alpha^3 + \alpha + \alpha^2 + 1.$$

In binary this is `0011 * 0101`. Treat the multiplier `0101` as bits $b_0 = 1$, $b_2 = 1$. The partial products are the multiplicand shifted by those positions: `0011` and `1100`. Adding them with XOR gives `1111`. The degree is already below $4$, so no reduction is needed, and the result is $\alpha^{12}$. That matches $\alpha^4 \cdot \alpha^8 = \alpha^{12}$.

Now try $\alpha^5$ (`0110`) times $\alpha^{13}$ (`1101`). The unreduced product is degree $6$, so a reduction appears:

$$\alpha^5 \cdot \alpha^{13} = \alpha^{18} = \alpha^{18 - 15} = \alpha^3.$$

In vectors: `0110 * 1101`. The multiplier bits are $b_0 = 1$, $b_2 = 1$, $b_3 = 1$, giving partial products `0110`, `110000`, and `1100000`. Reduce each power of $x^4$ or higher using $x^4 = x + 1$. The term $x^5 = x \cdot x^4$ becomes $x^2 + x$, and $x^6 = x^2 \cdot x^4$ becomes $x^3 + x^2$. Collecting all terms and XORing coefficients gives `1000`, which is $\alpha^3$. A hardware multiplier performs exactly this reduction, but in parallel rather than term by term.

## The symbol view

In this codec a symbol is one field element. With $m = 8$ a symbol is a byte; with $m = 4$ it is a nibble; with $m = 10$ it is the 10-bit symbol used by the Ethernet RS-FEC profile from chapter 6.3. The RS block is a sequence of symbols, not bits. When two symbols are multiplied, they are multiplied as field elements using the rules above, not as binary integers. This is the first thing that confuses newcomers: `0x02 * 0x03` in GF(256) is not `0x06`. It is whatever the field polynomial says it is, and there are no carries anywhere in the codec.

The chapter 1.3 definitions call this out explicitly: all arithmetic lives in $\mathrm{GF}(2^m)$. Addition is XOR. Subtraction is also XOR, because in characteristic 2 every element is its own negative. That single fact is why the generator polynomial roots are written $(x - \alpha^j)$ and $(x + \alpha^j)$ interchangeably, and why correction later will add the computed error value to the received symbol instead of subtracting it.

The choice of $m$ is the parameter `SYMBOL_WIDTH` from chapter 6.2. The choice of primitive polynomial is `PRIM_POLY`. Together they fix the exact log/antilog table the hardware uses. Change the polynomial and the binary representation of every nonzero symbol changes, even though the abstract code does not.

## Hardware tie: a register is a field element

An m-bit register holding one symbol is exactly one element of $\mathrm{GF}(2^m)$. Addition is a row of XOR gates. Multiplication by a constant is a fixed XOR network: each output bit is the XOR of some subset of the input bits, chosen once from the vector form of the constant. That is why the encoder taps, syndrome roots, Chien stepping constants, and Forney denominator are all cheap in silicon: they are multiplications by known constants, not general field multipliers.

A general field multiplier (`gf_mul`) is still just ANDs and XORs, with one variable array feeding a network of constant arrays. There is no carry chain, so the delay is logarithmic in the number of terms, not bit-serial. A parallel multiplier is larger than a carry-save integer multiplier of the same width, but it is also faster and deterministic, which is why the decoder can afford one multiplier per syndrome or Chien lane and still meet timing.

The GF layer described in chapter 3.1 and the FUB catalog is where these operations live. Every module that needs field arithmetic instantiates one of a small family of blocks: `gf_mul` (general multiply), `gf_mul_const` (multiply by a fixed constant, which synthesis collapses into pure XOR trees), `gf_inv`, and `gf_syndrome_cell` built on constant multiplies. Addition never needs a module; it is just XOR. When you see `gf_pkg` referenced in the RTL, it is the package of constant functions that implements the field arithmetic — multiply, inverse, powers, logs — from `SYMBOL_WIDTH` and `PRIM_POLY` at elaboration.

| Math object | Hardware representation |
|---|---|
| symbol | m-bit register |
| a + b | m XOR gates |
| a * b (general) | m-by-m AND/XOR array |
| a * constant | fixed XOR network |
| alpha^i | lookup or constant register |
: Table 7.4: Field operations and their hardware forms

With the field in place, section 7.2 turns symbols into a code.
