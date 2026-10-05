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

Every BCH decoder does arithmetic on error patterns. Before we write any hardware, we need a number system where those patterns behave predictably: a field.

A field is a set with two operations (call them addition and multiplication) that satisfy the usual rules — closure, associativity, commutativity, distributivity — plus two extra properties that make algebra work:

- Every element has an additive inverse, so subtraction is always possible.
- Every nonzero element has a multiplicative inverse, so division is always possible.

The integers modulo a prime form a field. The integers modulo a composite do not. Take $\bmod\ 6$: the element $2$ has no multiplicative inverse because $\gcd(2,6)=2$, and worse, $2 \cdot 3 \equiv 0 \pmod 6$ even though neither factor is zero. Those zero divisors break long division, and long division is exactly what polynomial encoding relies on. In a field, dividing one polynomial by another always produces a unique quotient and remainder; that remainder is what the encoder computes as parity. Without a field, the same division could have multiple remainders, and the decoder would not know which error pattern to blame. Error correction needs a finite field because the block length, the syndrome values, and the hardware datapath all have fixed widths.

## GF(2): the two-element field

Binary BCH codes live in extension fields of $\mathrm{GF}(2)$, the field with two elements, $0$ and $1$. Addition is XOR; multiplication is AND. Both are already hardware primitives.

| + | 0 | 1 | * | 0 | 1 |
|---|---|---|---|---|---|
| 0 | 0 | 1 | 0 | 0 | 0 |
| 1 | 1 | 0 | 1 | 0 | 1 |
: Table 7.1: GF(2) addition and multiplication

Because $1 + 1 = 0$, subtraction is the same as addition. This single fact drives almost every simplification in a binary BCH decoder: there are no sign changes, no borrows, and no two's-complement corner cases.

## Polynomials over GF(2)

A polynomial over $\mathrm{GF}(2)$ looks like any ordinary polynomial, except its coefficients are only $0$ or $1$ and all arithmetic on the coefficients is mod $2$.

$$f(x) = f_0 + f_1 x + f_2 x^2 + \dots + f_d x^d, \quad f_i \in \{0,1\}$$

The degree is the highest power with a nonzero coefficient. A polynomial is irreducible over $\mathrm{GF}(2)$ if it cannot be factored into lower-degree polynomials with coefficients in $\mathrm{GF}(2)$. Irreducible polynomials play the same role for polynomials that primes play for integers: they are the atoms from which larger structures are built.

For example, $x^2 + x + 1$ is irreducible over $\mathrm{GF}(2)$. There is no pair of degree-1 polynomials over $\mathrm{GF}(2)$ whose product gives it, because the only degree-1 polynomials are $x$, $x+1$, and their products are $x^2$ and $x^2+x$ and $x^2+1$, none of which equal $x^2+x+1$.

Watch out for polynomials that look irreducible but are not. Over $\mathrm{GF}(2)$,

$$(x + 1)^2 = x^2 + 2x + 1 = x^2 + 1$$

so $x^2 + 1$ is reducible even though it has no linear factor in the ordinary integer sense. The freshman's dream from section 7.1 makes perfect squares easy to spot: any polynomial whose exponents are all even is the square of another polynomial.

## Building GF(2^m)

We construct $\mathrm{GF}(2^m)$ by taking all polynomials of degree less than $m$ over $\mathrm{GF}(2)$ and doing arithmetic modulo an irreducible polynomial $p(x)$ of degree $m$. That makes $\mathrm{GF}(2^m)$ a finite field with $2^m$ elements.

Pick a primitive polynomial $p(x)$ of degree $m$. The residue of $x$ modulo $p(x)$ is called $\alpha$:

$$\alpha = x \bmod p(x)$$

Then every nonzero element of $\mathrm{GF}(2^m)$ can be written as a power of $\alpha$, and those powers cycle with period $2^m - 1$:

$$\mathrm{GF}(2^m)^* = \{1, \alpha, \alpha^2, \dots, \alpha^{2^m-2}\}$$

The element $0$ is the extra element that makes the count $2^m$. Multiplication is easy in the power representation: $\alpha^i \cdot \alpha^j = \alpha^{i+j \bmod (2^m-1)}$. Addition is easy in the vector representation: XOR the corresponding bit vectors.

A practical implementation keeps both a log table and an antilog table so it can switch between the two in a cycle or two. To see why both forms matter, multiply $(1 + \alpha)$ by $(\alpha + \alpha^2)$. In vector form these are $0011$ and $0110$.

$$(1 + \alpha)(\alpha + \alpha^2) = \alpha + \alpha^2 + \alpha^2 + \alpha^3 = \alpha + \alpha^3$$

The two $\alpha^2$ terms cancel because $1 + 1 = 0$. The result is vector $1010$, which Table 7.2 identifies as $\alpha^9$. In the power form the same product is $\alpha^4 \cdot \alpha^5 = \alpha^9$. Both give the same answer; the vector form is how the hardware is wired, and the power form is how the human keeps track.

## Inverses and the log table

Every nonzero element has a multiplicative inverse. In power form this is immediate:

$$(\alpha^i)^{-1} = \alpha^{-i \bmod (2^m - 1)} = \alpha^{2^m - 1 - i}$$

So the inverse of $\alpha^5$ is $\alpha^{10}$, and a quick check in Table 7.2 confirms $\alpha^5 \cdot \alpha^{10} = \alpha^{15} = 1$.

Division is therefore multiplication by the inverse. Solving $\alpha^7 \cdot z = \alpha^3$ for $z$ gives $z = \alpha^3 / \alpha^7 = \alpha^{3 - 7 \bmod 15} = \alpha^{11}$. The decoder uses this constantly: the Peterson solve in section 7.3 divides by a determinant, and every such division is one inverse lookup followed by one multiplication.

If you prefer not to store a log table, the inverse can also be computed with the extended Euclidean algorithm on polynomials over $\mathrm{GF}(2)$. For a small fixed field the table is smaller and faster, so that is what the RTL does.

## The freshman's dream in characteristic 2

In a field of characteristic $2$, the binomial theorem collapses because all intermediate binomial coefficients are even:

$$(a + b)^2 = a^2 + 2ab + b^2 = a^2 + b^2$$

More generally, for any non-negative integer $j$:

$$(a + b)^{2^j} = a^{2^j} + b^{2^j}$$

This identity is not a trick; it is the reason binary BCH decoders only need to compute half the syndromes. If $S_j$ is one syndrome, then $S_{2j} = S_j^2$ is free. The decoder hardware computes the odd-indexed syndromes and derives the even ones by squaring. We revisit that shortcut in section 7.3.

## A concrete field: GF(2^4)

For the worked examples in this chapter we use $m = 4$ and the primitive polynomial

$$p(x) = x^4 + x + 1$$

which is $10011$ in binary. The element $\alpha = x \bmod p(x)$ is represented by the 4-bit vector $0010$. Repeated multiplication by $\alpha$ generates all $15$ nonzero elements.

| i | alpha^i as polynomial | 4-bit vector |
|---|-----------------------|--------------|
| 0 | 1                     | 0001         |
| 1 | alpha                 | 0010         |
| 2 | alpha^2               | 0100         |
| 3 | alpha^3               | 1000         |
| 4 | 1 + alpha             | 0011         |
| 5 | alpha + alpha^2       | 0110         |
| 6 | alpha^2 + alpha^3     | 1100         |
| 7 | 1 + alpha + alpha^3   | 1011         |
| 8 | 1 + alpha^2           | 0101         |
| 9 | alpha + alpha^3       | 1010         |
| 10 | 1 + alpha + alpha^2  | 0111         |
| 11 | alpha + alpha^2 + alpha^3 | 1110   |
| 12 | 1 + alpha + alpha^2 + alpha^3 | 1111 |
| 13 | 1 + alpha^2 + alpha^3 | 1101       |
| 14 | 1 + alpha^3           | 1001         |
: Table 7.2: Log/antilog table for GF(2^4) with p(x) = x^4 + x + 1

Two checks against the table. First, $\alpha^4$ must satisfy $p(\alpha) = 0$, so $\alpha^4 = \alpha + 1$, which is vector $0011$ — exactly the row for $i = 4$. Second, addition is XOR: $\alpha^3$ is $1000$ and $\alpha^5$ is $0110$, so their sum is $1110$, which the table identifies as $\alpha^{11}$.

| a          | b           | a + b (XOR) | result |
|------------|-------------|-------------|--------|
| alpha^3    | alpha^5     | 1000 xor 0110 = 1110 | alpha^11 |
| alpha^7    | alpha^13    | 1011 xor 1101 = 0110 | alpha^5  |
| alpha^4    | alpha^8     | 0011 xor 0101 = 0110 | alpha^5  |
: Table 7.3: Addition examples in GF(2^4)

Multiplication is equally mechanical. To multiply $\alpha^7$ by $\alpha^{13}$ we add exponents mod $15$: $7 + 13 = 20 \equiv 5 \pmod{15}$, so the product is $\alpha^5$. To multiply two vector forms without the table, multiply the polynomials and reduce modulo $p(x)$. Hardware rarely does it that way; it uses the log/antilog ROM or a fixed XOR network.

## Why this is hardware-shaped

This chapter is the only place the decoder leaves the binary world and operates on $m$-bit field elements, but the hardware mapping is direct:

- An $m$-bit register holds one field element.
- Addition is $m$ XOR gates. There are no carries anywhere in the codec; this is field addition, not binary arithmetic.
- Multiplication by a constant is a fixed XOR network. The constant is hard-wired from the profile parameters.
- General multiplication uses an AND array followed by a reduction tree.
- Inversion is usually a table lookup.

The absence of carries is worth emphasizing. A binary adder chains carries from bit $0$ to bit $m - 1$; a field adder XORs every bit independently. That makes the GF datapath fast and easy to pipeline, which is why the encoder and decoder can afford one symbol operation per cycle even for large $m$.

Multiplication by the constant $\alpha$ — the operation the LFSR does on every clock edge — is a good illustration. In $\mathrm{GF}(2^4)$ with $p(x) = x^4 + x + 1$, multiplying a vector $(b_3, b_2, b_1, b_0)$ by $\alpha$ shifts it left and, if the bit shifted out is $1$, XORs $0011$ into the low bits. The whole thing is four 2-input XOR gates and a few muxes. A full variable multiply needs more logic, but it is still pure combinatorial gates; no iteration, no microcode.

The `gf_*` primitives that implement these operations live in the reed-solomon component tree and are imported into the BCH core, as described in chapter 3.1's GF layer subsection. Every arithmetic block in the encoder and decoder is built from three of them: `gf_mul_const` for multiplication by a known constant, `gf_mul` for general multiplication, and `gf_inv` for inversion. The `gf_pkg` package holds the constant functions that evaluate this arithmetic — and the generator polynomial coefficients derived from t, b, and p(x) — from the profile parameters discussed in chapter 6.2.
