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

# From Field to Code

## Codewords as polynomials

A binary BCH block of $n$ bits is a polynomial over $\mathrm{GF}(2)$:

$$c(x) = c_0 + c_1 x + c_2 x^2 + \dots + c_{n-1} x^{n-1}, \quad c_i \in \{0,1\}$$

The least significant bit is $c_0$; the most significant bit is $c_{n-1}$, which is also the first transmitted bit. This is not a general-purpose polynomial — it is just a convenient way to talk about a bit vector and its shifts at the same time.

These codes are cyclic. Multiply $c(x)$ by $x$ and reduce modulo $(x^n - 1)$:

$$x \cdot c(x) \bmod (x^n - 1)$$

Because we are in characteristic $2$, $x^n - 1 = x^n + 1$. The reduction wraps the coefficient of $x^n$ around to the constant term, which is exactly a cyclic rotation of the $n$ bits. If $c(x)$ is a codeword, so is every cyclic shift of it.

For a concrete 15-bit example, suppose $c(x)$ has a $1$ at $x^{14}$ and nowhere else. Then $x \cdot c(x) = x^{15}$, and reducing modulo $x^{15} + 1$ gives $1$, which places the $1$ at the constant term. The bit moved from polynomial exponent $14$ to polynomial exponent $0$. That cyclic property is why the encoder is a feedback shift register and why the decoder can treat a block as a single polynomial.

Every valid codeword is a multiple of the generator polynomial $g(x)$. If $u(x)$ is any polynomial of degree less than $k$, then $c(x) = u(x) \cdot g(x)$ is a codeword. There are $2^k$ such polynomials, so there are $2^k$ codewords. The generator polynomial therefore completely defines the code; the data bits only select which multiple of $g(x)$ we transmit. Systematic encoding chooses $u(x)$ so that the high coefficients of the product are exactly the data bits, then adds the remainder $r(x)$ to make the low coefficients the parity.

## Generator polynomial and consecutive roots

A BCH code is defined by its generator polynomial $g(x)$, a polynomial over $\mathrm{GF}(2)$ whose roots are $2t$ consecutive powers of $\alpha$:

$$g(\alpha^b) = g(\alpha^{b+1}) = \dots = g(\alpha^{b+2t-1}) = 0$$

The parameter $b$ is the first root. When $b = 1$ the code is narrow-sense, the default in most textbook treatments and in this chapter's example. Chapter 6.3 notes that CCSDS telecommand uses $b = 112$ in its field representation; the math is the same, only the exponents shift.

The number of consecutive roots determines the guaranteed error-correction capability. A generator with $2t$ consecutive roots produces a code with designed distance $2t + 1$, which means any two valid codewords differ in at least $2t + 1$ bit positions. The proof is the BCH bound; the intuition is that $2t$ roots give the decoder enough independent equations to solve for $t$ error locations. For our example $t = 2$, so the designed distance is $5$: any two valid codewords differ in at least five bit positions. That guarantees correction of up to $2$ errors and detection of up to $4$ errors. We do not prove the bound here, but we use it to choose $t$ for the target bit-error rate.

## Minimal polynomials

Each root $\alpha^i$ has a minimal polynomial $m_i(x)$: the monic irreducible polynomial over $\mathrm{GF}(2)$ that has $\alpha^i$ as a root in $\mathrm{GF}(2^m)$. Because the coefficients must lie in $\mathrm{GF}(2)$, the other roots of $m_i(x)$ are forced to be the conjugates of $\alpha^i$ under squaring. Here is why. If $m_i(x)$ has coefficients in $\mathrm{GF}(2)$ and $m_i(\alpha^i) = 0$, then applying the freshman's dream from section 7.1 gives

$$0 = (m_i(\alpha^i))^2 = m_i((\alpha^i)^2) = m_i(\alpha^{2i})$$

so $\alpha^{2i}$ is also a root. Repeating the argument collects the whole cyclotomic coset.

$$\alpha^i, \alpha^{2i}, \alpha^{4i}, \alpha^{8i}, \dots$$

taken modulo $2^m - 1$ until the sequence repeats. That set is the cyclotomic coset of $i$.

For $i = 1$ in $\mathrm{GF}(2^4)$ the coset is $\{1, 2, 4, 8\}$, so

$$m_1(x) = (x + \alpha)(x + \alpha^2)(x + \alpha^4)(x + \alpha^8)$$

Multiplying this out and reducing every coefficient modulo $2$ gives $x^4 + x + 1$. For $i = 3$ the coset is $\{3, 6, 12, 9\}$, and the same procedure gives $x^4 + x^3 + x^2 + x + 1$.

The generator is the least common multiple of the minimal polynomials of the consecutive roots:

$$g(x) = \mathrm{lcm}\{m_b(x), m_{b+1}(x), \dots, m_{b+2t-1}(x)\}$$

Since distinct minimal polynomials are irreducible, the lcm is just their product. The degree of $g(x)$ is the number of parity bits:

$$\deg(g) = n - k \le m \cdot t$$

For the BCH(15, 7) example in this chapter, $m = 4$ and $t = 2$, so $\deg(g) = 8 = 4 \cdot 2$.

| i | cyclotomic coset | minimal polynomial m_i(x) |
|---|------------------|---------------------------|
| 1 | {1, 2, 4, 8}     | x^4 + x + 1               |
| 2 | {1, 2, 4, 8}     | x^4 + x + 1               |
| 3 | {3, 6, 12, 9}    | x^4 + x^3 + x^2 + x + 1   |
| 4 | {1, 2, 4, 8}     | x^4 + x + 1               |
: Table 7.4: Minimal polynomials and cyclotomic cosets for alpha^1 .. alpha^4 in GF(2^4)

The coset for $i = 1$ has four members, so $m_1(x)$ has degree $4$. The same coset catches $\alpha^2$ and $\alpha^4$, which is why their minimal polynomials are identical. The coset for $i = 3$ is disjoint, giving a second degree-4 minimal polynomial.

## Constructing BCH(15, 7)

We build the narrow-sense code with $n = 15 = 2^4 - 1$, $k = 7$, and $t = 2$. The consecutive roots are $\alpha^1, \alpha^2, \alpha^3, \alpha^4$. From Table 7.4 only two distinct minimal polynomials are needed:

$$g(x) = \mathrm{lcm}(m_1(x), m_3(x)) = m_1(x) \cdot m_3(x)$$

$$g(x) = (x^4 + x + 1)(x^4 + x^3 + x^2 + x + 1)$$

Multiplying the two degree-4 polynomials gives terms from $x^8$ down to $x^0$. In characteristic $2$, any coefficient that appears twice cancels. The $x^5$, $x^3$, $x^2$, and $x^1$ terms each appear an even number of times and disappear; the remaining terms are:

$$g(x) = x^8 + x^7 + x^6 + x^4 + 1$$

The coefficients from $x^8$ down to $x^0$ are:

| Power | x^8 | x^7 | x^6 | x^5 | x^4 | x^3 | x^2 | x^1 | x^0 |
|-------|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| Coeff | 1   | 1   | 1   | 0   | 1   | 0   | 0   | 0   | 1   |
: Table 7.5: Coefficients of g(x) = x^8 + x^7 + x^6 + x^4 + 1

The degree is $8$, exactly $n - k = 15 - 7$, so this code has $8$ parity bits and $7$ data bits.

A full-length primitive code has $n = 2^m - 1$. Most real profiles are shortened: the configured block length is smaller, and the missing leading bits are treated as zero in the syndrome computation and Chien search. Chapter 6.2 covers the parameters and chapter 6.3 lists the candidate profiles. The algebra does not change; only the position offsets and the assumption of leading zeros change.

## Systematic encoding

A systematic codeword keeps the original $k$ data bits unchanged and appends $n - k$ parity bits. Write the data polynomial as $d(x)$ with degree less than $k$. Shift it by $n - k$ positions:

$$x^{n-k} \cdot d(x)$$

Divide by $g(x)$ and keep the remainder $r(x)$, which has degree less than $n - k$:

$$r(x) = x^{n-k} \cdot d(x) \bmod g(x)$$

The codeword is then:

$$c(x) = x^{n-k} \cdot d(x) + r(x)$$

The high part carries the data; the low part carries the parity. Because $c(x)$ differs from $x^{n-k} d(x)$ by a multiple of $g(x)$, it is a multiple of $g(x)$ and therefore a valid codeword. Every root of $g(x)$ is also a root of $c(x)$, which is why the syndrome test in section 7.3 works: evaluating $c(x)$ at any root of $g(x)$ gives zero.

The LFSR is polynomial long division in hardware. Each incoming bit shifts the partial dividend left by one power of $x$. If the bit shifted out of the high position is $1$, the register XORs the generator coefficients into the lower positions — that is the same as subtracting $g(x)$ from the current partial remainder. After the last data bit the register contains exactly the remainder $r(x)$.

The hardware in chapter 3.2 is exactly this division. The encoder core's parity registers form a bit-level LFSR whose feedback taps are the binary coefficients of $g(x)$: each arriving bit shifts the partial remainder up one power of $x$, and when the bit that falls off the end is a $1$, the tap positions XOR $g(x)$ back in. Because the code is binary, that feedback is plain XOR — the binary encoder contains no GF multipliers at all, which is the structural difference from the RS encoder, whose symbol-level LFSR multiplies by the field-element coefficients of its $g(x)$.

## Worked example: encoding one block

Take the 7-bit message

$$d(x) = x^6 + x^3 + x^2 + 1$$

In bit order $d_6 d_5 d_4 d_3 d_2 d_1 d_0$ this is $1001101$. Feed the bits into the encoder LFSR one at a time, most significant bit first—this is the same as transmission order. The generator is $g(x) = x^8 + x^7 + x^6 + x^4 + 1$, so the feedback taps are at positions $7$, $6$, $4$, and $0$. The $x^8$ term is implicit in the shift register: it is the bit that falls off the left end and becomes the feedback decision.

| Step | Input bit | LFSR p7..p0 after update |
|------|-----------|--------------------------|
| 1    | 1         | 11010001                 |
| 2    | 0         | 01110011                 |
| 3    | 0         | 11100110                 |
| 4    | 1         | 11001100                 |
| 5    | 1         | 10011000                 |
| 6    | 0         | 11100001                 |
| 7    | 1         | 11000010                 |
: Table 7.6: LFSR contents while encoding d(x) = x^6 + x^3 + x^2 + 1

The LFSR table and a manual polynomial long division give the same remainder, which is a useful cross-check. The final register contents $11000010$ are the parity polynomial:

$$r(x) = x^7 + x^6 + x$$

Appending the parity to the data gives the systematic 15-bit codeword:

$$c(x) = x^{14} + x^{11} + x^{10} + x^8 + x^7 + x^6 + x$$

In bit order $c_{14} \dots c_0$:

$$c = 1001101\,11000010$$

The first seven bits are the original message and the last eight bits are the parity. We can sanity-check the result by evaluating $c(x)$ at a generator root such as $\alpha$. Every term in $c(x)$ is a power of $\alpha$; using Table 7.2 from section 7.1 to convert those powers to vectors and XORing them gives $0$. That is not an accident — it is the definition of a valid codeword. We use exactly this 15-bit word in section 7.3, where we corrupt two bits and walk through the decode.
