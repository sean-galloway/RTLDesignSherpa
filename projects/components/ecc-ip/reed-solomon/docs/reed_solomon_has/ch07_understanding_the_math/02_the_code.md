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

## Codewords as polynomials over GF(2^m)

A Reed-Solomon block is a polynomial whose coefficients are field elements. If the block has $n$ symbols, we write

$$c(x) = c_0 + c_1 x + \ldots + c_{n-1} x^{n-1},$$

where each $c_i$ is one element of $\mathrm{GF}(2^m)$. This is different from the bit-polynomial view used in CRCs or binary BCH. There the coefficients are single bits; here the coefficients are whole symbols. A single coefficient can already be any of $2^m$ values, so the polynomial carries much more information per term. A CRC appends the same number of check symbols but only detects: it can flag any burst of up to $2t$ bits, yet it cannot say where the error is. An RS code of the same parity size can correct $t$ symbol errors anywhere in the block, and each symbol is $m$ bits, so a single error locator can cover an entire burst.

Of the $n$ coefficients, $k$ are data symbols and $2t$ are parity symbols, with $n = k + 2t$. The code is called RS($n$, $k$) over $\mathrm{GF}(2^m)$. The parameter `T_SYMBOLS` from chapter 6.2 is this $t$, and `N_SYMBOLS` is $n$. A codeword is valid exactly when it is divisible by $g(x)$, which is the same as saying it vanishes at every root of $g(x)$.

## The generator polynomial

Reed-Solomon is the $q$-ary cousin of BCH. Its generator polynomial has $2t$ consecutive powers of $\alpha$ as roots:

$$g(x) = \prod_{i=0}^{2t-1} (x - \alpha^{b+i}).$$

In characteristic 2, subtraction is the same as addition, so $(x - \alpha^j)$ and $(x + \alpha^j)$ are identical. The value $b = 1$ is called narrow-sense; chapter 6.2 exposes $b$ as the `FIRST_ROOT` parameter, and profiles move it (DVB uses $b = 0$, CCSDS $b = 112$).

Unlike binary BCH, RS does not need minimal polynomials. In binary BCH the coefficients must be bits, so each root $\alpha^j$ has to be grouped with its conjugates under squaring to force binary coefficients. RS already allows coefficients to be any field element, so the simple product above has coefficients in $\mathrm{GF}(2^m)$ directly. The degree of $g(x)$ is exactly $2t$, which equals $n - k$. Each root contributes one degree to $g(x)$, and therefore one parity symbol to the block. That direct count is why RS($n$, $k$) always has exactly $n - k = 2t$ parity symbols.

## Why RS is maximum-distance-separable

A code's minimum distance $d_{\min}$ is the smallest number of symbol positions in which any two distinct codewords differ. The Singleton bound says $d_{\min} \leq n - k + 1$. Reed-Solomon meets this bound exactly:

$$d_{\min} = n - k + 1 = 2t + 1.$$

That is why RS can correct any $t$ symbol errors: $2t + 1$ guarantees that any two codewords are far enough apart that a sphere of radius $t$ around each one does not overlap any other. Decoding is unambiguous: the decoder always finds the single closest codeword, or declares failure if too many symbols are wrong.

It also explains why RS is the default choice for burst channels such as flash pages and optical links, which are exactly the use cases in chapter 2.1. A burst that corrupts several consecutive bits usually lands inside one or two symbols; RS counts symbol errors, not bit errors, so a 10-bit burst inside one symbol costs the same as a single flipped bit inside another symbol. The MDS property tells us the code is using its parity as efficiently as any linear code possibly can.

## Shortened codes

A full-length RS code has $n = 2^m - 1$. Practical standards often use a shorter block by treating the leading $2^m - 1 - n$ symbols as zero and not transmitting them. The DVB RS(204,188) profile in chapter 6.3 is built this way from RS(255,239) over $\mathrm{GF}(2^8)$: 51 leading zero symbols are dropped, leaving a 204-symbol block that is mathematically the tail of the full codeword.

Shortening does not change the generator polynomial, the field, or the number of correctable errors. The only hardware changes are in bookkeeping. The syndrome cells treat the missing leading positions as zero, so their accumulators start at zero and remain zero for those positions. The Chien search offsets its position counter so that it still walks the 204 transmitted positions rather than all 255. The decoder output drops the implicit zeros, so the consumer sees exactly the shortened packet.

## Worked construction of RS(15,11)

We now build a concrete code: RS(15,11) with $t = 2$ over $\mathrm{GF}(2^4)$, using the field from section 7.1. The generator has roots $\alpha$, $\alpha^2$, $\alpha^3$, $\alpha^4$:

$$g(x) = (x + \alpha)(x + \alpha^2)(x + \alpha^3)(x + \alpha^4).$$

We multiply the factors pairwise. First pair $(x + \alpha)(x + \alpha^2)$:

$$(x + \alpha)(x + \alpha^2) = x^2 + (\alpha + \alpha^2)x + \alpha^3 = x^2 + \alpha^5 x + \alpha^3.$$

Second pair $(x + \alpha^3)(x + \alpha^4)$:

$$(x + \alpha^3)(x + \alpha^4) = x^2 + (\alpha^3 + \alpha^4)x + \alpha^7 = x^2 + \alpha^7 x + \alpha^7.$$

Now multiply the two quadratics:

$$g(x) = (x^2 + \alpha^5 x + \alpha^3)(x^2 + \alpha^7 x + \alpha^7).$$

Collecting terms gives

$$g(x) = x^4 + (\alpha^5 + \alpha^7) x^3 + (\alpha^3 + \alpha^{12} + \alpha^7) x^2 + (\alpha^{12} + \alpha^{10}) x + \alpha^{10}.$$

Using Table 7.2 to add the vector forms, the coefficients simplify to:

| Coefficient | Value | Vector |
|---|---|---|
| g_0 | alpha^10 | 0111 |
| g_1 | alpha^3 | 1000 |
| g_2 | alpha^6 | 1100 |
| g_3 | alpha^13 | 1101 |
| g_4 | 1 | 0001 |
: Table 7.5: Generator polynomial g(x) for RS(15,11)

So

$$g(x) = x^4 + \alpha^{13} x^3 + \alpha^6 x^2 + \alpha^3 x + \alpha^{10}.$$

Every codeword polynomial is a multiple of this $g(x)$. That is the entire definition of the code. The four roots guarantee that any valid codeword $c(x)$ satisfies $c(\alpha) = c(\alpha^2) = c(\alpha^3) = c(\alpha^4) = 0$. Those four evaluations are exactly what the syndrome cells in chapter 3.2 compute later, only on the received word instead of a known codeword.

## Systematic encoding

The encoder in chapter 3.2 produces codewords in systematic form: the $k$ data symbols pass through unchanged, followed by the $2t$ parity symbols. Mathematically,

$$c(x) = x^{2t} d(x) + r(x),$$

where $d(x)$ is the data polynomial and

$$r(x) = x^{2t} d(x) \bmod g(x).$$

The parity $r(x)$ is the remainder after polynomial long division of $x^{2t} d(x)$ by $g(x)$. The hardware LFSR is that long division running in real time: the $2t$ registers hold the current remainder, and each incoming data symbol updates them by one degree.

Here is how one LFSR step works. Let the current remainder be $r(x) = r_0 + r_1 x + r_2 x^2 + r_3 x^3$. When the next data symbol $s$ arrives, we conceptually append it to the high-degree end, forming $x \cdot r(x) + s \, x^4$. Since $g(x)$ is monic, $x^4 \equiv g_3 x^3 + g_2 x^2 + g_1 x + g_0 \pmod{g(x)}$. So the new remainder is

$$x \cdot r(x) + s \cdot (g_3 x^3 + g_2 x^2 + g_1 x + g_0),$$

with all arithmetic in $\mathrm{GF}(2^m)$. The hardware implements this with XOR gates and constant multipliers tied to the generator coefficients. After the last data symbol the registers contain the parity; the mux then switches from data to parity and drains the registers out.

## Worked systematic encode

Take the following 11 data symbols as $d_0, d_1, \ldots, d_{10}$:

| Index | d_i |
|---:|---|
| 0 | 0 |
| 1 | 1 |
| 2 | alpha |
| 3 | alpha^4 |
| 4 | alpha^2 |
| 5 | alpha^8 |
| 6 | alpha^5 |
| 7 | alpha^10 |
| 8 | alpha^3 |
| 9 | alpha^14 |
| 10 | alpha^9 |
: Table 7.6: Data symbols for the RS(15,11) worked example

The encoder streams these in reverse polynomial order: $d_{10}, d_9, \ldots, d_0$. After each symbol the LFSR state is the current remainder. The table below shows the high-to-low remainder registers $r_3, r_2, r_1, r_0$ after each input. All operations are in $\mathrm{GF}(2^4)$.

| Step | Input | r3 | r2 | r1 | r0 |
|---:|---|---|---|---|---|
| 0 | alpha^9 | alpha^7 | alpha^0 | alpha^12 | alpha^4 |
| 1 | alpha^14 | alpha^3 | alpha^2 | 0 | alpha^11 |
| 2 | alpha^3 | alpha^2 | 0 | alpha^11 | 0 |
| 3 | alpha^10 | alpha^2 | alpha^14 | alpha^7 | alpha^14 |
| 4 | alpha^5 | 0 | 0 | alpha^9 | alpha^11 |
| 5 | alpha^8 | alpha^6 | alpha^4 | 0 | alpha^3 |
| 6 | alpha^2 | alpha^0 | alpha^9 | alpha^2 | alpha^13 |
| 7 | alpha^4 | alpha^4 | alpha^12 | alpha^11 | alpha^11 |
| 8 | alpha^1 | alpha^1 | alpha^1 | alpha^5 | alpha^10 |
| 9 | alpha^0 | alpha^5 | alpha^0 | alpha^6 | alpha^14 |
| 10 | 0 | alpha^14 | alpha^1 | alpha^6 | alpha^0 |
: Table 7.7: LFSR remainder evolution during encoding

The final remainder is the parity, from low degree to high:

$$r_0 = \alpha^0, \quad r_1 = \alpha^6, \quad r_2 = \alpha^1, \quad r_3 = \alpha^{14}.$$

In stream order the encoder sends data first, then parity, because chapter 3.2 describes a systematic encoder that passes the data beats through and appends the parity at the end. The polynomial coefficient order $c_0, c_1, \ldots, c_{14}$ is the opposite: the parity coefficients sit at the low-degree end and the data coefficients at the high-degree end. The table below lists the codeword in polynomial order so that $c(x) = c_0 + c_1 x + \ldots + c_{14} x^{14}$ is easy to read. Position $j$ is the coefficient index, so position 0 is the $x^0$ coefficient and the encoder sends position 14 first.

| Position | c_i |
|---:|---|
| 0 | alpha^0 |
| 1 | alpha^6 |
| 2 | alpha^1 |
| 3 | alpha^14 |
| 4 | 0 |
| 5 | 1 |
| 6 | alpha |
| 7 | alpha^4 |
| 8 | alpha^2 |
| 9 | alpha^8 |
| 10 | alpha^5 |
| 11 | alpha^10 |
| 12 | alpha^3 |
| 13 | alpha^14 |
| 14 | alpha^9 |
: Table 7.8: Final RS(15,11) codeword

This exact codeword is used again in section 7.3, where we inject errors and correct them. As a sanity check, dividing the full codeword polynomial by $g(x)$ leaves remainder zero, which is the defining property of any RS codeword. If the remainder were nonzero, either the generator or the encoding table would contain an arithmetic error, and section 7.3 could not possibly decode correctly.
