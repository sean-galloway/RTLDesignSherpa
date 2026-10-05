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

# Every Stage: Math to Pseudocode

This section walks through each hardware block introduced in chapter 3.2, shows the exact equations it implements, and gives pseudocode whose identifiers match the RTL registers. The goal is to make the gap between the math in sections 7.1–7.3 and the Verilog as small as possible.

## Encoder (bch_encoder_core)

The encoder is systematic: the first $k$ input bits pass through unchanged and the remaining $n - k$ bits are the parity remainder.

**The math.** Shift the message polynomial $d(x)$ by $n - k$ positions and divide by $g(x)$:

$$r(x) = x^{n-k} \cdot d(x) \bmod g(x)$$

$$c(x) = x^{n-k} \cdot d(x) + r(x)$$

The LFSR is polynomial long division in hardware.

**The pseudocode.** `r_lfsr[j]` is lane $j$ of the remainder register; lane 0 is the low-order coefficient and lane `DEG_G-1` is the coefficient that shifts out first during the parity drain. `GEN_BITS[j]` is the binary tap $g_j$.

```text
function lfsr_step(r_lfsr, d):
    fb = d ^ r_lfsr[DEG_G - 1]
    for j = 0 .. DEG_G - 1:
        prev = (j == 0) ? 0 : r_lfsr[j - 1]
        r_lfsr[j] = GEN_BITS[j] ? prev ^ fb : prev
    return r_lfsr

// beat unroll: B bits per cycle
w_chain[0] = r_lfsr
for u = 0 .. B - 1:
    w_chain[u + 1] = lfsr_step(w_chain[u], in_data[u])
w_lfsr_next = w_chain[B]
for u = 1 .. B:
    if w_in_count == u:
        w_lfsr_next = w_chain[u]

r_lfsr <= w_lfsr_next           // on every accepted data beat

// parity drain
w_par_beat_len = min(B, remaining parity bits)
for u = 0 .. w_par_beat_len - 1:
    w_parity_bits[u] = r_lfsr[DEG_G - 1 - u]
r_lfsr <= r_lfsr << w_par_beat_len
```

**In the RTL.** `lfsr_step` is the SystemVerilog function at `rtl/macro/bch_encoder_core.sv:143-160`; the unrolled chain and partial-beat mux are at `:175-186`; the parity drain reads the high-order lanes at `:231-238` and `frame_err` is raised on a bit-count mismatch at `:228`. The hardware is a single GF$(2^m)$ bit-LFSR unrolled `BITS_PER_BEAT` times; each `w_chain[u]` is a combinational copy of one serial LFSR step.

## Syndrome unit (bch_syndrome_unit)

The syndrome unit evaluates the received polynomial $R(x)$ at the $t$ independent odd roots.

**The math.** For each odd root exponent $j$ in the consecutive range:

$$S_j = R(\alpha^j) = \sum_{p=0}^{n-1} R_p \cdot \alpha^{j \cdot p}$$

The even syndromes are not computed here; they are rebuilt later by squaring.

**The pseudocode.** One `gf_syndrome_cell` per odd root. `ROOT` is the fixed field element $\alpha^{\text{root_exp}}$.

```text
for each odd root index j = 0 .. T - 1:
    root_exp = FIRST_ROOT + ((FIRST_ROOT + 1) % 2) + 2*j
    ROOT     = alpha ^ root_exp
    r_s      = 0

    on every input beat:
        w_chain[0] = r_s
        for u = 0 .. B - 1:
            symbol     = in_data[u] embedded as GF element {0..0, bit}
            w_chain[u+1] = w_chain[u] * ROOT ^ symbol
        w_next = w_chain[B]
        for u = 1 .. B:
            if w_in_count == u:
                w_next = w_chain[u]
        r_s <= w_next

    out_syndromes[j] = r_s

out_no_error = (out_syndromes == 0)
```

**In the RTL.** The syndrome fub is `rtl/fub/bch_syndrome_unit.sv:50`; it instantiates `T_BITS` copies of `gf_syndrome_cell` (`:128-144`) and computes `out_no_error` from the packed syndrome vector (`:155`). The shared `gf_syndrome_cell` itself is one `gf_mul_const` and a register (`projects/components/ecc-ip/reed-solomon/rtl/fub/gf/gf_syndrome_cell.sv:24-32`).

## Key-equation solver (bch_key_equation_solver)

The solver turns the syndromes into the error-locator polynomial $\Lambda(x)$. For a binary BCH code only $\Lambda(x)$ is needed; there is no Forney stage because every error magnitude is 1.

**The math.** The key equation is

$$\Lambda(x) \cdot S(x) \equiv \Omega(x) \pmod{x^{2t}}$$

where $S(x) = S_1 + S_2 x + \dots + S_{2t} x^{2t-1}$. The reformulated inversionless Berlekamp-Massey (riBM) algorithm solves it in exactly $2t$ iterations. One iteration uses the discrepancy $\delta = \Delta_0$ and a swap decision:

$$\Delta_i(r+1) = \gamma(r) \cdot \Delta_{i+1}(r) \;\oplus\; \delta(r) \cdot \Theta_i(r)$$

$$\Theta_i(r+1) = \text{swap} \;?\; \Delta_{i+1}(r) \;:\; \Theta_i(r)$$

$$\gamma(r+1) = \text{swap} \;?\; \delta(r) \;:\; \gamma(r)$$

$$k(r+1) = \text{swap} \;?\; -k(r)-1 \;:\; k(r)+1$$

**The pseudocode.** The syndrome expander reconstructs $S_1 \dots S_{2t}$ from the $t$ odd input lanes; note that this expander lives in `bch_key_equation_solver`, not in the syndrome unit.

```text
// syndrome expander (inside bch_key_equation_solver)
for i = 1 .. 2*t:
    if i is odd:
        w_full[i-1] = in_syndromes[(i-1)/2]
    else:
        w_full[i-1] = w_full[i/2 - 1] ^ 2   // S_{2j} = S_j^2

// riBM array (shared from the reed-solomon library)
NPE = 3*t + 1
for i = 0 .. NPE - 1:
    if i < 2*t:      init[i] = w_full[i]
    elif i == 3*t:   init[i] = 1
    else:            init[i] = 0
    Delta[i] = init[i]
    Theta[i] = init[i]

gamma = 1
k     = 0
for iter = 1 .. 2*t:
    delta = Delta[0]
    swap  = (delta != 0) && (k >= 0)
    for i = 0 .. NPE - 1:
        Delta_next[i] = gamma * Delta[i+1] ^ delta * Theta[i]
        Theta_next[i] = swap ? Delta[i+1] : Theta[i]
    Delta = Delta_next
    Theta = Theta_next
    gamma = swap ? delta : gamma
    k     = swap ? -k-1 : k+1

// BCH wrapper readout
for i = 0 .. T:
    out_lambda[i] = Delta[t + i]
out_lambda_degree = degree of Delta[t .. 3*t]
out_more_than_t   = any Delta[t+i] != 0 for i > T
```

**In the RTL.** The BCH wrapper reconstructs the full syndrome sequence at `rtl/fub/bch_key_equation_solver.sv:109-134`, instantiates the imported `key_equation_solver_ribm` at `:150-167`, and trims the locator to `Lambda_0 .. Lambda_t` at `:180-185`. The riBM module itself is in the reed-solomon component tree (`projects/components/ecc-ip/reed-solomon/rtl/fub/key_equation_solver_ribm.sv:95,137-145` for initialization, `:180-188` for the control update, and `:196-213` for output readout). A sister description of the same riBM math lives at `../../../../reed-solomon/docs/reed_solomon_has/ch07_understanding_the_math/05_every_stage_math_to_pseudocode.md`. The per-cell update is in `projects/components/ecc-ip/reed-solomon/rtl/fub/gf/ribm_pe.sv:24-34,62-83`.

## Chien search (bch_chien_search)

The Chien search evaluates $\Lambda(x)$ at every bit position and flags the zeros.

**The math.** Position $p$ (counted from the first transmitted bit) has locator value $X_p = \alpha^{n-1-p}$. The position is in error when

$$\Lambda(X_p^{-1}) = 0, \qquad X_p^{-1} = \alpha^{-(n-1-p)}$$

Within one beat the lane offset $u$ evaluates position $p+u$:

$$\Lambda(X_{p+u}^{-1}) = \sum_{i=0}^{t} \Lambda_i \cdot \alpha^{-i(n-1-p)} \cdot \alpha^{i u}$$

**The pseudocode.** `r_c[i]` holds the coefficient contribution for the first position of the current beat; `LANE_K[u,i]` is the constant $\alpha^{i u}$.

```text
for i = 0 .. T:
    r_c[i] = in_lambda[i] * alpha^{-i*(N-1)}

p = 0
while p < N:
    for u = 0 .. B - 1:
        sum = 0
        for i = 0 .. T:
            sum ^= LANE_K[u,i] * r_c[i]
        w_root[u] = (sum == 0)

    out_flip_en    = w_root & position_valid(p .. p+B-1)
    out_root_count += count(w_root & position_valid)

    p += B
    for i = 0 .. T:
        r_c[i] *= alpha^{i*B}
```

**In the RTL.** The coefficient cells are initialized and stepped at `rtl/fub/bch_chien_search.sv:135-156`; the per-beat lane sum and root detection are at `:174-208`; the running root count is at `:219-231` and `out_flip_en` at `:210-214`. Because the code is binary, a root is a pure bit-flip location and no Forney stage is needed (`rtl/fub/bch_chien_search.sv:9-11`).

## Verdict and correction (bch_decoder_core)

The decoder core collects the Chien results, decides whether the block is correctable, and applies the flips.

**The math.** A block is correctable when

$$\text{degree}(\Lambda) \le t \quad\text{and}\quad \text{root count} = \text{degree}(\Lambda)$$

and, when enabled, the corrected stream re-check syndromes are all zero. For a binary BCH code every error value is 1, so correction is

$$\hat{c}_p = R_p \oplus e_p$$

where $e_p = 1$ for every found root position $p$. An uncorrectable block passes through unchanged.

**The pseudocode.**

```text
// during Chien: capture beat data and flip mask
r_buf[beat]  <= in_data
r_flip[beat] <= w_chien_out_flip_en

// final verdict
w_verdict_correctable = !r_more_than_t
                        && (r_chien_root_count == r_lambda_degree)
                        && (!ENABLE_RECHECK || w_rechk_out_no_error)

// release
r_release_apply = w_verdict_correctable
out_data = r_buf[idx] ^ (r_flip[idx] & {B{r_release_apply}})

// frame-err or uncorrectable: r_release_apply = 0, block emitted unchanged
```

**In the RTL.** The block buffer and flip-mask array are at `rtl/macro/bch_decoder_core.sv:148-150`; the verdict expression is at `:359-365`; the XOR-based flip application is at `:377-380`; the capture of `r_flip` is at `:520-524`; and the uncorrectable/frame-err pass-through paths are at `:535-547,558-569`.

## Trace

The Python script `ch07_math_trace.py` in this directory reproduces the section-7.3 example with the same field, the same codeword, and the same errors. Its output is:

```text
BCH(15,7) t=2 trace (bit 14 first):
  codeword           = 100110111000010
  received           = 100100111001010
  S_1                = alpha^12  (1111)
  S_3                = alpha^7   (1011)
  S_2                = alpha^9   (1010)
  S_4                = alpha^3   (1000)
  raw riBM Lambda    = alpha^1, alpha^13, alpha^14
  monic locator      = alpha^13 + alpha^12*X + X^2
  Chien roots (exp)  = [3, 10]
  RTL positions p    = [4, 11]
  corrected          = 100110111000010
```

| Quantity | Value | Note |
|----------|-------|------|
| $S_1$ | $\alpha^{12}$ | matches Table 7.7 |
| $S_3$ | $\alpha^{7}$ | matches Table 7.7 |
| raw riBM $\Lambda_0,\Lambda_1,\Lambda_2$ | $\alpha^1, \alpha^{13}, \alpha^{14}$ | RTL array output (BCH wrapper keeps first three lanes) |
| monic locator | $X^2 + \alpha^{12} X + \alpha^{13}$ | reciprocal-scaled form used by the section-7.3 Chien table |
| Chien roots (exponents) | $\{3, 10\}$ | the flipped bits from section 7.3 |
| RTL positions $p$ | $\{4, 11\}$ | transmission-order indices; $p = n-1-j$ for exponent $j$ |
| corrected word | `100110111000010` | identical to the section-7.2 codeword |
: Table 7.12: Numeric trace of the section-7.3 example

The raw riBM array output is a scalar multiple of the reciprocal of the textbook monic locator. The hardware's Chien cell wiring evaluates that raw polynomial at $\alpha^{-(n-1-p)}$, so the RTL position counter reports $p = 4$ and $p = 11$ for the same two errors that section 7.3 labels as bit exponents $10$ and $3$.
