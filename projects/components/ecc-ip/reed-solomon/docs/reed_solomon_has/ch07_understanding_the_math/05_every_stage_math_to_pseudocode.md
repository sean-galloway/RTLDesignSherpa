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

Section 7.1 built the field, section 7.2 built the code, and section 7.3 walked a decode by hand. This page gives each stage the shape it has in the RTL: the equations first, then the register names and pseudocode, then the exact module and line numbers. The riBM key-equation solver is shared with the BCH decoder; the corresponding BCH page is at `../../../../bch/docs/bch_has/ch07_understanding_the_math/05_every_stage_math_to_pseudocode.md`.

| Math step | Hardware block | Cross-reference |
|---|---|---|
| parity generation | `gf_lfsr_encoder` / `rs_encoder_core` | section 7.5 below |
| syndrome evaluation | `syndrome_unit` | section 7.5 below |
| key-equation solve | `key_equation_solver_ribm` or `key_equation_solver_euclid` | section 7.3, section 7.5 below |
| root finding | `chien_search` | section 7.3, section 7.5 below |
| error magnitude | `forney_evaluator` | section 7.5 below |
| erasure combine | `rs_erasure_unit` | section 7.5 below |
| correction + recheck | `rs_decoder_core` | section 7.5 below |
: Table 7.19: From mathematics to hardware blocks

## Encoder (`gf_lfsr_encoder`, wrapped by `rs_encoder_core`)

The encoder divides the data polynomial by the generator polynomial $g(x) = \prod_{i=0}^{2t-1}(x - \alpha^{b+i})$ and appends the remainder as parity. The division is a $2t$-stage linear feedback shift register over $\mathrm{GF}(2^m)$.

**The math.**
For one input symbol $d$:

$$\begin{aligned}
\mathit{fb} &= d \oplus r[2t-1], \\
n[0] &= \mathit{fb} \cdot g_0, \\
n[j] &= r[j-1] \oplus \mathit{fb} \cdot g_j \quad (j = 1 \ldots 2t-1).
\end{aligned}$$

The output codeword is the $k$ data symbols followed by the $2t$ remainder symbols.

**The pseudocode.**
```text
g[0..2t-1] = generator coefficients, leading 1 implicit
r_reg[0..2t-1] = 0

function step_one(r, d):
    fb = d ^ r[2t-1]
    n[0] = fb * g[0]
    for j = 1 .. 2t-1:
        n[j] = r[j-1] ^ (fb * g[j])
    return n

# data phase: low lanes are the earlier symbols
for each input beat with i_count valid lanes:
    w_chain[0] = r_reg
    for u = 0 .. S-1:
        w_chain[u+1] = step_one(w_chain[u], lane[u])
    r_reg = w_chain[i_count]

# parity drain phase
for each drain beat:
    for u = 0 .. S-1:
        out_lane[u] = (u < 2t) ? r_reg[2t-1-u] : 0
    for j = 0 .. 2t-1:
        r_reg[j] = (j >= S) ? r_reg[j-S] : 0
```

**In the RTL.** `gf_lfsr_encoder.sv:142-156` implements `step_one`, `:158-169` unrolls $S$ steps and selects the partial-beat result, and `:171-175` drains the parity in transmission order. `rs_encoder_core.sv:147-187` sequences the data and drain phases around the skid buffer.

## Syndrome unit (`syndrome_unit`, `gf_syndrome_cell`)

The syndrome unit evaluates the received word at each generator root. There are $2t$ roots and therefore $2t$ independent syndrome cells.

**The math.**
For root $\alpha^{b+i}$:

$$S_i = R(\alpha^{b+i}) = \sum_j r_j \alpha^{(b+i)(n-1-j)}.$$

Each cell updates by Horner's rule as the symbols arrive:

$$s \leftarrow s \cdot \alpha^{b+i} \oplus r_j.$$

**The pseudocode.**
```text
for i = 0 .. 2t-1:
    root_i = alpha^(b+i)
    r_s[i] = 0

for each received beat (first beat resets the accumulators):
    for i = 0 .. 2t-1:
        w_chain[i][0] = first_beat ? 0 : r_s[i]
        for u = 0 .. S-1:
            w_chain[i][u+1] = w_chain[i][u] * root_i ^ lane[u]
        r_s[i] = w_chain[i][i_count]

ow_synd[i]    = r_s[i]
ow_all_zero   = (all r_s == 0)
```

**In the RTL.** `syndrome_unit.sv:73-89` instantiates $2t$ `gf_syndrome_cell` instances, one per root. `gf_syndrome_cell.sv:76-88` is the $S$-step Horner chain, and `syndrome_unit.sv:91-92` forms the all-zero flag.

## Key-equation solver riBM (`key_equation_solver_ribm`, `ribm_pe`)

The riBM solver inverts the key equation $\Lambda(x) S(x) \equiv \Omega(x) \pmod{x^{2t}}$ in exactly $2t$ cycles. It is the default solver selected by `KES_ALGO = "RIBM"` (`rtl/macro/rs_decoder_core.sv:123,335-357`). The same `key_equation_solver_ribm` module is instantiated by the BCH decoder.

**The math.**
The algorithm keeps $3t+1$ processing elements. Each element holds a pair $(\Delta_i, \Theta_i)$. One iteration uses the discrepancy $\delta = \Delta_0$ and a swap flag:

$$\begin{aligned}
\Delta_i^{\text{new}} &= \gamma \cdot \Delta_{i+1} \oplus \delta \cdot \Theta_i, \\
\Theta_i^{\text{new}} &= \text{swap} \;?\; \Delta_{i+1} \;:\; \Theta_i.
\end{aligned}$$

The control updates are:

$$\begin{aligned}
\gamma &\leftarrow \text{swap} \;?\; \delta \;:\; \gamma, \\
k &\leftarrow \text{swap} \;?\; -k-1 \;:\; k+1.
\end{aligned}$$

**The pseudocode.**
```text
NPE = 3*t + 1
for i = 0 .. 2t-1:
    Delta[i] = Theta[i] = S[i]
for i = 2t .. 3t-1:
    Delta[i] = Theta[i] = 0
Delta[3t] = Theta[3t] = 1
gamma = 1
k = 0

repeat 2t times:
    delta = Delta[0]
    swap  = (delta != 0) && (k >= 0)
    for i = 0 .. NPE-1:
        Delta_next[i] = gamma*Delta[i+1] ^ delta*Theta[i]
        Theta_next[i] = swap ? Delta[i+1] : Theta[i]
    Delta = Delta_next
    Theta = Theta_next
    if swap:
        gamma = delta
        k = -k - 1
    else:
        k = k + 1

o_lambda = Delta[t .. 3t]      # Lambda_0 .. Lambda_2t
o_omega  = Delta[0 .. t-1]     # high-half evaluator, Omega_0 .. Omega_{t-1}
o_deg    = degree of Lambda among the 2t+1 coefficients
o_deg_err = any Lambda_{t+1..2t} is nonzero
```

**In the RTL.** `key_equation_solver_ribm.sv:95` sets `NPE = 3t+1`. The array is loaded at `:137-145`, the processing elements are at `:147-164`, the swap logic is at `:132-134`, the control update is at `:180-188`, and the outputs are selected at `:194-213`. Each `ribm_pe` (`rtl/fub/gf/ribm_pe.sv:43`) performs the two multiplies and two register updates (`ribm_pe.sv:24-32,79-82`).

## Key-equation solver Euclid (`key_equation_solver_euclid`)

The alternative solver is an inversionless extended Euclidean algorithm selected by `KES_ALGO = "EUCLID"`. It divides $x^{2t}$ by the syndrome polynomial until the remainder degree drops below $t$.

**The math.**
Registers $R$ and $Q$ hold the two remainders top-aligned (leading coefficient at index $2t$). Registers $\tilde\lambda$ and $\tilde\mu$ hold the corresponding multipliers, also kept top-aligned. One cycle does one of:

- normalize $R$: if $R[2t] = 0$, shift $R$ and $\tilde\lambda$ up by $x$, `degR--`;
- normalize $Q$: if $Q[2t] = 0$, shift $Q$ and $\tilde\mu$ up by $x$, `degQ--`;
- cross: $R_{\text{new}} = (Q[2t] \cdot R \oplus R[2t] \cdot Q) \cdot x$, $\tilde\lambda_{\text{new}} = (Q[2t] \cdot \tilde\lambda \oplus R[2t] \cdot \tilde\mu) \cdot x$, then swap roles if `degR < degQ`.

The loop stops when $\deg R < t$.

**The pseudocode.**
```text
R[0..2t] = 0; R[2t] = 1                # x^2t
Q[0..2t] = 0; for i=0..2t-1: Q[i+1] = S[i]   # S(x) top-aligned
lam_tilde[0..LW-1] = 0
mu_tilde[0..LW-1] = 0; mu_tilde[1] = 1
degR = 2t; degQ = 2t-1

while degR >= t:
    if R[2t] == 0:
        R       = shift_up(R)       # index i <- old i-1
        lam_tilde = shift_up(lam_tilde)
        degR -= 1
    elif Q[2t] == 0:
        Q       = shift_up(Q)
        mu_tilde = shift_up(mu_tilde)
        degQ -= 1
    else:
        a = R[2t]; b = Q[2t]
        Rn = (b*R) ^ (a*Q)
        Ln = (b*lam_tilde) ^ (a*mu_tilde)
        if degR < degQ:
            Q, mu_tilde, degQ = R, lam_tilde, degR
            degR = old_degQ - 1
        else:
            degR -= 1
        R       = shift_up(Rn)
        lam_tilde = shift_up(Ln)

sh = 2t - degR
o_lambda = lam_tilde[sh .. sh+2t]      # Lambda_0 .. Lambda_2t
o_omega  = R[sh .. sh+t-1]             # textbook evaluator
o_deg    = degree of Lambda
o_deg_err = degR out of range or high coefficients nonzero
```

**In the RTL.** `key_equation_solver_euclid.sv:118-126` declares the four register arrays and the two signed degrees. The initial values are loaded at `:212-225`, the normalize/cross/swap step is at `:150-199`, and the output un-shift is at `:270-299`.

## Chien search (`chien_search`)

The Chien search evaluates the locator polynomial at every symbol position to find its roots. A root at position $j$ means that symbol is in error.

**The math.**
Symbol $j$ (the $j$-th symbol transmitted) has location

$$X_j = \alpha^{n-1-j}.$$

It is in error when

$$\Lambda(X_j^{-1}) = 0.$$

The search keeps one cell per locator coefficient. Cell $i$ holds $\Lambda_i \cdot X_j^{-i}$ for the current beat's first position. It is initialized at position 0 with $X_0^{-i} = \alpha^{-i(n-1)}$ and stepped by $\alpha^{iS}$ per beat. The odd-index lane sum is

$$\text{odd\_sum}[u] = \sum_{i \text{ odd}} \Lambda_i \cdot (X_{j+u})^{-i} = X_{j+u}^{-1} \cdot \Lambda'(X_{j+u}^{-1}),$$

which is the formal derivative handed to the Forney stage.

**The pseudocode.**
```text
for i = 0 .. t:
    r_c[i] = Lambda_i * alpha^(-i*(n-1))

for base = 0, S, 2S, ... while base < n:
    for u = 0 .. S-1:
        sum = 0; odd = 0
        for i = 0 .. t:
            term = r_c[i] * alpha^(i*u)
            sum ^= term
            if i is odd: odd ^= term
        o_root[u]    = (sum == 0)
        o_odd_sum[u] = odd
    for i = 0 .. t:
        r_c[i] = r_c[i] * alpha^(i*S)
```

**In the RTL.** `chien_search.sv:87-109` initializes and steps the cells, and `:129-147` forms the per-lane sum and odd-sum outputs. The decoder core tracks the beat base position with `r_c_pos` (`rtl/macro/rs_decoder_core.sv:589-590,705-724`).

## Forney evaluator (`forney_evaluator`)

The Forney stage turns each Chien root into the actual error magnitude.

**The math.**
With the Chien search supplying $\text{odd\_sum} = X^{-1} \Lambda'(X^{-1})$, the error value is

$$e_j = \frac{X_j^{-(b+\mathit{off})} \cdot \Omega(X_j^{-1})}{\text{odd\_sum}}.$$

The offset is $\mathit{off} = 2t$ for the riBM solver and $\mathit{off} = 0$ for the Euclid solver and for erasure mode. The reason is that riBM's `o_omega` is the *high half* of $S(x)\Lambda(x)$, coefficients $2t \ldots 3t-1$, not the textbook $\Omega = S\Lambda \bmod x^{2t}$. The extra $X^{-2t}$ factor in the numerator converts the high-half evaluator into the same ratio as the textbook form (`rtl/fub/forney_evaluator.sv:8-11,24-33`). The RTL does not use a $\Lambda_0$-normalization trick; it performs a real `gf_inv` per lane.

**The pseudocode.**
```text
OFF = b + off        # off = 2t for riBM, 0 for Euclid / erasures
for i = 0 .. t-1:
    r_w[i] = Omega_i * alpha^(-(i+OFF)*(n-1))

for base = 0, S, 2S, ... while base < n:
    for u = 0 .. S-1:
        w_num[u] = 0
        for i = 0 .. t-1:
            w_num[u] ^= r_w[i] * alpha^((i+OFF)*u)
        w_den_inv[u] = inv(odd_sum[u])
        o_err_val[u] = w_num[u] * w_den_inv[u]
        o_den_zero[u] = (odd_sum[u] == 0)
    for i = 0 .. t-1:
        r_w[i] = r_w[i] * alpha^((i+OFF)*S)
```

**In the RTL.** `forney_evaluator.sv:84` computes `OFF = FIRST_ROOT + (OMEGA_HIGH_HALF ? 2t : 0)`, `:86-109` holds and steps the Omega cells, and `:130-152` evaluates each lane with one `gf_inv` and one `gf_mul`. `rs_decoder_core.sv:679-686` selects `OMEGA_HIGH_HALF` from the solver choice and erasure-support flag.

## Erasure path (`rs_erasure_unit`)

When `ERASURE_SUPPORT = 1`, the decoder accepts symbols flagged as known bad. An erasure costs one parity symbol instead of two, so the correction bound is

$$2\mu + f \leq 2t,$$

where $\mu$ is the number of unknown errors and $f$ is the number of erasures. The RTL enforces the equivalent budget $w\_budget = (2t - f)/2$ (`rtl/macro/rs_decoder_core.sv:497-504`).

**The math.**
The erasure locator is

$$\Gamma(x) = \prod_{p=1}^{f} (1 + X_p x),$$

where $X_p = \alpha^{n-1-p}$ is the location of the flagged symbol. The Forney syndromes are

$$GS = \Gamma \cdot S \bmod x^{2t}.$$

The solver window is stripped differently for the two algorithms: riBM receives $GS \gg f$ (the low $f$ coefficients dropped), while Euclid receives $x^f \cdot T$ (the same values shifted up). After solving, the combined polynomials are

$$\Lambda_c = \Gamma \cdot \Lambda_e, \qquad \Omega_c = \Lambda_e \cdot GS \bmod x^{2t}.$$

If $GS$'s high cells are all zero, the erasures alone explain every syndrome and the solver is bypassed with $\Lambda_e = 1$, so $\Lambda_c = \Gamma$ and $\Omega_c = GS$.

**The pseudocode.**
```text
# Stage A: record flagged locations
r_xpow = alpha^(n-1)
r_xfile[0..2t] = 0
f = 0
for each received beat:
    for u = 0 .. S-1:
        if erasure[u] and u < count:
            r_xfile[f] = r_xpow * alpha^(-u)
            f += 1
    r_xpow = r_xpow * alpha^(-count)

# Stage B: TRANS
r_gam[0] = 1; r_gam[1..2t] = 0
r_gs[0..2t-1] = S[0..2t-1]
for cycle = 0 .. f-1:
    x = r_xfile[cycle]
    for i = 2t .. 1:
        r_gam[i] ^= x * r_gam[i-1]
    for j = 2t-1 .. 1:
        r_gs[j] ^= x * r_gs[j-1]
o_t_zero = (r_gs[f..2t-1] are all zero)

# solver input window
if KES_ALGO == "RIBM":
    kes_synd[i] = (i+f < 2t) ? r_gs[i+f] : 0
else:
    kes_synd[i] = (i >= f) ? r_gs[i] : 0

# Stage B: COMB (after solver returns Lambda_e of degree deg_e)
acc_lam[0..2t] = 0
acc_om[0..2t-1] = 0
for ci = deg_e .. 0:
    lc = Lambda_e[ci]
    for i = 2t .. 0:
        acc_lam[i] = (i>0 ? acc_lam[i-1] : 0) ^ lc * r_gam[i]
    for j = 2t-1 .. 0:
        acc_om[j] = (j>0 ? acc_om[j-1] : 0) ^ lc * r_gs[j]

o_lambda_c = o_t_zero ? r_gam : acc_lam
o_omega_c  = o_t_zero ? r_gs  : acc_om
o_deg_c    = min(deg_e + f, 2t+1)
```

**In the RTL.** Stage A records locations in `r_xfile` (`rs_erasure_unit.sv:141-205`). TRANS builds `r_gam` and `r_gs` (`rs_erasure_unit.sv:309-324`). The solver window is selected at `:326-344`. COMB multiplies through `Lambda_e` at `:347-412`, and the `o_t_zero` bypass is handled at `:52-54,285-288,398-412`.

## Correction and verdict (`rs_decoder_core`)

The final stage replays the buffered received word, XORs each located error magnitude into the corresponding symbol, and asks a second syndrome unit whether the result is a valid codeword.

**The math.**
Correction is addition in characteristic 2:

$$c_j = r_j \oplus e_j \quad \text{for each found root } j.$$

The block is uncorrectable when any of the following is true:

- the solver reported a degree error, or $\deg(\Lambda) > t$ (or the erasure budget was exceeded);
- the number of Chien roots does not equal $\deg(\Lambda)$;
- the Forney denominator is zero at a located root;
- the corrected word's syndromes are not all zero.

The final verdict expression is

$$w\_uncorrectable\_final = r\_sv2\_correct \;\&\&\; \bigl(r\_sv2\_bad \;||\; (r\_sv2\_roots \neq r\_sv2\_deg) \;||\; r\_sv2\_den\_zero \;||\; !w\_rechk\_zero\bigr).$$

**The pseudocode.**
```text
# C1: walk one beat
for base = 0, S, 2S, ... while base < n:
    for u = 0 .. S-1:
        pos = base + u
        hit[u] = correct_en && valid[pos] && chien_root[u]
        corr[u] = hit[u] ? forney_val[u] : 0

# C2: replay and correct
for u = 0 .. S-1:
    w_c2_sym[u] = rx[u] ^ (hit[u] ? corr[u] : 0)

# second syndrome pass over the corrected stream
rechk_zero = syndromes_all_zero(w_c2_sym)

# root count, saturated
roots_final = r_c_roots + count(hit[0..S-1])

# verdict, one cycle after the last beat leaves C2
uncorrectable = r_sv2_correct &&
                (r_sv2_bad ||
                 (r_sv2_roots != r_sv2_deg) ||
                 r_sv2_den_zero ||
                 !rechk_zero)
```

**In the RTL.** `rs_decoder_core.sv:705-724` maps lanes to symbol positions and computes hits, `:756-759` XORs corrections, `:762-778` instantiates the second syndrome unit, `:781-784` counts roots, and `:790-794` forms the final uncorrectable verdict. The status ports `out_status_ok/uncorrectable/frame_err/corrected` are driven at `:836-847`.

## Trace: RS(15,11) revisited

The script `ch07_math_trace.py` (in this directory) reproduces the section 7.3 example with the same field and the RTL-shaped algorithms above. Its output is:

```text
GF(2^4) primitive polynomial 0x13 = x^4 + x + 1
alpha order = 15; doc element vectors match

RS(15,11) t=2 b=1 received word (doc positions 0..14):
  0:alpha^0 1:alpha^6 2:alpha^1 3:alpha^12 4:0 5:alpha^0 6:alpha^1 7:alpha^4 8:alpha^2 9:alpha^8 10:alpha^5 11:alpha^13 12:alpha^3 13:alpha^14 14:alpha^9

syndromes S1..S4: alpha^4 alpha^6 alpha^5 alpha^0
riBM Lambda (degree 2): alpha^1 + alpha^6 x + alpha^0 x^2
riBM Omega: alpha^9 + alpha^0 x
Chien roots (doc positions): 3, 11
Forney magnitudes:
  j=3: alpha^5
  j=11: alpha^9
corrected word == original codeword: yes
post-correction syndromes: all zero

profile checks: RS(255,239) and RS(252,236) both have n-k=16, 2t=16, d=17
ALL CHECKS PASSED
```

The riBM locator is `alpha^1 + alpha^6 x + alpha^0 x^2`. That is exactly `alpha^1` times the Peterson locator `1 + alpha^5 x + alpha^14 x^2` from section 7.3. Because Chien search looks for zeros, the common scale factor does not move the roots: they are still at positions 3 and 11. The Forney evaluator carries the same scale, and the `off = 2t` exponent converts the high-half riBM Omega into the same ratio as the textbook evaluator, so the magnitudes come out exactly `alpha^5` at `j = 3` and `alpha^9` at `j = 11`. The corrected word matches the original codeword, and the post-correction syndromes are all zero.
