#!/usr/bin/env python3
"""Trace every numeric claim in the BCH HAS chapter 7.4 and 7.5 pages.

Pure stdlib. Run from anywhere; it uses only the command line.
"""
import sys


def build_gf(m, prim_poly):
    """Return exp/log tables for GF(2^m) with primitive polynomial prim_poly."""
    q = (1 << m) - 1
    exp = [0] * q
    log = [None] * (1 << m)
    x = 1
    for e in range(q):
        exp[e] = x
        log[x] = e
        nxt = x << 1
        if nxt & (1 << m):
            nxt ^= prim_poly
        x = nxt & ((1 << m) - 1)
    return exp, log


def gf_mul(a, b, exp, log):
    if a == 0 or b == 0:
        return 0
    q = len(exp)
    return exp[(log[a] + log[b]) % q]


def gf_square(a, exp, log):
    if a == 0:
        return 0
    q = len(exp)
    return exp[(2 * log[a]) % q]


def gf_inv(a, exp, log):
    if a == 0:
        raise ZeroDivisionError
    q = len(exp)
    return exp[(q - log[a]) % q]


def gf_pow(a, e, exp, log):
    if a == 0:
        return 0
    q = len(exp)
    return exp[(log[a] * e) % q]


def alpha_pow(e, m, exp):
    q = (1 << m) - 1
    return exp[e % q]


def poly_mul(a, b, exp, log):
    """Multiply polynomials with GF(2^m) coefficients; lowest degree first."""
    if not a or not b:
        return [0]
    res = [0] * (len(a) + len(b) - 1)
    for i, av in enumerate(a):
        if av == 0:
            continue
        for j, bv in enumerate(b):
            if bv == 0:
                continue
            res[i + j] ^= gf_mul(av, bv, exp, log)
    return res


def build_generator(m, prim_poly, t, b, exp, log):
    """Build g(x) from distinct conjugates of alpha^b .. alpha^(b+2t-1)."""
    n_full = (1 << m) - 1
    visited = [False] * n_full
    poly = [1]
    for i in range(2 * t):
        e = ((b + i) % n_full + n_full) % n_full
        cur = e
        while not visited[cur]:
            visited[cur] = True
            root = alpha_pow(cur, m, exp)
            poly = poly_mul(poly, [root, 1], exp, log)
            cur = (cur * 2) % n_full
    # Coefficients must lie in GF(2).
    for c in poly:
        assert c in (0, 1), "generator coefficient not binary"
    return poly


def generator_degree(m, prim_poly, t, b):
    exp, log = build_gf(m, prim_poly)
    g = build_generator(m, prim_poly, t, b, exp, log)
    return len(g) - 1


def generator_bits(m, prim_poly, t, b, exp, log):
    g = build_generator(m, prim_poly, t, b, exp, log)
    return [1 if c != 0 else 0 for c in g[:-1]]  # g_0 .. g_{deg-1}


def lfsr_step(r, d, g_bits):
    """One bit-serial LFSR update; r[0] is the low-order remainder lane."""
    deg = len(g_bits)
    fb = d ^ r[-1]
    nxt = [0] * deg
    for j in range(deg):
        prev = 0 if j == 0 else r[j - 1]
        nxt[j] = prev ^ (fb if g_bits[j] else 0)
    return nxt


def beat_unroll(r, bits, g_bits):
    """Apply lfsr_step for each bit in a beat (low lanes first)."""
    chain = [r]
    for d in bits:
        chain.append(lfsr_step(chain[-1], d, g_bits))
    return chain


def encode_systematic(msg_bits, g_bits, bits_per_beat=1):
    """Systematic encode: data bits MSB first; parity returned MSB lane first."""
    r = [0] * len(g_bits)
    # Process full beats; for the worked example B == 1.
    for start in range(0, len(msg_bits), bits_per_beat):
        beat = msg_bits[start:start + bits_per_beat]
        chain = beat_unroll(r, beat, g_bits)
        r = chain[len(beat)]
    parity = list(reversed(r))  # high-order lane first
    return msg_bits + parity


def horner_syndrome(bits, root, exp, log):
    """Evaluate sum bits[i] * root^{n-1-i}; bits MSB first."""
    s = 0
    for b in bits:
        s = gf_mul(s, root, exp, log) ^ b
    return s


def odd_syndrome_roots(b, t):
    first_odd = b + ((b + 1) % 2)
    return [first_odd + 2 * j for j in range(t)]


def compute_odd_syndromes(rx_bits, m, prim_poly, t, b, exp, log):
    roots = odd_syndrome_roots(b, t)
    return [horner_syndrome(rx_bits, alpha_pow(r, m, exp), exp, log) for r in roots]


def expand_syndromes(odd, t, exp, log):
    """Reconstruct S_1 .. S_{2t}; odd[0] is S_1, odd[1] is S_3, ..."""
    full = [0] * (2 * t)
    for idx in range(1, 2 * t + 1):
        if idx % 2 == 1:
            full[idx - 1] = odd[idx // 2]
        else:
            full[idx - 1] = gf_square(full[idx // 2 - 1], exp, log)
    return full


def ribm(odd, t, exp, log):
    """RTL-style riBM: returns Lambda_0 .. Lambda_{2t} (Delta_t .. Delta_{3t})."""
    full = expand_syndromes(odd, t, exp, log)
    npe = 3 * t + 1
    delta = full[:] + [0] * (npe - len(full))
    delta[npe - 1] = 1
    theta = list(delta)
    gamma = 1
    k = 0
    for _ in range(2 * t):
        disc = delta[0]
        swap = (disc != 0) and (k >= 0)
        new_delta = [0] * npe
        new_theta = [0] * npe
        for i in range(npe):
            dnext = delta[i + 1] if i + 1 < npe else 0
            new_delta[i] = gf_mul(gamma, dnext, exp, log) ^ gf_mul(disc, theta[i], exp, log)
            new_theta[i] = dnext if swap else theta[i]
        delta = new_delta
        theta = new_theta
        gamma = disc if swap else gamma
        k = (-k - 1) if swap else (k + 1)
    return delta[t:]  # Lambda_0 .. Lambda_{2t}


def poly_degree(poly):
    return max((i for i, v in enumerate(poly) if v != 0), default=-1)


def monic_page_locator(raw_lambda, exp, log):
    """Return the monic textbook locator whose reciprocal is a scalar multiple of raw_lambda.

    The raw riBM/RTL output is Lambda_raw(x) = c * x^d * Lambda_page(1/x).
    Multiplying x^d * Lambda_raw(1/x) by 1/c gives Lambda_page(x).
    Because Lambda_page is monic and its reciprocal has constant term 1,
    c equals Lambda_raw[0]; so we scale by inv(Lambda_raw[0]).
    """
    d = poly_degree(raw_lambda)
    if d < 0:
        return [0]
    scale = gf_inv(raw_lambda[0], exp, log)
    return [gf_mul(raw_lambda[d - i], scale, exp, log) for i in range(d + 1)]


def chien_rtl(lambda_raw, n, bits_per_beat, m, exp, log):
    """RTL-style Chien: evaluate lambda_raw(alpha^{-(n-1-p)}), p = 0..n-1."""
    q = (1 << m) - 1
    positions = []
    # Per-cell state r_c[i] = Lambda_i * alpha^{-i*(n-1)}.
    rc = [0] * len(lambda_raw)
    for i, li in enumerate(lambda_raw):
        if li != 0:
            rc[i] = gf_mul(li, alpha_pow(-i * (n - 1), m, exp), exp, log)
    for p in range(n):
        X = alpha_pow(-(n - 1 - p), m, exp)
        val = 0
        for i, li in enumerate(lambda_raw):
            if li != 0:
                val ^= gf_mul(li, gf_pow(X, i, exp, log), exp, log)
        if val == 0:
            positions.append(p)
        # Step cells by one beat (B == 1 for this trace).
        for i in range(len(rc)):
            if rc[i] != 0:
                rc[i] = gf_mul(rc[i], alpha_pow(i * bits_per_beat, m, exp), exp, log)
    return set(positions)


def chien_exponents(lambda_monic, n, m, exp, log):
    """Textbook Chien: roots are alpha^j; return the exponents j."""
    q = (1 << m) - 1
    roots = set()
    for j in range(q):
        X = alpha_pow(j, m, exp)
        val = 0
        for i, li in enumerate(lambda_monic):
            if li != 0:
                val ^= gf_mul(li, gf_pow(X, i, exp, log), exp, log)
        if val == 0:
            roots.add(j)
    return roots


def int_to_bits(val, n):
    return [(val >> i) & 1 for i in reversed(range(n))]


def bits_to_int(bits):
    val = 0
    for b in bits:
        val = (val << 1) | b
    return val


def alpha_name(v, exp, log):
    if v == 0:
        return "0"
    return f"alpha^{log[v]}"


def main():
    errors = []

    # -------------------------------------------------------------------------
    # GF(2^4) worked example from sections 7.2 / 7.3.
    # -------------------------------------------------------------------------
    M4 = 4
    PRIM4 = 0x13  # x^4 + x + 1, matches Table 7.2 in section 7.1.
    exp4, log4 = build_gf(M4, PRIM4)

    # Sanity checks against Table 7.2 and section 7.3 line 124.
    assert exp4[1] == 0b0010, "alpha^1 vector mismatch"
    assert exp4[14] == 0b1001, "alpha^14 vector mismatch"
    assert alpha_pow(4, M4, exp4) == 0b0011, "alpha^4 vector mismatch"

    # Codeword from section 7.2 and received word from section 7.3.
    c_bits = int_to_bits(0b100110111000010, 15)
    R_bits = int_to_bits(0b100100111001010, 15)
    msg_bits = int_to_bits(0b1001101, 7)

    g4 = build_generator(M4, PRIM4, t=2, b=1, exp=exp4, log=log4)
    g_bits4 = generator_bits(M4, PRIM4, t=2, b=1, exp=exp4, log=log4)
    assert len(g4) - 1 == 8, "deg g for (15,7) must be 8"
    assert g_bits4 == [1, 0, 0, 0, 1, 0, 1, 1], "g(x) coefficient mismatch"

    enc4 = encode_systematic(msg_bits, g_bits4, bits_per_beat=1)
    assert enc4 == c_bits, "encoder output must match section 7.2 codeword"
    assert bits_to_int(enc4[len(msg_bits):]) == 0b11000010, "parity mismatch"

    # Syndromes.
    odd4 = compute_odd_syndromes(R_bits, M4, PRIM4, t=2, b=1, exp=exp4, log=log4)
    S1, S3 = odd4
    assert log4[S1] == 12, f"S1 expected alpha^12, got {alpha_name(S1, exp4, log4)}"
    assert log4[S3] == 7, f"S3 expected alpha^7, got {alpha_name(S3, exp4, log4)}"

    full4 = expand_syndromes(odd4, t=2, exp=exp4, log=log4)
    assert log4[full4[1]] == 9, "S2 mismatch"
    assert log4[full4[3]] == 3, "S4 mismatch"

    # Key-equation solver (RTL-style raw output).
    lam4_raw = ribm(odd4, t=2, exp=exp4, log=log4)
    deg4 = poly_degree(lam4_raw)
    assert deg4 == 2, f"lambda degree expected 2, got {deg4}"
    more_than_t = any(v != 0 for v in lam4_raw[3:])
    assert not more_than_t, "unexpected more-than-t flag"

    # Textbook monic locator used by the section-7.3 Chien table.
    lam4_page = monic_page_locator(lam4_raw[:3], exp4, log4)
    assert lam4_page[2] == 1, "monic locator leading coefficient must be 1"
    assert log4[lam4_page[1]] == 12, "page Lambda_1 mismatch"
    assert log4[lam4_page[0]] == 13, "page Lambda_0 mismatch"

    # Chien: RTL position counter vs textbook exponent roots.
    rtl_positions = chien_rtl(lam4_raw, n=15, bits_per_beat=1, m=M4, exp=exp4, log=log4)
    page_roots = chien_exponents(lam4_page, n=15, m=M4, exp=exp4, log=log4)
    # The section-7.3 example numbers its roots by polynomial exponent.
    assert page_roots == {3, 10}, f"page Chien roots expected {{3,10}}, got {page_roots}"
    # The RTL reports transmission-order positions; they are the complement.
    assert rtl_positions == {14 - p for p in page_roots}, "RTL/textbook root mapping inconsistent"

    # Correction flips the transmission-order bits found by the RTL Chien.
    corrected = list(R_bits)
    for p in rtl_positions:
        corrected[p] ^= 1
    assert corrected == c_bits, "corrected word must match original codeword"

    # -------------------------------------------------------------------------
    # Parameter relation checks for the four RTL/board profiles.
    # -------------------------------------------------------------------------
    profiles = [
        # (m, prim, t, n, b, expected_deg_g, expected_k)
        (6, 0x43, 1, 63, 1, 6, 57),
        (6, 0x43, 1, 63, 0, 7, 56),
        (6, 0x43, 2, 63, 1, 12, 51),
        (13, 0x201B, 8, 4224, 1, 104, 4120),
    ]
    for m, prim, t, n, b, exp_deg, exp_k in profiles:
        deg = generator_degree(m, prim, t, b)
        k = n - deg
        if deg != exp_deg:
            errors.append(f"profile m={m} t={t} b={b}: deg_g={deg}, expected {exp_deg}")
        if k != exp_k:
            errors.append(f"profile m={m} t={t} b={b}: k={k}, expected {exp_k}")

    if errors:
        for e in errors:
            print(f"FAIL: {e}")
        sys.exit(1)

    # -------------------------------------------------------------------------
    # Compact trace output used by section 7.5.
    # -------------------------------------------------------------------------
    print("BCH(15,7) t=2 trace (bit 14 first):")
    print(f"  codeword           = {bits_to_int(c_bits):015b}")
    print(f"  received           = {bits_to_int(R_bits):015b}")
    print(f"  S_1                = {alpha_name(S1, exp4, log4)}  ({S1:04b})")
    print(f"  S_3                = {alpha_name(S3, exp4, log4)}  ({S3:04b})")
    print(f"  S_2                = {alpha_name(full4[1], exp4, log4)}  ({full4[1]:04b})")
    print(f"  S_4                = {alpha_name(full4[3], exp4, log4)}  ({full4[3]:04b})")
    raw_names = ", ".join(alpha_name(v, exp4, log4) for v in lam4_raw[:3])
    print(f"  raw riBM Lambda    = {raw_names}")
    def term_name(i, v):
        if i == 0:
            return alpha_name(v, exp4, log4)
        if v == 1:
            return f"X^{i}" if i != 1 else "X"
        base = alpha_name(v, exp4, log4)
        return f"{base}*X^{i}" if i != 1 else f"{base}*X"

    print("  monic locator      = " + " + ".join(
        term_name(i, v) for i, v in enumerate(lam4_page) if v != 0
    ))
    print(f"  Chien roots (exp)  = {sorted(page_roots)}")
    print(f"  RTL positions p    = {sorted(rtl_positions)}")
    print(f"  corrected          = {bits_to_int(corrected):015b}")
    print()
    print("Profile deg(g) and k checks:")
    for m, prim, t, n, b, exp_deg, exp_k in profiles:
        print(f"  m={m:2d} t={t} b={b}: n={n}, deg_g={exp_deg}, k={exp_k}  OK")
    print()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
