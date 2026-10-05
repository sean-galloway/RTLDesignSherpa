#!/usr/bin/env python3
"""Trace script for Reed-Solomon HAS chapter 7 sections 7.4 and 7.5.

Pure-stdlib reference for the RS(15,11) t=2 example in section 7.3.  It
reproduces the GF(2^4) field table, mirrors the RTL shapes (LFSR encoder,
Horner syndrome cell, riBM, Chien, Forney), and verifies every numeric claim
that appears in the new pages.
"""

import sys


# GF(2^m) with the chapter's primitive polynomial
class GF:
    def __init__(self, m, prim):
        self.m = m
        self.prim = prim
        self.order = (1 << m) - 1
        self.exp = [0] * self.order
        self.log = [-1] * (1 << m)
        r = 1
        for i in range(self.order):
            self.exp[i] = r
            self.log[r] = i
            r <<= 1
            if r & (1 << m):
                r ^= prim
            r &= (1 << m) - 1

    def add(self, a, b):
        return a ^ b

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[(self.log[a] + self.log[b]) % self.order]

    def inv(self, a):
        if a == 0:
            raise ZeroDivisionError("GF inverse of zero")
        return self.exp[(-self.log[a]) % self.order]

    def pow(self, a, e):
        if a == 0:
            return 0
        return self.exp[(self.log[a] * e) % self.order]

    def alpha_pow(self, k):
        return self.exp[k % self.order]

    def to_exp(self, a):
        return self.log[a] if a else None

    def from_exp(self, e):
        return self.exp[e % self.order]


# Small polynomial helpers (coefficients indexed by degree, low to high)
def poly_eval(gf, p, x):
    v = 0
    xi = 1
    for c in p:
        v ^= gf.mul(c, xi)
        xi = gf.mul(xi, x)
    return v


def poly_mul_mod(gf, a, b, mod_deg):
    out = [0] * mod_deg
    for i, av in enumerate(a):
        if av == 0:
            continue
        for j, bv in enumerate(b):
            if bv and i + j < mod_deg:
                out[i + j] ^= gf.mul(av, bv)
    return out


def poly_degree(p):
    for i in range(len(p) - 1, -1, -1):
        if p[i]:
            return i
    return -1


def build_generator(gf, t, b):
    """g(x) = prod_{i=0}^{2t-1} (x - alpha^{b+i}); coefficients low to high."""
    g = [1]
    for i in range(2 * t):
        root = gf.alpha_pow(b + i)
        # multiply g(x) by (x + root) in characteristic 2
        new = [0] * (len(g) + 1)
        for j, c in enumerate(g):
            new[j + 1] ^= c
            new[j] ^= gf.mul(c, root)
        g = new
    return g


# Encoder: 2t-stage GF LFSR
def lfsr_step_one(gf, g, r, d):
    t2 = len(r)
    fb = gf.add(d, r[t2 - 1])
    n = [0] * t2
    n[0] = gf.mul(g[0], fb)
    for j in range(1, t2):
        n[j] = gf.add(r[j - 1], gf.mul(g[j], fb))
    return n


def encode_systematic(gf, data, n, t, b):
    """Return a full codeword (n symbols, highest-degree first) for data."""
    k = n - 2 * t
    if len(data) != k:
        raise ValueError("data length must equal k")
    g = build_generator(gf, t, b)
    r = [0] * (2 * t)
    for d in data:
        r = lfsr_step_one(gf, g, r, d)
    # r[0] is the x^0 remainder coefficient; transmission order drains the
    # highest-degree remainder coefficient first (r[2t-1] .. r[0]).
    codeword = list(data) + list(reversed(r))
    return codeword


# Syndrome unit: 2t Horner cells
def syndromes(gf, block, t, b):
    S = []
    for i in range(2 * t):
        root = gf.alpha_pow(b + i)
        s = 0
        for sym in block:
            s = gf.mul(s, root) ^ sym
        S.append(s)
    return S


# riBM key-equation solver
def ribm(gf, S, t):
    L = 3 * t + 1
    D = [0] * (L + 1)
    Th = [0] * (L + 1)
    for i in range(2 * t):
        D[i] = Th[i] = S[i]
    D[3 * t] = Th[3 * t] = 1
    gamma = 1
    k = 0
    for _ in range(2 * t):
        d0 = D[0]
        Dn = [0] * (L + 1)
        for i in range(L):
            Dn[i] = gf.mul(gamma, D[i + 1]) ^ gf.mul(d0, Th[i])
        if d0 != 0 and k >= 0:
            Th = [D[i + 1] for i in range(L)] + [0]
            gamma = d0
            k = -k - 1
        else:
            k = k + 1
        D = Dn
    lam = D[t:3 * t + 1]
    omega = D[0:t]
    return lam, omega


# Chien search in transmission order
def chien_roots(gf, lam, n):
    cells = [gf.mul(lam[i], gf.alpha_pow(-i * (n - 1))) for i in range(len(lam))]
    roots = []
    for j in range(n):
        val = 0
        for c in cells:
            val ^= c
        if val == 0:
            roots.append(j)
        cells = [gf.mul(cells[i], gf.alpha_pow(i)) for i in range(len(cells))]
    return roots


# Forney evaluator (riBM high-half Omega)
def forney(gf, lam, omega, j, n, t, b):
    l = n - 1 - j
    xinv = gf.alpha_pow(-l)
    # Omega(x^{-1}) by Horner
    om = 0
    for i in range(len(omega) - 1, -1, -1):
        om = gf.mul(om, xinv) ^ omega[i]
    # formal derivative of Lambda at x^{-1}: sum over odd i
    dl = 0
    p = 1
    for i in range(1, len(lam), 2):
        dl ^= gf.mul(lam[i], p)
        p = gf.mul(p, gf.mul(xinv, xinv))
    if dl == 0:
        return None
    off = 2 * t
    num = gf.mul(gf.alpha_pow((1 - b - off) * l), om)
    return gf.mul(num, gf.inv(dl))


# Display helpers
def fmt_exp(gf, a):
    if a == 0:
        return "0"
    return f"alpha^{gf.to_exp(a)}"


def fmt_poly(gf, p):
    terms = []
    for i, c in enumerate(p):
        if c == 0:
            continue
        if i == 0:
            terms.append(fmt_exp(gf, c))
        elif i == 1:
            terms.append(fmt_exp(gf, c) + " x")
        else:
            terms.append(fmt_exp(gf, c) + f" x^{i}")
    return " + ".join(terms) if terms else "0"


# Main trace
def main():
    # Field used by the chapter 7 example table
    m = 4
    prim = 0x13  # x^4 + x + 1, binary 10011
    gf = GF(m, prim)

    # Doc's element vector table (Table 7.2)
    doc_vectors = [
        0b0001, 0b0010, 0b0100, 0b1000, 0b0011, 0b0110, 0b1100, 0b1011,
        0b0101, 0b1010, 0b0111, 0b1110, 0b1111, 0b1101, 0b1001,
    ]
    for i, vec in enumerate(doc_vectors):
        assert gf.exp[i] == vec, f"field table mismatch at alpha^{i}"
    assert gf.log[0] == -1

    # alpha must generate every nonzero field element
    assert len(set(gf.exp)) == gf.order, "alpha is not primitive"

    # Section 7.3 received word (position = polynomial coefficient index)
    # Table 7.9 lists positions 0 .. 14 in low-degree-first order.
    received_doc = [
        gf.alpha_pow(0),   # 0  : alpha^0
        gf.alpha_pow(6),   # 1  : alpha^6
        gf.alpha_pow(1),   # 2  : alpha^1
        gf.alpha_pow(12),  # 3  : alpha^12
        0,                 # 4  : 0
        gf.alpha_pow(0),   # 5  : 1
        gf.alpha_pow(1),   # 6  : alpha
        gf.alpha_pow(4),   # 7  : alpha^4
        gf.alpha_pow(2),   # 8  : alpha^2
        gf.alpha_pow(8),   # 9  : alpha^8
        gf.alpha_pow(5),   # 10 : alpha^5
        gf.alpha_pow(13),  # 11 : alpha^13
        gf.alpha_pow(3),   # 12 : alpha^3
        gf.alpha_pow(14),  # 13 : alpha^14
        gf.alpha_pow(9),   # 14 : alpha^9
    ]

    # Original codeword: remove the two injected errors
    codeword_doc = list(received_doc)
    codeword_doc[3] = gf.add(codeword_doc[3], gf.alpha_pow(5))
    codeword_doc[11] = gf.add(codeword_doc[11], gf.alpha_pow(9))

    # RTL processing order: first-transmitted symbol is the highest-degree coeff
    rtl_rx = list(reversed(received_doc))

    n = 15
    t = 2
    b = 1  # narrow-sense roots alpha^1 .. alpha^4, matching Table 7.10

    # Syndromes
    S = syndromes(gf, rtl_rx, t, b)
    doc_syndromes = [gf.alpha_pow(e) for e in (4, 6, 5, 0)]
    assert S == doc_syndromes, f"syndromes mismatch: {S} != {doc_syndromes}"

    # riBM
    lam, omega = ribm(gf, S, t)
    deg_lam = poly_degree(lam)
    assert deg_lam == t, f"expected deg(Lambda) = {t}, got {deg_lam}"

    # Chien search in RTL order
    rtl_roots = chien_roots(gf, lam, n)
    doc_roots = sorted({n - 1 - r for r in rtl_roots})
    assert doc_roots == [3, 11], f"Chien roots mismatch: {doc_roots}"

    # Forney magnitudes mapped back to doc positions
    mag = {}
    for doc_j in doc_roots:
        rtl_j = n - 1 - doc_j
        e = forney(gf, lam, omega, rtl_j, n, t, b)
        assert e is not None, "Forney denominator zero at a found root"
        mag[doc_j] = e
    assert mag[3] == gf.alpha_pow(5), f"magnitude at j=3 mismatch"
    assert mag[11] == gf.alpha_pow(9), f"magnitude at j=11 mismatch"

    # Correction in RTL order, then map back to doc order
    rtl_corr = list(rtl_rx)
    for rtl_j in rtl_roots:
        rtl_corr[rtl_j] = gf.add(rtl_corr[rtl_j], forney(gf, lam, omega, rtl_j, n, t, b))
    corrected_doc = list(reversed(rtl_corr))
    assert corrected_doc == codeword_doc, "corrected word does not match codeword"

    # Re-check syndromes on the corrected word
    S2 = syndromes(gf, list(reversed(corrected_doc)), t, b)
    assert all(s == 0 for s in S2), f"post-correction syndromes not zero: {S2}"

    # Encoder sanity check: encode a random message and verify zero syndromes
    test_data = [gf.alpha_pow(i * 7 % gf.order) for i in range(n - 2 * t)]
    test_cw = encode_systematic(gf, test_data, n, t, b)
    S_enc = syndromes(gf, test_cw, t, b)
    assert all(s == 0 for s in S_enc), "encoder parity did not produce zero syndromes"

    # Parameter relation checks from section 7.4
    profiles = [
        (255, 239, 8, 8, False),
        (252, 236, 8, 8, True),
    ]
    for n_p, k_p, t_p, m_p, shortened in profiles:
        assert n_p - k_p == 2 * t_p, f"n-k != 2t for ({n_p},{k_p}) t={t_p}"
        assert 2 * t_p + 1 == 17, f"designed distance != 17"
        if shortened:
            assert n_p < (1 << m_p) - 1, "shortened code is not shorter than full length"
            assert n_p - k_p == 2 * t_p, "shortened parity count changed"

    # Print compact trace ---------------------------------------------------
    print(f"GF(2^{m}) primitive polynomial 0x{prim:02X} = x^{m} + x + 1")
    print(f"alpha order = {gf.order}; doc element vectors match")
    print()
    print("RS(15,11) t=2 b=1 received word (doc positions 0..14):")
    print("  " + " ".join(f"{i}:{fmt_exp(gf, v)}" for i, v in enumerate(received_doc)))
    print()
    print(f"syndromes S1..S4: {' '.join(fmt_exp(gf, s) for s in S)}")
    print(f"riBM Lambda (degree {deg_lam}): {fmt_poly(gf, lam)}")
    print(f"riBM Omega: {fmt_poly(gf, omega)}")
    print(f"Chien roots (doc positions): {', '.join(str(j) for j in doc_roots)}")
    print("Forney magnitudes:")
    for j in sorted(mag):
        print(f"  j={j}: {fmt_exp(gf, mag[j])}")
    print("corrected word == original codeword: yes")
    print("post-correction syndromes: all zero")
    print()
    print("profile checks: RS(255,239) and RS(252,236) both have n-k=16, 2t=16, d=17")
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
