"""
Reed-Solomon decoder reference in the hardware's own algorithms

Mirrors what the RTL does step for step -- Horner syndromes in transmission
order, the riBM key-equation solver (Sarwate-Shanbhag 2001), Chien search from
the first transmitted position, Forney with the first root b -- so each RTL
block has an EXACT golden, not just an end-to-end one. The field arithmetic is
reedsolo's (gf_mul, gf_pow, gf_inverse after init_tables), never a table of our
own (area CLAUDE.md rule). validate() proves the model against reedsolo's own
decoder before any RTL is scored against it.

Conventions (shared with the RTL):
  - a block is a list of n symbols in transmission order; symbol j has
    location X_j = alpha^(n-1-j), so the first symbol is the highest power
  - S_i = r(alpha^(b+i)) for i = 0 .. 2t-1, computed by Horner as symbols arrive
  - Lambda has t+1 coefficients (index = degree), Omega has t (riBM output)
  - a block is uncorrectable when deg(Lambda) > t (riBM's array holds
    Lambda_{t+1..2t} at indices 2t+1..3t), when the number of Chien roots
    differs from deg(Lambda), or when the corrected word's syndromes are
    not all zero (the re-check, which catches the miscorrections the first
    two cannot)

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import random

import reedsolo as rs


class RSModel:
    def __init__(self, m, prim, t, n, b=0):
        self.m, self.prim, self.t, self.n, self.b = m, prim, t, n, b
        self.k = n - 2 * t
        self.q = 1 << m
        rs.init_tables(prim=prim, generator=2, c_exp=m)
        self.alpha = 2

    # -- helpers on reedsolo's field -------------------------------------------
    def mul(self, a, b):
        return rs.gf_mul(a, b)

    def alpha_pow(self, k):
        return rs.gf_pow(self.alpha, k % (self.q - 1))

    def inv(self, a):
        return rs.gf_inverse(a)

    # -- encoder ----------------------------------------------------------------
    def encode(self, data):
        enc = rs.rs_encode_msg(bytearray(data) if self.m <= 8 else list(data),
                               2 * self.t, fcr=self.b, generator=2)
        return list(enc)

    # -- syndromes: Horner in transmission order --------------------------------
    def syndromes(self, block):
        """S_i = r(alpha^(b+i)); returns 2t values. Cell i keeps s <- s*alpha^(b+i) ^ r_j."""
        S = []
        for i in range(2 * self.t):
            root = self.alpha_pow(self.b + i)
            s = 0
            for sym in block:
                s = self.mul(s, root) ^ sym
            S.append(s)
        return S

    # -- riBM key-equation solver -------------------------------------------------
    def ribm(self, S):
        """Sarwate-Shanbhag reformulated inversionless Berlekamp-Massey.
        Returns (Lambda[0..2t], Omega[0..t-1]) up to a common scale factor;
        Lambda[t+1..2t] are nonzero only when the block is uncorrectable."""
        t = self.t
        L = 3 * t + 1
        D = [0] * (L + 1)          # Delta~ with one spare so D[i+1] is defined at i = 3t
        Th = [0] * (L + 1)         # Theta~
        for i in range(2 * t):
            D[i] = S[i]
            Th[i] = S[i]
        D[3 * t] = 1
        Th[3 * t] = 1
        gamma = 1
        k = 0
        for _ in range(2 * t):
            d0 = D[0]
            Dn = [0] * (L + 1)
            for i in range(L):
                Dn[i] = self.mul(gamma, D[i + 1]) ^ self.mul(d0, Th[i])
            if d0 != 0 and k >= 0:
                Th = [D[i + 1] for i in range(L)] + [0]
                gamma = d0
                k = -k - 1
            else:
                k = k + 1
            D = Dn
        omega = D[0:t]
        # Lambda_0..Lambda_t sit at t..2t; the entries above (2t+1 .. 3t) are
        # Lambda_{t+1} .. Lambda_{2t}. Any of them nonzero means the true
        # locator has degree > t -- more than t errors -- which is the
        # degree check the RTL applies. Return all 2t+1 so callers can.
        lam = D[t:3 * t + 1]
        return lam, omega

    @staticmethod
    def degree(poly):
        for i in range(len(poly) - 1, -1, -1):
            if poly[i]:
                return i
        return -1

    # -- Chien search in transmission order -----------------------------------------
    def chien(self, lam):
        """Evaluate Lambda(alpha^-l) for l = n-1 .. 0 (symbol j has l = n-1-j).
        Cell i holds lam[i] * alpha^(-i*l); stepping to the next symbol
        multiplies cell i by alpha^i. Returns the list of symbol indices j
        where Lambda(X_j^-1) == 0."""
        roots = []
        cells = [self.mul(lam[i], self.alpha_pow(-i * (self.n - 1))) for i in range(len(lam))]
        for j in range(self.n):
            val = 0
            for c in cells:
                val ^= c
            if val == 0:
                roots.append(j)
            cells = [self.mul(cells[i], self.alpha_pow(i)) for i in range(len(cells))]
        return roots

    # -- Forney -------------------------------------------------------------------------
    def forney(self, lam, omega, j):
        """Error value at symbol index j, X = alpha^(n-1-j):

            e = X^(1 - b - 2t) * Omega^(X^-1) / Lambda'(X^-1)

        riBM's evaluator is the HIGH half of S(x)Lambda(x) -- coefficients 2t
        .. 3t-1, verified equal in validate() -- not the textbook Omega =
        S*Lambda mod x^2t, so the Forney exponent carries an extra -2t. With
        the textbook Omega the exponent would be 1 - b (Blahut). Lambda' in
        characteristic 2 keeps the odd-degree terms only."""
        l = self.n - 1 - j
        xinv = self.alpha_pow(-l)
        om = 0
        for i in range(len(omega) - 1, -1, -1):
            om = self.mul(om, xinv) ^ omega[i]
        # formal derivative: sum over odd i of lam[i] * x^(i-1)
        dl = 0
        p = 1
        for i in range(1, len(lam), 2):
            dl ^= self.mul(lam[i], p)
            p = self.mul(p, self.mul(xinv, xinv))
        if dl == 0:
            return None
        num = self.mul(self.alpha_pow((1 - self.b - 2 * self.t) * l), om)
        return self.mul(num, self.inv(dl))

    # -- whole decoder ----------------------------------------------------------------
    def decode(self, block):
        """Returns (data_out, status) with status one of 'ok', 'corrected', 'uncorrectable'
        and data_out the k corrected data symbols (the received ones when uncorrectable)."""
        S = self.syndromes(block)
        if not any(S):
            return list(block[:self.k]), 'ok', 0
        lam_ext, omega = self.ribm(S)
        deg = self.degree(lam_ext)
        if deg > self.t or deg < 1:
            return list(block[:self.k]), 'uncorrectable', 0
        lam = lam_ext[:self.t + 1]
        roots = self.chien(lam)
        if len(roots) != deg:
            return list(block[:self.k]), 'uncorrectable', 0
        out = list(block)
        for j in roots:
            e = self.forney(lam, omega, j)
            if e is None:
                return list(block[:self.k]), 'uncorrectable', 0
            out[j] ^= e
        # Re-check: the corrected word must be a codeword. With more than t
        # errors the locator can have degree d <= t and exactly d roots and
        # still be wrong (seen on RS(15,11) with 3 errors); the degree and
        # root-count checks cannot see it, the syndromes of the result can.
        # The RTL runs a second syndrome unit over the corrected stream.
        if any(self.syndromes(out)):
            return list(block[:self.k]), 'uncorrectable', 0
        return out[:self.k], 'corrected', len(roots)

    # -- self-check against reedsolo ---------------------------------------------------
    def validate(self, trials=200, seed=1):
        """Model vs reedsolo on random blocks with 0..t+1 errors. Where reedsolo
        decodes, the model must produce the same data and the same correction
        count; where reedsolo raises, the model must say uncorrectable OR
        produce exactly what reedsolo would (miscorrection is a property of
        the code, not the algorithm). Returns (agree, disagree)."""
        rnd = random.Random(seed)
        agree = disagree = 0
        for _ in range(trials):
            data = [rnd.randrange(self.q) for _ in range(self.k)]
            enc = self.encode(data)
            # syndromes of a clean codeword must be zero
            assert not any(self.syndromes(enc)), "syndromes of a codeword are not zero"
            # and the model's syndromes are reedsolo's (its list carries a leading 0)
            ref_s = list(rs.rs_calc_syndromes(bytearray(enc) if self.m <= 8 else list(enc),
                                              2 * self.t, fcr=self.b, generator=2))[1:]
            assert ref_s == [0] * (2 * self.t)
            e = rnd.choice([0, 1, self.t - 1, self.t, self.t, self.t + 1]) if self.t > 1 \
                else rnd.choice([0, 1, 1, 2])
            e = max(0, min(e, self.n))
            pos = rnd.sample(range(self.n), e)
            rx = list(enc)
            for p in pos:
                rx[p] ^= rnd.randrange(1, self.q)
            ref_s = list(rs.rs_calc_syndromes(bytearray(rx) if self.m <= 8 else list(rx),
                                              2 * self.t, fcr=self.b, generator=2))[1:]
            assert ref_s == self.syndromes(rx), "Horner syndromes differ from reedsolo's"
            if 0 < e <= self.t:
                # riBM's evaluator is the high half of S*Lambda (with the full
                # 2t+1 locator); keep that fact checked on correctable blocks
                S = self.syndromes(rx)
                lam_ext, om = self.ribm(S)
                prod = [0] * (2 * self.t + len(lam_ext))
                for i, sv in enumerate(S):
                    for j2, lv in enumerate(lam_ext):
                        prod[i + j2] ^= self.mul(sv, lv)
                assert om == prod[2 * self.t:3 * self.t], "riBM evaluator is not (S*L)[2t:3t]"
            got, status, cnt = self.decode(rx)
            try:
                ref = rs.rs_correct_msg(bytearray(rx) if self.m <= 8 else list(rx),
                                        2 * self.t, fcr=self.b, generator=2)
                ref_data = list(ref[0])
                ref_ok = True
            except rs.ReedSolomonError:
                ref_ok = False
            if ref_ok:
                ok = (got == ref_data) and (status != 'uncorrectable') and (cnt == e or e > self.t)
            else:
                ok = status == 'uncorrectable'
            if ok:
                agree += 1
            else:
                disagree += 1
                if disagree <= 3:
                    print(f"DISAGREE e={e} pos={pos} status={status} cnt={cnt} ref_ok={ref_ok}")
        return agree, disagree


if __name__ == '__main__':
    for m, prim, t, n, b in [(8, 0x11D, 8, 255, 0), (8, 0x11D, 8, 204, 0), (8, 0x11D, 1, 21, 0),
                             (4, 0x13, 2, 15, 0), (8, 0x187, 16, 255, 112), (10, 0x409, 15, 544, 0)]:
        mdl = RSModel(m, prim, t, n, b)
        a, d = mdl.validate(trials=150)
        print(f"RS({n},{n-2*t}) m={m} b={b}: agree {a} disagree {d}")
