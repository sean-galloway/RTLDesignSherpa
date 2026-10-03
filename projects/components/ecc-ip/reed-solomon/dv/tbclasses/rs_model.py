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
    def ribm(self, S, erasure_count=0):
        """Sarwate-Shanbhag reformulated inversionless Berlekamp-Massey.
        Returns (Lambda[0..2t], Omega[0..t-1]) up to a common scale factor;
        Lambda[t+1..2t] are nonzero only when the block is uncorrectable.

        With erasure_count = f > 0 the input is the drop-f Forney syndrome
        list T (2t - f values, zero-padded to 2t by the caller or here) and
        the solver's updates are KILLED for the last f of the fixed 2t
        cycles: the padding would be consumed with nonzero discrepancies once
        the locator develops (proven unsound), so cycle >= 2t-f forces
        d0 = 0. The array still shifts every cycle, so the locator lands in
        the same readout cells and the result is textbook BM on T."""
        t = self.t
        L = 3 * t + 1
        D = [0] * (L + 1)          # Delta~ with one spare so D[i+1] is defined at i = 3t
        Th = [0] * (L + 1)         # Theta~
        for i in range(2 * t):
            v = S[i] if i < len(S) else 0
            D[i] = v
            Th[i] = v
        D[3 * t] = 1
        Th[3 * t] = 1
        gamma = 1
        k = 0
        for cyc in range(2 * t):
            d0 = D[0]
            if cyc >= 2 * t - erasure_count:
                d0 = 0
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

    # -- modified Euclidean key-equation solver -----------------------------------------
    @staticmethod
    def EUCLID_LW(t):
        """Width of the shifted lam~/mu~ registers. Measured over the validate()
        profiles: the highest index ever written is 2t+1 (t >= 8) or 2t+2
        (t <= 2), so 2t+3 entries, and euclid() asserts the top stays zero."""
        return 2 * t + 3

    def euclid(self, S, erasure_count=0):
        """Inversionless extended Euclid in the register form the RTL uses.

        R and Q are kept TOP-ALIGNED in 2t+1 registers (leading coefficient
        at index 2t) with nominal degrees degR, degQ; lam~ = lam * x^(2t-degR)
        and mu~ = mu * x^(2t-degQ) are kept in LW-wide registers so the
        cross-multiply needs no variable shift:

          normalise:  if R[2t] == 0:  R *= x, lam~ *= x, degR -= 1
                      elif Q[2t] == 0: Q *= x, mu~ *= x, degQ -= 1
          cross:      Rn = (Q[2t]*R ^ R[2t]*Q) * x,  Ln = (Q[2t]*lam~ ^ R[2t]*mu~) * x
                      (multiplying by x moves coefficients UP one index; the
                      cross-multiply zeroes index 2t, so this re-aligns the top)
                      if degR < degQ: (Q, mu~, degQ) <- (old R, old lam~, old degR)
                      degR = max(old degR, old degQ) - 1
          stop when degR < t; then Lambda = lam~ >> (2t - degR), Omega = R >> (2t - degR)

        Init: R = x^2t, Q = S(x) (S_{2t-1} at index 2t), lam~ = 0, mu~ = x
        (mu = 1 shifted by 2t - degQ = 1). Returns (Lambda[0..2t],
        Omega[0..t-1], cycles). Omega here is the TEXTBOOK evaluator
        (S*Lambda mod x^2t), so Forney uses X^(1-b) -- forney(..., high_half=False).
        Lambda and Omega carry one common scale factor.

        With erasure_count = f > 0 the input is the zeroed-low Forney
        syndrome window (the low f coefficients of Gamma*S mod x^2t forced
        to zero, i.e. x^f * T): Euclid consumes the polynomial as a whole,
        so zeroed-low is sound here (it is NOT for a forward-iterating BM --
        the zeroed tail would contaminate later discrepancies). The modulus
        stays x^2t and the stop threshold rises to t + ceil(f/2), the
        erasure-key-equation degree; f = 0 reduces to the errors-only t."""
        t = self.t
        T2 = 2 * t
        LW = self.EUCLID_LW(t)
        R = [0] * (T2 + 1); R[T2] = 1
        Q = [0] * (T2 + 1)
        for i in range(T2):
            Q[i + 1] = S[i]
        lam = [0] * LW
        mu = [0] * LW; mu[1] = 1
        degR, degQ = T2, T2 - 1
        stop = t + (erasure_count + 1) // 2
        cycles = 0
        self._euclid_max_lam_idx = max(getattr(self, '_euclid_max_lam_idx', 0), 1)
        while degR >= stop:
            cycles += 1
            assert cycles <= 6 * t + 4, "Euclid did not terminate"
            if R[T2] == 0:
                R = [0] + R[:-1]; lam = [0] + lam[:-1]; degR -= 1
            elif Q[T2] == 0:
                Q = [0] + Q[:-1]; mu = [0] + mu[:-1]; degQ -= 1
            else:
                a, b = R[T2], Q[T2]
                assert lam[LW - 1] == 0 and mu[LW - 1] == 0, "lam~/mu~ register too narrow"
                Rn = [self.mul(b, R[i]) ^ self.mul(a, Q[i]) for i in range(T2 + 1)]
                Ln = [self.mul(b, lam[i]) ^ self.mul(a, mu[i]) for i in range(LW)]
                assert Rn[T2] == 0
                if degR < degQ:
                    Q, mu, degQ_new = R, lam, degR
                    degR_new = degQ - 1
                    degQ = degQ_new
                else:
                    degR_new = degR - 1
                R = [0] + Rn[:-1]; lam = [0] + Ln[:-1]
                degR = degR_new
            top = max((i for i, v in enumerate(lam) if v), default=0)
            self._euclid_max_lam_idx = max(self._euclid_max_lam_idx, top)
        sh = T2 - degR
        lam_out = (lam[sh:] + [0] * sh)[:T2 + 1]
        om_out = (R[sh:] + [0] * sh)[:t]
        return lam_out, om_out, cycles

    @staticmethod
    def degree(poly):
        for i in range(len(poly) - 1, -1, -1):
            if poly[i]:
                return i
        return -1

    # -- erasure support (TASK-002, ERASURE_SUPPORT) ----------------------------
    def erasure_locator(self, positions):
        """Gamma(x) = prod_j (1 - X_j * x) over the flagged symbol indices j,
        X_j = alpha^(n-1-j). Coefficients indexed by degree, 2t+1 entries, deg
        = number of positions. Roots are exactly the erasure locations
        (Gamma(X_j^-1) = 0), the same convention the Chien search uses for the
        error locator. The per-erasure update G[i] ^= X_j * G[i-1] is also the
        hardware shape: one parallel combine cycle per flagged beat."""
        t2 = 2 * self.t
        G = [0] * (t2 + 1)
        G[0] = 1
        deg = 0
        for j in positions:
            x = self.alpha_pow(self.n - 1 - j)     # X_j; roots land at X_j^-1
            # G <- G * (1 - X_j * x): new[i] = G[i] ^ X_j * G[i-1], top down
            for i in range(deg + 1, 0, -1):
                G[i] = G[i] ^ self.mul(x, G[i - 1])
            deg += 1
        return G

    def poly_mul_mod(self, A, B, mod_deg):
        """(A * B) mod x^mod_deg; coefficients indexed by degree."""
        out = [0] * mod_deg
        for i, a in enumerate(A):
            if not a:
                continue
            for j2, b2 in enumerate(B):
                if b2 and i + j2 < mod_deg:
                    out[i + j2] ^= self.mul(a, b2)
        return out

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
    def forney(self, lam, omega, j, high_half=True):
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
        off = 2 * self.t if high_half else 0
        num = self.mul(self.alpha_pow((1 - self.b - off) * l), om)
        return self.mul(num, self.inv(dl))

    # -- whole decoder ----------------------------------------------------------------
    def decode(self, block, kes='ribm', erasures=None):
        """Returns (data_out, status, count) with status one of 'ok', 'corrected',
        'uncorrectable' and data_out the k corrected data symbols (the received
        ones when uncorrectable). kes selects the solver, 'ribm' or 'euclid'.
        erasures is None (errors-only) or a list of flagged symbol indices; the
        bound is 2e + f <= 2t, f = len(erasures), and count includes the
        erasure positions.

        The erasure path is the Forney-syndrome method and leaves the SOLVER
        ARRAYS untouched: Gamma multiplies the syndromes mod x^2t in front,
        the LOW f coefficients of the product (the evaluator tail -- reedsolo
        drops or zeroes the same ones) are stripped, and the solver runs on
        what remains with only a control change: riBM kills its update for
        the last f of the fixed 2t cycles, Euclid raises its stop threshold
        to t + ceil(f/2) on the zeroed-low window. The combined locator
        Gamma * Lambda_e then goes to Chien and Forney (which take len(lam)
        cells, so they are unchanged too). This is the shape the RTL takes:
        a Gamma-build + Forney-syndrome unit between the syndrome unit and
        the KES, and a locator multiply after it."""
        S = self.syndromes(block)
        if not any(S):
            return list(block[:self.k]), 'ok', 0
        er = sorted(set(erasures)) if erasures else []
        f = len(er)
        if f > 2 * self.t:
            return list(block[:self.k]), 'uncorrectable', 0
        if er:
            gamma = self.erasure_locator(er)
            GS = self.poly_mul_mod(gamma, S, 2 * self.t)
            T = GS[f:]
        else:
            gamma = None
            T = S
        if er and not any(T):
            # the erasures alone explain every syndrome (no unknown errors):
            # Lambda_e = 1 and neither solver may be entered (Euclid would
            # not terminate on an all-zero Q)
            lam_e_ext = [1] + [0] * (2 * self.t)
            omega = [0] * self.t
        elif kes == 'euclid':
            lam_e_ext, omega, _ = self.euclid([0] * f + T, erasure_count=f)
        else:
            lam_e_ext, omega = self.ribm(T, erasure_count=f)
        deg_e = self.degree(lam_e_ext)
        # The bounded-distance degree check: erasures shrink the error
        # budget, deg(Lambda_e) <= (2t - f)/2, which reduces to deg <= t
        # errors-only. Without it a beyond-bound block (2e + f > 2t) can
        # walk every later check onto a WRONG valid codeword (seen at
        # e = 1, f = 15: riBM "corrected" to garbage that re-checks clean).
        # deg_e < 0: the solver collapsed -- always a failure. deg_e == 0:
        # Lambda_e constant, legitimate only when erasures explain the
        # syndromes on their own.
        budget = (2 * self.t - f) // 2
        if deg_e > budget or deg_e < 0 or (deg_e == 0 and not er):
            return list(block[:self.k]), 'uncorrectable', 0
        lam_e = lam_e_ext[:self.t + 1]
        if er:
            lam = self.poly_mul_mod(gamma, lam_e, 2 * self.t + 1)
        else:
            lam = lam_e
        deg = self.degree(lam)
        roots = self.chien(lam)
        if len(roots) != deg:
            return list(block[:self.k]), 'uncorrectable', 0
        # the erasure positions are roots of Gamma by construction, hence of
        # the combined locator; if one is missing the position list itself
        # was inconsistent (a duplicate that survived, an index >= n)
        if er and not set(er) <= set(roots):
            return list(block[:self.k]), 'uncorrectable', 0
        out = list(block)
        if er:
            # Forney on the combined locator needs the combined evaluator
            # Gamma*Lambda_e*S mod x^2t with the textbook exponent 1 - b; the
            # solvers' own Omega outputs belong to the stripped (riBM) or
            # shifted (Euclid) problem and do not apply at erasure positions
            omega = self.poly_mul_mod(lam, S, 2 * self.t)
        for j in roots:
            e = self.forney(lam, omega, j, high_half=(kes != 'euclid' and not er))
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
            got_e, status_e, cnt_e = self.decode(rx, kes='euclid')
            if (got_e, status_e, cnt_e) != (got, status, cnt):
                disagree += 1
                if disagree <= 3:
                    print(f"EUCLID vs riBM disagree e={e}: {status_e}/{cnt_e} vs {status}/{cnt}")
                continue
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


    # -- erasure self-check against reedsolo --------------------------------------
    def validate_erasures(self, trials=200, seed=1):
        """Model vs reedsolo's erase_pos path on random blocks with f flagged
        erasures and e unflagged corruptions, swept through the interesting
        points of the 2e + f <= 2t bound (including just past it, and f > 2t).
        Same agreement rules as validate(), plus the beyond-bound relax:
        past 2e + f <= 2t reedsolo itself MISCORRECTS (measured: 77 wrong
        "decodes", 0 right, 172 raises in one 600-trial corpus), so there
        the model may say uncorrectable even where reedsolo returns data --
        the model's bounded-distance degree check (deg Lambda_e <=
        (2t - f)/2) makes it the stricter, safer decoder, and both solvers
        agree with each other everywhere. A flagged
        symbol is left uncorrupted in some trials -- a flag is a claim about
        the channel, not about the data."""
        rnd = random.Random(seed)
        agree = disagree = 0
        for _ in range(trials):
            data = [rnd.randrange(self.q) for _ in range(self.k)]
            enc = self.encode(data)
            f = rnd.choice([0, 1, self.t, 2 * self.t - 1, 2 * self.t, 2 * self.t + 1])
            f = min(f, self.n)
            epos = rnd.sample(range(self.n), f)
            remaining = [p for p in range(self.n) if p not in set(epos)]
            budget = max(0, (2 * self.t - f) // 2)
            e = rnd.choice([0, 1, budget, budget, budget + 1]) if budget >= 1 \
                else rnd.choice([0, 1])
            e = min(e, len(remaining))
            xpos = rnd.sample(remaining, e)
            rx = list(enc)
            for p in epos + xpos:
                rx[p] ^= rnd.randrange(1, self.q)
            if epos and rnd.random() < 0.3:
                p = rnd.choice(epos)
                rx[p] = enc[p]          # flagged but not actually corrupted
            # the decoder reports Chien roots: every flagged position is a
            # root of Gamma by construction, corrupted or not, so the
            # expected count is e + f -- unless the word is clean overall,
            # when zero syndromes return 'ok' before a flag is ever read
            n_corrupt = sum(1 for p in range(self.n) if rx[p] != enc[p])
            expect_cnt = 0 if n_corrupt == 0 else e + f
            got, status, cnt = self.decode(rx, erasures=epos)
            got_e, status_e, cnt_e = self.decode(rx, kes='euclid', erasures=epos)
            beyond = (2 * e + f > 2 * self.t) or (f > 2 * self.t)
            if (got_e, status_e, cnt_e) != (got, status, cnt):
                disagree += 1
                if disagree <= 3:
                    print(f"EUCLID vs riBM disagree e={e} f={f}: "
                          f"{status_e}/{cnt_e} vs {status}/{cnt}")
                continue
            try:
                ref = rs.rs_correct_msg(bytearray(rx) if self.m <= 8 else list(rx),
                                        2 * self.t, fcr=self.b, generator=2,
                                        erase_pos=list(epos))
                ref_data = list(ref[0])
                ref_ok = True
            except rs.ReedSolomonError:
                ref_ok = False
            if ref_ok:
                ok = (got == ref_data) and (status != 'uncorrectable') \
                    and (cnt == expect_cnt or beyond)
                # beyond the bound reedsolo's "decode" is a miscorrection
                # (property of the code); the model's budget degree check
                # makes it the stricter decoder there, which is also good
                ok = ok or (beyond and status == 'uncorrectable')
            else:
                ok = status == 'uncorrectable'
            if ok:
                agree += 1
            else:
                disagree += 1
                if disagree <= 3:
                    print(f"DISAGREE e={e} f={f} status={status} cnt={cnt} ref_ok={ref_ok}")
        return agree, disagree


if __name__ == '__main__':
    import sys
    for m, prim, t, n, b in [(8, 0x11D, 8, 255, 0), (8, 0x11D, 8, 204, 0), (8, 0x11D, 1, 21, 0),
                             (4, 0x13, 2, 15, 0), (8, 0x187, 16, 255, 112), (10, 0x409, 15, 544, 0)]:
        mdl = RSModel(m, prim, t, n, b)
        a, d = mdl.validate(trials=150)
        ae, de = mdl.validate_erasures(trials=150)
        print(f"RS({n},{n-2*t}) m={m} b={b}: agree {a} disagree {d}; erasures agree {ae} disagree {de}; "
              f"euclid max lam~ index {mdl._euclid_max_lam_idx} of LW={mdl.EUCLID_LW(t)}")
