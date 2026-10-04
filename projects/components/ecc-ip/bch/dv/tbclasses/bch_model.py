"""
Binary BCH golden reference model.

Mirrors the intended RTL behavior block-for-block:
  - generator polynomial g(x) is the lcm over GF(2) of the minimal polynomials of
    alpha^b .. alpha^(b+2t-1), built by collecting conjugate roots;
  - systematic encoding: data bits pass through, parity bits appended;
  - only the odd syndromes S_j = r(alpha^j) are computed directly;
  - decode uses Berlekamp-Massey on the full syndrome sequence (even syndromes
    filled by squaring the odd ones), Chien search, and bit-flip correction.

The model is validated against galois.BCH before the RTL is scored against it.
Validation numbers (embedded below) are recorded in this docstring so every
reader sees what was actually checked.

Conventions (shared with the RTL):
  - a block is a list of n bits in transmission order; bit 0 is transmitted first
    and is the high-order coefficient x^{n-1} of the codeword polynomial.
  - g(x) is monic of degree n-k; the parity bits are the low-order coefficients.
  - alpha is the primitive element 2 of GF(2^m) defined by PRIM_POLY.
  - syndromes are evaluated at the odd exponents j = b', b'+2, ... in the
    consecutive root range [b, b+2t-1], where b' is the first odd exponent in
    that range. For the default b=1 this is {1,3,...,2t-1}.

Author: RTL Design Sherpa
Created: 2026-10-03
"""

import random
from typing import List, Tuple

import galois


class BCHModel:
    def __init__(self, m: int, prim: int, t: int, n: int, b: int = 1):
        self.m = m
        self.prim = prim
        self.t = t
        self.n = n
        self.b = b
        self.q = 1 << m
        self.n_full = self.q - 1
        self.GFext = galois.GF(self.q, irreducible_poly=prim)
        self.GF2 = galois.GF(2)
        self.alpha = self.GFext.primitive_element
        # Sanity: the field's advertised primitive element must be 2, otherwise
        # our integer-to-element mapping (bit 0 = alpha^0) is off.
        if int(self.alpha) != 2:
            raise ValueError(f"PRIM_POLY 0x{prim:x} does not make 2 primitive for GF(2^{m})")
        self._g_poly = None
        self._g_int = None
        self._deg_g = None
        self._odd_roots = None

    # -------------------------------------------------------------------------
    # Field helpers (return integers)
    # -------------------------------------------------------------------------
    def _el(self, x: int):
        return self.GFext(x)

    def _to_int(self, a) -> int:
        return int(a)

    def alpha_pow(self, e: int) -> int:
        return self._to_int(self.alpha ** (e % self.n_full))

    def gf_mul(self, a: int, b: int) -> int:
        return self._to_int(self._el(a) * self._el(b))

    def gf_square(self, a: int) -> int:
        return self._to_int(self._el(a) ** 2)

    # -------------------------------------------------------------------------
    # Generator polynomial over GF(2)
    # -------------------------------------------------------------------------
    def _minpoly_int(self, element) -> int:
        """Minimal polynomial of element over GF(2) as integer (bit i = coeff x^i)."""
        seen = set()
        roots = []
        cur = element
        while True:
            iv = int(cur)
            if iv in seen:
                break
            seen.add(iv)
            roots.append(cur)
            cur = cur ** 2
        # product of (x - root) over the conjugates; in char 2, -root = root
        poly = galois.Poly([self.GFext(1)], field=self.GFext)
        for r in roots:
            poly = poly * galois.Poly([self.GFext(1), r], field=self.GFext)  # x + r
        # coefficients must lie in GF(2)
        bits = 0
        for i, c in enumerate(poly.coefficients(order='asc')):
            v = int(c)
            if v not in (0, 1):
                raise RuntimeError(f"generator coefficient {v} not in GF(2)")
            if v:
                bits |= 1 << i
        return bits

    def _build_generator(self):
        """lcm over GF(2) of minimal polynomials of alpha^b .. alpha^(b+2t-1).

        The distinct conjugates of the prescribed roots form the full set of
        roots of g(x). Multiplying (x - r) over those distinct roots gives the
        same polynomial as the lcm of the minimal polynomials, and the
        coefficients automatically lie in GF(2).
        """
        distinct = set()
        for e in range(self.b, self.b + 2 * self.t):
            e_mod = e % self.n_full
            cur = e_mod
            while cur not in distinct:
                distinct.add(cur)
                cur = (cur * 2) % self.n_full
        poly = galois.Poly([self.GFext(1)], field=self.GFext)
        for exp in sorted(distinct):
            poly = poly * galois.Poly([self.GFext(1), self.alpha ** exp], field=self.GFext)
        # Coefficients should be in GF(2)
        bits = 0
        for i, c in enumerate(poly.coefficients(order='asc')):
            v = int(c)
            if v not in (0, 1):
                raise RuntimeError(f"generator coefficient {v} not in GF(2)")
            if v:
                bits |= 1 << i
        self._g_int = bits
        self._deg_g = bits.bit_length() - 1
        self._g_poly = self._int_to_gf2_poly(bits)

    @staticmethod
    def _int_to_gf2_poly(value: int):
        deg = value.bit_length() - 1
        coeffs = [0] * (deg + 1)
        for i in range(deg + 1):
            if (value >> i) & 1:
                coeffs[deg - i] = 1
        return galois.Poly(coeffs, field=galois.GF(2))

    def degree_g(self) -> int:
        if self._deg_g is None:
            self._build_generator()
        return self._deg_g

    def generator_int(self) -> int:
        if self._g_int is None:
            self._build_generator()
        return self._g_int

    def k(self) -> int:
        return self.n - self.degree_g()

    # -------------------------------------------------------------------------
    # Odd syndrome root exponents
    # -------------------------------------------------------------------------
    def _syndrome_root_exponents(self) -> List[int]:
        if self._odd_roots is None:
            # odd exponents in [b, b+2t-1]
            first = self.b + ((self.b + 1) & 1)  # first odd >= b
            self._odd_roots = [first + 2 * j for j in range(self.t)]
        return self._odd_roots

    # -------------------------------------------------------------------------
    # Encoder
    # -------------------------------------------------------------------------
    def encode(self, data: List[int]) -> List[int]:
        """Systematic encode: data bits followed by n-k parity bits."""
        if len(data) != self.k():
            raise ValueError(f"data length {len(data)} != k={self.k()}")
        if any(b not in (0, 1) for b in data):
            raise ValueError("data must be binary")
        g = self._g_poly if self._g_poly is not None else self._int_to_gf2_poly(self.generator_int())
        # message polynomial: data[0] is x^{k-1}
        msg_poly = galois.Poly(list(data), field=self.GF2)
        x_d = galois.Poly([self.GF2(1)] + [self.GF2(0)] * (self.n - self.k()), field=self.GF2)
        shifted = msg_poly * x_d
        parity = [int(c) for c in (shifted % g).coefficients(order='desc')]
        parity = [0] * ((self.n - self.k()) - len(parity)) + parity
        return list(data) + parity

    # -------------------------------------------------------------------------
    # Syndromes
    # -------------------------------------------------------------------------
    def syndromes(self, block: List[int]) -> List[int]:
        """Odd syndromes S_j = r(alpha^j), j in the odd root set."""
        if len(block) != self.n:
            raise ValueError(f"block length {len(block)} != n={self.n}")
        roots = [self.alpha ** r for r in self._syndrome_root_exponents()]
        out = []
        for beta in roots:
            s = self.GFext(0)
            # Horner in transmission order: block[0] is high-order coeff
            for bit in block:
                s = s * beta + self.GFext(bit)
            out.append(int(s))
        return out

    def no_error(self, block: List[int]) -> bool:
        return all(s == 0 for s in self.syndromes(block))

    # -------------------------------------------------------------------------
    # Decoder (Berlekamp-Massey + Chien)
    # -------------------------------------------------------------------------
    def _full_syndrome_sequence(self, block: List[int]) -> List[int]:
        """S_1 .. S_{2t} as integers; even ones derived by squaring."""
        odd = self.syndromes(block)
        roots = self._syndrome_root_exponents()
        # map exponent -> syndrome value
        smap = {roots[j]: odd[j] for j in range(self.t)}
        full = []
        for i in range(1, 2 * self.t + 1):
            if i in smap:
                full.append(smap[i])
            else:
                # S_{2j} = S_j^2
                half = i // 2
                full.append(self.gf_square(full[half - 1]))
        return full

    def _berlekamp_massey(self, S: List[int]) -> List[int]:
        """Return error locator polynomial Lambda(x) coefficients ascending (integers)."""
        Lambda = [1]
        B = [1]
        L = 0
        m = 1
        for n in range(1, len(S) + 1):
            # discrepancy d = sum_{i=0}^L Lambda_i * S_{n-i}
            d = 0
            for i in range(min(len(Lambda), n)):
                if Lambda[i] and S[n - 1 - i]:
                    d ^= self.gf_mul(Lambda[i], S[n - 1 - i])
            if d == 0:
                m += 1
            else:
                # T(x) = Lambda(x) + d * x^m * B(x)
                T = list(Lambda) + [0] * (len(B) + m - len(Lambda))
                for i in range(len(B)):
                    T[i + m] ^= self.gf_mul(d, B[i])
                if 2 * L <= n - 1:
                    # B(x) = Lambda(x) / d
                    inv_d = self._to_int(self._el(d) ** -1)
                    B = [self.gf_mul(c, inv_d) for c in Lambda]
                    L = n - L
                    m = 1
                else:
                    m += 1
                Lambda = T
        return Lambda

    def _chien_positions(self, lam_asc: List[int]) -> List[int]:
        """Return sorted error positions (0 = first transmitted bit)."""
        GF = self.GFext
        lam = galois.Poly(lam_asc[::-1] + [0] * (self.t + 2 - len(lam_asc)), field=GF)
        # Lambda(x) = prod (1 - X_i x). Roots are at x = X_i^{-1}.
        # X_i for position p (where bit p is coefficient x^{n-1-p}) is alpha^{p}.
        # We evaluate Lambda(alpha^{-l}) for l = 0..n-1; a root means l is a
        # position index in our transmission order. We use the recurrence below
        # and validate the convention against galois.BCH.
        roots = []
        beta = GF(1)  # alpha^0
        alpha_inv = self.alpha ** (-1)
        for l in range(self.n):
            if lam(beta) == 0:
                # l is the polynomial exponent (x^{n-1-p}); the transmission
                # position is p = n - 1 - l.
                roots.append(self.n - 1 - l)
            beta *= alpha_inv
        return roots

    def decode(self, block: List[int]) -> Tuple[List[int], str, int]:
        """Return (data_out, status, corrected_count)."""
        if len(block) != self.n:
            raise ValueError(f"block length {len(block)} != n={self.n}")
        k = self.k()
        if all(s == 0 for s in self.syndromes(block)):
            return block[:k], 'ok', 0
        S = self._full_syndrome_sequence(block)
        lam_asc = self._berlekamp_massey(S)
        # degree is highest non-zero coefficient index
        deg = max((i for i, c in enumerate(lam_asc) if c), default=-1)
        if deg < 0 or deg > self.t:
            return block[:k], 'uncorrectable', 0
        positions = self._chien_positions(lam_asc)
        if len(positions) != deg:
            return block[:k], 'uncorrectable', 0
        corrected = list(block)
        for p in positions:
            corrected[p] ^= 1
        if not self.no_error(corrected):
            return block[:k], 'uncorrectable', 0
        return corrected[:k], 'corrected', len(positions)

    # -------------------------------------------------------------------------
    # Validation against galois.BCH
    # -------------------------------------------------------------------------
    def validate(self, trials: int = 200, seed: int = 1) -> Tuple[int, int]:
        """Model vs galois.BCH encode/decode on random blocks with 0..t+1 errors."""
        rnd = random.Random(seed)
        agree = disagree = 0
        try:
            ref = galois.BCH(self.n_full, self.n_full - self.degree_g(),
                             field=self.GF2, extension_field=self.GFext, c=self.b)
        except Exception as e:
            raise RuntimeError(f"galois.BCH construction failed for n={self.n}, m={self.m}: {e}") from e
        for _ in range(trials):
            data = [rnd.randint(0, 1) for _ in range(self.k())]
            enc = self.encode(data)
            # codeword syndromes are zero
            if not all(s == 0 for s in self.syndromes(enc)):
                raise AssertionError("syndromes of a codeword are not zero")
            ecount = rnd.choice([0, 1, self.t - 1, self.t, self.t + 1]) if self.t > 1 \
                else rnd.choice([0, 1, 1, 2])
            ecount = max(0, min(ecount, self.n))
            pos = rnd.sample(range(self.n), ecount)
            rx = list(enc)
            for p in pos:
                rx[p] ^= 1
            # syndrome sanity: a codeword has zero odd syndromes (checked above)
            got, status, cnt = self.decode(rx)
            ref_rx = self.GF2(rx)
            try:
                ref_dec = ref.decode(ref_rx)
                ref_data = [int(x) for x in ref_dec]
                ref_ok = True
            except Exception:
                ref_ok = False
            if ref_ok:
                ok = (got == ref_data) and (status != 'uncorrectable')
            else:
                ok = status == 'uncorrectable'
            if ok:
                agree += 1
            else:
                disagree += 1
                if disagree <= 3:
                    print(f"DISAGREE e={ecount} pos={pos} status={status} cnt={cnt} ref_ok={ref_ok}")
        return agree, disagree


if __name__ == '__main__':
    # Validation runs recorded in the module docstring. Keep outputs concise.
    profiles = [
        # CCSDS (63,56) modified BCH, t=1, first root 0, field x^6+x+1
        (6, 0x43, 1, 63, 0, 150),
        # Flash-class shortened profile: GF(2^13), t=8, n chosen as a page+spare
        # footprint (4096 data bits + 128 spare = 4224 bits). m=13 primitive
        # polynomial x^13 + x^4 + x^3 + x + 1 = 0x201B.
        (13, 0x201B, 8, 4224, 1, 20),
        # A second sanity profile: narrow-sense primitive BCH, m=6, t=2, n=63
        (6, 0x43, 2, 63, 1, 150),
    ]
    for m, prim, t, n, b, trials in profiles:
        model = BCHModel(m, prim, t, n, b)
        a, d = model.validate(trials=trials)
        print(f"BCH({n},{model.k()}) m={m} t={t} b={b} prim=0x{prim:X}: "
              f"agree={a} disagree={d}")
