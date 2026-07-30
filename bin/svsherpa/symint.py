# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.symint
# Purpose: Symbolic integer algebra for widths, bounds and ranges
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Symbolic integers.

Widths in real RTL are rarely plain numbers -- they are ``WIDTH-1``,
``$clog2(DEPTH)+1``, ``2*N-1``, ``CHANNELS*WIDTH``. To check widths at build
time without forcing every parameter to be concrete, widths are carried as
small symbolic expressions rather than ints.

The design goal is narrow: enough algebra to decide *"are these two widths the
same expression?"* and to render legal SV text. Sums and products are flattened
and normalised, so ``(WIDTH-1)+1`` compares equal to ``WIDTH``. Anything more
exotic (division, ``$clog2``) is treated as an opaque atom -- structurally
comparable, but not simplified.

    >>> W = SymInt.ref("WIDTH")
    >>> str(W - 1)
    'WIDTH-1'
    >>> (W - 1) + 1 == W
    True
    >>> SymInt.clog2(8).try_eval({})
    3
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Mapping

from .errors import SvError

# Precedence levels mirroring SystemVerilog, used to render with the fewest
# parentheses that still parse the way we mean.
_PREC_ATOM = 100
_PREC_MUL = 30
_PREC_ADD = 20

IntLike = "SymInt | int"


def _as_sym(value: IntLike) -> "SymInt":
    if isinstance(value, SymInt):
        return value
    if isinstance(value, bool):  # bool is an int subclass; reject it explicitly
        raise SvError(f"cannot use bool {value!r} as a width")
    if isinstance(value, int):
        return SymInt.lit(value)
    raise SvError(f"cannot use {value!r} of type {type(value).__name__} as a width")


@dataclass(frozen=True)
class SymInt:
    """An immutable symbolic non-negative integer.

    Internally a sum of terms plus a constant::

        const + sum(coeff * product(atoms))

    ``atoms`` are opaque strings (parameter names) or nested ``SymInt`` wrapped
    in a function application such as ``$clog2(...)``.
    """

    const: int = 0
    # Maps a canonical product-of-atoms key to its integer coefficient.
    terms: tuple[tuple[tuple[str, ...], int], ...] = field(default=())

    # ---------------------------------------------------------------- builders
    @staticmethod
    def lit(value: int) -> "SymInt":
        return SymInt(const=int(value))

    @staticmethod
    def ref(name: str) -> "SymInt":
        return SymInt(const=0, terms=(((name,), 1),))

    @staticmethod
    def clog2(value: IntLike) -> "SymInt":
        """``$clog2(value)`` -- folded when *value* is a known constant."""
        sym = _as_sym(value)
        known = sym.try_eval({})
        if known is not None:
            return SymInt.lit(max(0, math.ceil(math.log2(known)) if known > 1 else 0))
        return SymInt(const=0, terms=(((f"$clog2({sym.render()})",), 1),))

    @staticmethod
    def opaque(text: str) -> "SymInt":
        """An arbitrary SV integer expression treated as a single atom."""
        return SymInt(const=0, terms=(((text,), 1),))

    # ------------------------------------------------------------- arithmetic
    def _combine(self, other: "SymInt", sign: int) -> "SymInt":
        acc: dict[tuple[str, ...], int] = dict(self.terms)
        for key, coeff in other.terms:
            acc[key] = acc.get(key, 0) + sign * coeff
        return SymInt(
            const=self.const + sign * other.const,
            terms=_norm_terms(acc),
        )

    def __add__(self, other: IntLike) -> "SymInt":
        return self._combine(_as_sym(other), 1)

    __radd__ = __add__

    def __sub__(self, other: IntLike) -> "SymInt":
        return self._combine(_as_sym(other), -1)

    def __rsub__(self, other: IntLike) -> "SymInt":
        return _as_sym(other)._combine(self, -1)

    def __mul__(self, other: IntLike) -> "SymInt":
        rhs = _as_sym(other)
        # (c1 + T1) * (c2 + T2) expanded termwise; c1*c2 folds into `const`.
        acc: dict[tuple[str, ...], int] = {}
        for key, coeff in self.terms:
            if rhs.const:
                acc[key] = acc.get(key, 0) + coeff * rhs.const
        for key, coeff in rhs.terms:
            if self.const:
                acc[key] = acc.get(key, 0) + coeff * self.const
        for lkey, lc in self.terms:
            for rkey, rc in rhs.terms:
                key = tuple(sorted(lkey + rkey))
                acc[key] = acc.get(key, 0) + lc * rc
        return SymInt(const=self.const * rhs.const, terms=_norm_terms(acc))

    __rmul__ = __mul__

    def __neg__(self) -> "SymInt":
        return SymInt.lit(0) - self

    # ------------------------------------------------------------- evaluation
    def try_eval(self, env: Mapping[str, int] | None = None) -> int | None:
        """Resolve to an ``int`` when every atom is known, else ``None``."""
        env = env or {}
        total = self.const
        for key, coeff in self.terms:
            product = coeff
            for atom in key:
                if atom in env:
                    product *= env[atom]
                else:
                    return None
            total += product
        return total

    def is_const(self) -> bool:
        return not self.terms

    # -------------------------------------------------------------- rendering
    def render(self, prec: int = 0) -> str:
        """Emit SV text, parenthesised only when *prec* demands it."""
        parts: list[str] = []
        for key, coeff in self.terms:
            atoms = "*".join(key)
            if coeff == 1:
                parts.append(atoms)
            elif coeff == -1:
                parts.append(f"-{atoms}")
            else:
                parts.append(f"{coeff}*{atoms}")
        if self.const or not parts:
            parts.append(str(self.const))

        # Join with '+', folding leading '-' into '-' rather than '+-'.
        text = parts[0]
        for part in parts[1:]:
            text += part if part.startswith("-") else f"+{part}"

        own = _PREC_ATOM if len(parts) == 1 and not text.startswith("-") else _PREC_ADD
        return f"({text})" if prec > own else text

    def __str__(self) -> str:
        return self.render()

    def __repr__(self) -> str:
        return f"SymInt({self.render()!r})"


def _norm_terms(
    acc: Mapping[tuple[str, ...], int],
) -> tuple[tuple[tuple[str, ...], int], ...]:
    """Drop zero coefficients and sort so equal expressions compare equal."""
    return tuple(sorted((k, v) for k, v in acc.items() if v != 0))


def clog2(value: IntLike) -> SymInt:
    """``$clog2(value)`` as a width expression."""
    return SymInt.clog2(value)


def width_of(value: IntLike) -> SymInt:
    """Coerce *value* to a :class:`SymInt` width."""
    return _as_sym(value)


def widths_conflict(lhs: SymInt, rhs: SymInt, env: Mapping[str, int]) -> bool:
    """True when *lhs* and *rhs* are provably different widths.

    Symbolic widths that are not structurally identical are *not* reported as
    conflicts -- ``WIDTH`` and ``DATA_WIDTH`` may well be equal at elaboration.
    Only mismatches we can prove are flagged, which keeps false positives out
    of the way of real work.
    """
    if lhs == rhs:
        return False
    left, right = lhs.try_eval(env), rhs.try_eval(env)
    if left is None or right is None:
        return False
    return left != right
