# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axi_stress_model
# Purpose: Python reference for the bus-stress blocks (rtl/amba/includes/
#          axi_stress_pkg.sv): the data function, beat addresses, burst
#          legality, error names, and packers for the cfg/status structs.
# Subsystem: framework
#
# Written from the AXI4 spec and the package's stated contract, not by
# transliterating the RTL loops, so a test that compares the two is
# comparing two readings of one contract.
"""Reference model of the axi_stress_* data contract.

Every byte is a function of its fabric address, the owning slave's tag and
the direction:  word(A) = f_word(A & ~3, seed, tag, dir),
byte(A) = (word(A) >> 8*(A % 4)) & 0xFF.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Tuple

M32 = 0xFFFF_FFFF

FIXED, INCR, WRAP = 0, 1, 2
OKAY, EXOKAY, SLVERR, DECERR = 0, 1, 2, 3

ERR_NAMES = {
    0: 'RD_STRAY', 1: 'RD_LAST', 2: 'RD_RESP', 3: 'RD_DATA',
    4: 'WR_STRAY', 5: 'WR_RESP', 6: 'WR_EARLY', 7: 'HANG',
    8: 'S_ADDR', 9: 'S_PROTO', 10: 'S_WDATA', 11: 'S_WSTRB', 12: 'S_WLAST',
    13: 'S_WID', 14: 'S_SB', 15: 'M_SB',
}
ERR_CODES = {v: k for k, v in ERR_NAMES.items()}


def err_list(mask: int) -> List[str]:
    """Names of the bits set in a 16-bit err_mask."""
    return [ERR_NAMES.get(b, f'bit{b}') for b in range(16) if (mask >> b) & 1]


# ---------------------------------------------------------------------------
# Data function
# ---------------------------------------------------------------------------

def xs32(v: int) -> int:
    """xorshift32 (13, 17, 5)."""
    v &= M32
    v ^= (v << 13) & M32
    v ^= v >> 17
    v ^= (v << 5) & M32
    return v


def f_word(addr: int, seed: int, tag: int, rd: bool) -> int:
    """The data word at the 4-byte-aligned word holding fabric address addr."""
    tag &= 0xFF
    k = (seed ^ ((tag << 24) | ((~tag & 0xFF) << 16) | (tag << 8) | (~tag & 0xFF))
         ^ (0x5A5A_A5A5 if rd else 0)) & M32
    rot = ((k << 16) | (k >> 16)) & M32
    return xs32(xs32((addr & ~3 & M32) ^ k) ^ rot)


# AXI5 sideband layout (axi_stress_pkg SB_M_* / RSB_M_*)
SB_M_NSAID, SB_M_TRACE, SB_M_MPAM, SB_M_MECID = 0x0000_000F, 0x10, 0x0000_FFE0, 0xFFFF_0000
RSB_M_TRACE = 0x01


def f_sb(addr: int, seed: int) -> int:
    """AXI5 sideband word of a request's start address."""
    return xs32(xs32((addr ^ seed ^ 0xC6A4_A793) & M32) ^ 0x5851_F42D)


def f_rsb(sb: int) -> int:
    """The response sideband echo of a request sideband word: TRACE."""
    return (sb >> 4) & 1


def f_poison(addr: int, seed: int, lg2: int) -> bool:
    """A beat at addr is poisoned 1 in 2**lg2 (never for lg2 = 0)."""
    return lg2 != 0 and (f_sb(addr ^ 0x9E37_79B9, seed) & ((1 << lg2) - 1)) == 0


def f_byte(addr: int, seed: int, tag: int, rd: bool) -> int:
    return (f_word(addr, seed, tag, rd) >> (8 * (addr & 3))) & 0xFF


def beat_data(addr: int, nbytes: int, seed: int, tag: int, rd: bool) -> int:
    """A full bus beat at the bus-aligned beat holding addr, every lane."""
    base = addr & ~(nbytes - 1)
    v = 0
    for lane in range(nbytes // 4):
        v |= f_word(base + 4 * lane, seed, tag, rd) << (32 * lane)
    return v


# ---------------------------------------------------------------------------
# Bursts (AXI4 A3.4.1)
# ---------------------------------------------------------------------------

def beat_addrs(addr: int, length: int, size: int, burst: int) -> List[int]:
    """Address of every beat: length = AxLEN + 1 beats."""
    nb = 1 << size
    if burst == FIXED:
        return [addr] * length
    aligned = addr & ~(nb - 1)
    if burst == WRAP:
        span = nb * length
        lower = addr & ~(span - 1)
        return [lower + ((addr - lower + i * nb) % span) for i in range(length)]
    return [addr] + [aligned + i * nb for i in range(1, length)]


def beat_lanes(addr: int, size: int, bus_bytes: int) -> List[int]:
    """Byte lanes a beat at addr of 2**size bytes occupies on the bus."""
    nb = 1 << size
    lo = addr % bus_bytes
    hi = (addr & ~(nb - 1)) % bus_bytes + nb - 1
    return list(range(lo, hi + 1))


def burst_illegal(addr: int, axlen: int, size: int, burst: int, bus_lg2: int) -> str:
    """'' if AXI4 allows the burst, else why not."""
    nb = 1 << size
    if size > bus_lg2:
        return 'size wider than the bus'
    if burst == 3:
        return 'reserved burst type'
    if burst != INCR and axlen > 15:
        return 'FIXED/WRAP longer than 16'
    if burst == WRAP and axlen not in (1, 3, 7, 15):
        return 'WRAP length not 2/4/8/16'
    if burst == WRAP and addr % nb:
        return 'WRAP start off the size grid'
    if burst == INCR and ((addr & ~(nb - 1)) & 0xFFF) + (axlen + 1) * nb > 0x1000:
        return 'INCR crosses 4 KB'
    return ''


# ---------------------------------------------------------------------------
# Packed structs: field lists in declaration order (first field = MSBs)
# ---------------------------------------------------------------------------

WIN_FIELDS = (('base', 32), ('size_lg2', 6), ('tag', 8), ('resp', 2),
              ('len_mask', 8), ('size_min', 3), ('size_max', 3),
              ('burst_mask', 3), ('unaligned', 1), ('strb_rand', 1),
              ('rd_en', 1), ('wr_en', 1), ('sb', 1), ('poison_lg2', 4))

MCFG_FIELDS = (('enable', 1), ('txn_count', 32), ('seed', 32), ('id_base', 16),
               ('id_mask', 16), ('gap_mask', 8), ('resp_throttle', 4),
               ('data_throttle', 4), ('max_out', 8), ('timeout_lg2', 5),
               ('qos_rand', 1))

MSTS_FIELDS = (('busy', 1), ('done', 1), ('runs', 8), ('issued', 32), ('completed', 32),
               ('beats', 32), ('err_mask', 16), ('err_cnt', 16), ('fe_valid', 1),
               ('fe_kind', 4), ('fe_id', 16), ('fe_addr', 32), ('fe_exp', 32),
               ('fe_act', 32), ('lat_max', 16), ('lat_sum', 32), ('out_now', 8),
               ('out_max', 8))

SCFG_FIELDS = (('base', 32), ('size_lg2', 6), ('offset_mode', 1), ('tag', 8),
               ('err_en', 1), ('err_base', 32), ('err_mask', 32), ('inorder', 1),
               ('interleave', 1), ('lat_min', 8), ('lat_mask', 8),
               ('req_throttle', 4), ('data_throttle', 4), ('max_out', 8),
               ('seed', 32), ('sb_src', 8), ('poison_lg2', 4))

SSTS_FIELDS = (('runs', 8), ('bursts', 32), ('beats', 32), ('err_mask', 16), ('err_cnt', 16),
               ('fe_valid', 1), ('fe_kind', 4), ('fe_id', 16), ('fe_addr', 32),
               ('fe_exp', 32), ('fe_act', 32), ('out_now', 8), ('out_max', 8))


def width(fields: Sequence[Tuple[str, int]]) -> int:
    return sum(w for _, w in fields)


def pack(fields: Sequence[Tuple[str, int]], values: Dict[str, int]) -> int:
    unknown = set(values) - {n for n, _ in fields}
    if unknown:
        raise KeyError(f'unknown struct fields: {sorted(unknown)}')
    v = 0
    for name, w in fields:
        f = values.get(name, 0)
        if f < 0 or f >> w:
            raise ValueError(f'{name}={f:#x} does not fit {w} bits')
        v = (v << w) | f
    return v


def unpack(fields: Sequence[Tuple[str, int]], v: int) -> Dict[str, int]:
    out = {}
    for name, w in reversed(fields):
        out[name] = v & ((1 << w) - 1)
        v >>= w
    return out


def pack_windows(wins: Iterable[Dict[str, int]], nwin: int) -> int:
    """Window 0 in the least significant bits, as tb_axi_stress_pair takes it."""
    wins = list(wins)
    if len(wins) > nwin:
        raise ValueError(f'{len(wins)} windows, {nwin} built')
    ww = width(WIN_FIELDS)
    v = 0
    for i, w in enumerate(wins):
        v |= pack(WIN_FIELDS, w) << (i * ww)
    return v


@dataclass
class Window:
    """A master target window, as the host and the TB both describe one."""
    base: int
    size_lg2: int
    tag: int
    resp: int = OKAY
    len_mask: int = 0xFF
    size_min: int = 0
    size_max: int = 7
    burst_mask: int = 0b111
    unaligned: int = 1
    strb_rand: int = 1
    rd_en: int = 1
    wr_en: int = 1
    sb: int = 0
    poison_lg2: int = 0

    def fields(self) -> Dict[str, int]:
        return dict(self.__dict__)
