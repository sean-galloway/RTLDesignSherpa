#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# AXI5 native-sideband spec shared by the package / adapter / crossbar /
# slave-adapter generators (BRIDGE-002 phase A5-2 slice 2).
#
# One table drives everything: which struct fields exist per channel,
# their widths, which feature enables them, and the axi5_* wrapper port
# base each field maps to. Field emission order is THIS table's order —
# every generator must iterate it the same way so struct layout, pack
# sites, xbar routing, and extraction all agree.
#
# Struct field naming: the AWUNIQUE/ARUNIQUE bit is named `uniq` because
# `unique` is a SystemVerilog keyword.
#
# Slice-2 policy (see vault BRIDGE-002 design note):
#   - Struct fields are the UNION of features on any AXI5 port. Bridges
#     with no AXI5 ports get no fields, so pure-AXI4 RTL stays
#     byte-identical (the zero-drift invariant).
#   - Master adapters populate their enabled fields ONLY on the direct
#     (width-matched) path arm; converter arms pack '0 — per-beat and
#     per-transaction sideband cannot traverse the dwidth-converter IP.
#   - The crossbar forwards fields unconditionally (non-qualifying
#     sources are already '0) and exposes discrete sideband signals only
#     for AXI5 slaves that enable the feature.
#   - Response-direction fields (b.trace / r.trace / r.poison) mux from
#     qualifying slaves, '0 otherwise; the master adapter extracts only
#     on its direct arm.

from typing import Iterable, List, Optional, Set, Tuple

# (channel, field, width, feature, wrapper_port_base)
#
# Width is an int, or one of the symbolic widths below that scale with the
# DATA width of the struct/port the field lives on (BRIDGE-018): MTE carries
# one 4-bit tag per 16 bytes of data and chunking one strobe bit per 128-bit
# chunk, so their widths are a function of the data bus. Resolve with
# field_width(width, data_width); channel_fields(..., dw=) does it for you.
WIDTH_TAGS = 'tags'            # AXI_TAG_WIDTH * NUM_TAGS   = 4 * max(1, dw/128)
WIDTH_NTAGS = 'ntags'          # NUM_TAGS                   = max(1, dw/128)
WIDTH_CHUNKSTRB = 'chunkstrb'  # CHUNK_STRB_WIDTH           = max(1, dw/128)
SIDEBAND_FIELDS: Tuple[Tuple[str, str, object, str, str], ...] = (
    ('aw', 'nsaid',     4,               'nsaid',    'awnsaid'),
    ('aw', 'trace',     1,               'trace',    'awtrace'),
    ('aw', 'mpam',      11,              'mpam',     'awmpam'),
    ('aw', 'mecid',     16,              'mecid',    'awmecid'),
    ('aw', 'uniq',      1,               'unique',   'awunique'),
    ('aw', 'atop',      6,               'atomic',   'awatop'),
    ('aw', 'tagop',     2,               'mte',      'awtagop'),
    ('aw', 'tag',       WIDTH_TAGS,      'mte',      'awtag'),
    ('w',  'poison',    1,               'poison',   'wpoison'),
    ('w',  'tag',       WIDTH_TAGS,      'mte',      'wtag'),
    ('w',  'tagupdate', WIDTH_NTAGS,     'mte',      'wtagupdate'),
    ('b',  'trace',     1,               'trace',    'btrace'),
    ('b',  'tag',       WIDTH_TAGS,      'mte',      'btag'),
    ('b',  'tagmatch',  1,               'mte',      'btagmatch'),
    ('ar', 'nsaid',     4,               'nsaid',    'arnsaid'),
    ('ar', 'trace',     1,               'trace',    'artrace'),
    ('ar', 'mpam',      11,              'mpam',     'armpam'),
    ('ar', 'mecid',     16,              'mecid',    'armecid'),
    ('ar', 'uniq',      1,               'unique',   'arunique'),
    ('ar', 'chunken',   1,               'chunking', 'archunken'),
    ('ar', 'tagop',     2,               'mte',      'artagop'),
    ('r',  'trace',     1,               'trace',    'rtrace'),
    ('r',  'poison',    1,               'poison',   'rpoison'),
    ('r',  'chunkv',    1,               'chunking', 'rchunkv'),
    ('r',  'chunknum',  4,               'chunking', 'rchunknum'),
    ('r',  'chunkstrb', WIDTH_CHUNKSTRB, 'chunking', 'rchunkstrb'),
    ('r',  'tag',       WIDTH_TAGS,      'mte',      'rtag'),
    ('r',  'tagmatch',  1,               'mte',      'rtagmatch'),
)

# The data width a feature needs: tags are per 16 bytes and chunks are
# 128 bits, so neither means anything on a narrower bus (the AXI5 checker
# in the DV framework rejects chunking below 128 as well).
WIDE_FEATURE_MIN_DW = {'mte': 128, 'chunking': 128}


def n_tags(dw: int) -> int:
    """Tags (or 128-bit chunks) per beat on a `dw`-bit data bus."""
    return max(1, dw // 128)


def field_width(width, dw: int) -> int:
    """Resolve a table width (int or symbolic) for a `dw`-bit data bus."""
    if isinstance(width, int):
        return width
    if width == WIDTH_TAGS:
        return 4 * n_tags(dw)
    if width in (WIDTH_NTAGS, WIDTH_CHUNKSTRB):
        return n_tags(dw)
    raise ValueError(f"unknown sideband width spec {width!r}")


def fit_expr(src: str, src_w: int, dst_w: int) -> str:
    """`src` (src_w bits) as a dst_w-bit expression: as-is, zero-extended
    or sliced. Widths are decided in Python so the emitted RTL carries
    explicit widths and no casts (BRIDGE-018: the width-independent aw/ar/b
    structs size their tag fields for the widest port, so a narrower MTE
    port packs and extracts through this)."""
    if src_w == dst_w:
        return src
    if dst_w > src_w:
        return f"{{{{{dst_w - src_w}{{1'b0}}}}, {src}}}"
    return f"{src}[{dst_w - 1}:0]"


# Features whose sideband can ride the fabric structs. `poison` (A5-2
# slice 2), `atomic` (A5-3a/b) and `mte` (BRIDGE-018) are legal ONLY under
# the validator's connectivity rule (every connected path direct +
# feature-enabled both ends): dropping any of them silently changes what
# a transaction means. `chunking` (BRIDGE-018) is droppable like trace --
# ARCHUNKEN is permission, not demand, so a chunking master reaching a
# slave that cannot chunk simply gets ordered data with RCHUNKV low.
NATIVE_SIDEBAND_FEATURES = ('nsaid', 'trace', 'mpam', 'mecid', 'unique',
                            'poison', 'atomic', 'mte', 'chunking')

# Response-direction channels (slave -> master).
RESP_CHANNELS = ('b', 'r')


def port_features(port) -> Set[str]:
    """The AXI5 feature set of a port object (MasterConfig / SlaveInfo /
    PortSpec); empty unless protocol == 'axi5'."""
    if getattr(port, 'protocol', 'axi4') != 'axi5':
        return set()
    return set(getattr(port, 'axi5_features', None) or ())


def sideband_union(masters: Iterable, slaves: Iterable) -> Set[str]:
    """Union of native-sideband features across every AXI5 port of the
    bridge. Drives struct-field emission."""
    feats: Set[str] = set()
    for p in list(masters) + list(slaves):
        feats |= port_features(p)
    return feats & set(NATIVE_SIDEBAND_FEATURES)


def channel_fields(features: Optional[Iterable[str]],
                   channel: str,
                   dw: Optional[int] = None) -> List[Tuple[str, object, str, str]]:
    """(field, width, feature, wrapper_base) tuples for `channel`, in
    canonical order, restricted to `features`. With `dw` the widths are
    resolved to ints for a `dw`-bit data bus; without it a symbolic width
    comes back as-is (callers that only need names pass no dw)."""
    feats = set(features or ())
    out = []
    for ch, f, w, feat, base in SIDEBAND_FIELDS:
        if ch == channel and feat in feats:
            out.append((f, field_width(w, dw) if dw is not None else w, feat, base))
    return out


def struct_dw(channel: str, path_dw: int, bridge_max_dw: int) -> int:
    """The data width a channel STRUCT is sized for. w/r structs exist per
    data width (the path's); aw/ar/b are width-independent, so their
    data-scaled fields are sized for the widest port in the bridge."""
    return path_dw if channel in ('w', 'r') else bridge_max_dw


def slave_qualifies(master, slave, feature: str) -> bool:
    """True when `feature` passes natively end-to-end on the
    master->slave path: both ends AXI5 with the feature enabled and the
    path is direct (width-matched — no dwidth converter)."""
    return (feature in port_features(master)
            and feature in port_features(slave)
            and master.data_width == slave.data_width)
