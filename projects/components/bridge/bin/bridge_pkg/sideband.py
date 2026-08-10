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
SIDEBAND_FIELDS: Tuple[Tuple[str, str, int, str, str], ...] = (
    ('aw', 'nsaid',  4,  'nsaid',  'awnsaid'),
    ('aw', 'trace',  1,  'trace',  'awtrace'),
    ('aw', 'mpam',   11, 'mpam',   'awmpam'),
    ('aw', 'mecid',  16, 'mecid',  'awmecid'),
    ('aw', 'uniq',   1,  'unique', 'awunique'),
    ('aw', 'atop',   6,  'atomic', 'awatop'),
    ('w',  'poison', 1,  'poison', 'wpoison'),
    ('b',  'trace',  1,  'trace',  'btrace'),
    ('ar', 'nsaid',  4,  'nsaid',  'arnsaid'),
    ('ar', 'trace',  1,  'trace',  'artrace'),
    ('ar', 'mpam',   11, 'mpam',   'armpam'),
    ('ar', 'mecid',  16, 'mecid',  'armecid'),
    ('ar', 'uniq',   1,  'unique', 'arunique'),
    ('r',  'trace',  1,  'trace',  'rtrace'),
    ('r',  'poison', 1,  'poison', 'rpoison'),
)

# Features whose sideband can ride the fabric structs. `poison` (A5-2
# slice 2) and `atomic` (A5-3a, store-class only -- the boundary's
# axi5_atomic_filter DECERRs read-return classes) are legal ONLY under
# the validator's connectivity rule (every connected path direct +
# feature-enabled both ends). mte / chunking remain rejected.
NATIVE_SIDEBAND_FEATURES = ('nsaid', 'trace', 'mpam', 'mecid', 'unique',
                            'poison', 'atomic')

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
                   channel: str) -> List[Tuple[str, int, str, str]]:
    """(field, width, feature, wrapper_base) tuples for `channel`, in
    canonical order, restricted to `features`."""
    feats = set(features or ())
    return [(f, w, feat, base)
            for ch, f, w, feat, base in SIDEBAND_FIELDS
            if ch == channel and feat in feats]


def slave_qualifies(master, slave, feature: str) -> bool:
    """True when `feature` passes natively end-to-end on the
    master->slave path: both ends AXI5 with the feature enabled and the
    path is direct (width-matched — no dwidth converter)."""
    return (feature in port_features(master)
            and feature in port_features(slave)
            and master.data_width == slave.data_width)
