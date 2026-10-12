#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# AXI5-Lite sideband spec, shared by the slave-adapter generator, the shim
# component and the bridge top's port emission.
#
# One table, iterated in one order, everywhere -- the same discipline
# sideband.py applies to AXI5-full. When the port list, the adapter's port
# declarations and the bridge top's connection list are each written by hand,
# they drift, and the drift shows up as a PINMISSING nobody reads.
#
# Scope note: this is the sideband of an AXI5-Lite port on an AXI4 fabric.
# What the bridge can actually source for it is limited by what crossed the
# fabric, and that is decided in axi4_to_axil5_{rd,wr}, not here: the ID and
# USER are forwarded from the AXI4 side, TRACE and POISON have no AXI4 origin
# and the converter ties them to zero. This table's job is only to say which
# ports exist, how wide, and which way they point.
#
# Signal set: IHI 0022L B2.1.5 / Table B2.2 (GitHub #102 item 3). AxLOCK,
# AxMPAM, AxMECID, AxNSAID and xLOOP are NOT present on AXI5-Lite and
# exclusive access is not supported, so none of them is here. AWID/BID and
# ARID/RID ARE required (on a Subordinate), so they are.
#
# Every field is exposed on the bridge boundary whether or not its feature is
# enabled -- a disabled group reads 0 rather than vanishing. That is
# deliberate: an AXI5-Lite port whose surface changes shape with a config
# knob cannot be connected to a fixed external slave, and the top-level
# interface is meant to stay connectable.

from typing import List, Tuple

# (channel, port_base, width_key, direction)
#   width_key  '1'        single bit
#              'id'       the port's ID width (slave port: the fabric ID
#                         width; master port: the master's id_width)
#              'user'     USER_WIDTH
#              'poison'   one bit per 64 data bits
#   direction  'out' driven by the bridge toward the external slave
#              'in'  driven by the external slave toward the bridge
AXIL5_SIDEBAND_FIELDS: Tuple[Tuple[str, str, str, str], ...] = (
    ('aw', 'awid',    'id',     'out'),
    ('aw', 'awuser',  'user',   'out'),
    ('aw', 'awtrace', '1',      'out'),
    ('w',  'wuser',   'user',   'out'),
    ('w',  'wpoison', 'poison', 'out'),
    ('b',  'bid',     'id',     'in'),
    ('b',  'buser',   'user',   'in'),
    ('b',  'btrace',  '1',      'in'),
    ('ar', 'arid',    'id',     'out'),
    ('ar', 'aruser',  'user',   'out'),
    ('ar', 'artrace', '1',      'out'),
    ('r',  'rid',     'id',     'in'),
    ('r',  'ruser',   'user',   'in'),
    ('r',  'rtrace',  '1',      'in'),
    ('r',  'rpoison', 'poison', 'in'),
)

# The ID fields. On a MASTER port they are not sideband to terminate: they
# reach the adapter's AXI4 face (awid/arid in, bid/rid out).
ID_BASES = ('awid', 'bid', 'arid', 'rid')

WRITE_CHANNELS = ('aw', 'w', 'b')
READ_CHANNELS = ('ar', 'r')

# USER matches the fabric's AXI4 USER width -- USER is the only optional
# group with an AXI4 source, so widening it would pad zeros. It lives here so
# the adapter, the shim and the bridge top cannot disagree about how wide a
# port is.
AXIL5_USER_WIDTH = 1

# ENABLE_* parameter name per axi5_features entry. The feature vocabulary is
# shared with AXI5-full (sideband.py) so one port config reads the same on
# either protocol.
#
# One entry, and that is not an omission. axi4_to_axil5_{rd,wr} gate only
# USER because only it has an AXI4 source to gate; TRACE and POISON are tied
# to zero unconditionally, so the converter deliberately has no ENABLE_ for
# them. Naming one here would generate an override for a parameter that does
# not exist and fail elaboration. (ENABLE_LOCK went with AxLOCK, #102 item 3.)
FEATURE_TO_ENABLE = {
    'user': 'ENABLE_USER',
}


def poison_width(data_width: int) -> int:
    """One poison bit per 64 data bits, never zero."""
    return max(data_width // 64, 1)


def field_width(width_key: str, data_width: int, user_width: int,
                id_width: int) -> int:
    """Resolve a table width_key to a bit count."""
    return {
        '1': 1,
        'id': id_width,
        'user': user_width,
        'poison': poison_width(data_width),
    }[width_key]


def sideband_ports(channels: str) -> List[Tuple[str, str, str]]:
    """(port_base, width_key, direction) for the channels this port carries.

    `channels` is the port's 'rw' / 'rd' / 'wr' spec.
    """
    wanted = set()
    if channels in ('rw', 'wr'):
        wanted |= set(WRITE_CHANNELS)
    if channels in ('rw', 'rd'):
        wanted |= set(READ_CHANNELS)
    return [(base, width_key, direction)
            for channel, base, width_key, direction in AXIL5_SIDEBAND_FIELDS
            if channel in wanted]


def enable_params(features) -> List[Tuple[str, int]]:
    """(ENABLE_*, 0|1) for every group, in a stable order.

    Every group is named explicitly rather than only the enabled ones: an
    omitted ENABLE_* falls back to the module default, and a generator that
    relies on a default is one default change away from silently enabling a
    group nobody asked for.
    """
    enabled = set(features or ())
    return [(param, 1 if feature in enabled else 0)
            for feature, param in sorted(FEATURE_TO_ENABLE.items(),
                                         key=lambda kv: kv[1])]
