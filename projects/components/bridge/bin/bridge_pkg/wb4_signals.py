#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Wishbone B4 port surface, shared by the bridge top, the master adapter, the
# slave adapter and the slave-adapter instance component (BRIDGE-019).
#
# One table, one order, everywhere -- the discipline axil5_sideband.py set.
# A Wishbone port on the bridge is either the REQUESTER side (a slave port:
# the bridge drives CYC/STB/... toward an external completer) or the
# COMPLETER side (a master port: an external requester drives them into the
# bridge). The table records which side drives each signal; the two helpers
# below turn that into port directions for either kind of port.
#
# Widths: 'addr' = the port's address width, 'data' = its data width,
# 'sel' = data/8, 'cti' / 'bte' = the wb4_pkg burst-hint widths (carried,
# not acted on -- B4 chapter 4 calls them advisory), '1' = a single bit.
# Naming follows rtl/amba/wb4 and the RDS-DV WB4 BFMs: uppercase B4 names
# after the port prefix, DAT_W / DAT_R for the two data buses.

from typing import List, Tuple

# (base, width_key, requester_drives)
WB4_FIELDS: Tuple[Tuple[str, str, bool], ...] = (
    ('CYC',   '1',    True),
    ('STB',   '1',    True),
    ('WE',    '1',    True),
    ('ADR',   'addr', True),
    ('DAT_W', 'data', True),
    ('SEL',   'sel',  True),
    ('CTI',   'cti',  True),
    ('BTE',   'bte',  True),
    ('STALL', '1',    False),
    ('ACK',   '1',    False),
    ('ERR',   '1',    False),
    ('RTY',   '1',    False),
    ('DAT_R', 'data', False),
)

WB4_CTI_WIDTH = 3
WB4_BTE_WIDTH = 2


def field_width(width_key: str, addr_width: int, data_width: int) -> int:
    return {
        '1': 1,
        'addr': addr_width,
        'data': data_width,
        'sel': data_width // 8,
        'cti': WB4_CTI_WIDTH,
        'bte': WB4_BTE_WIDTH,
    }[width_key]


def wb4_ports(side: str, addr_width: int, data_width: int) -> List[Tuple[str, str, int]]:
    """(base, 'input'|'output', width) for a bridge port of the given side.

    side='requester': the bridge is the Wishbone requester (a SLAVE port);
                      requester-driven signals are outputs.
    side='completer': the bridge is the Wishbone completer (a MASTER port);
                      requester-driven signals are inputs.
    """
    if side not in ('requester', 'completer'):
        raise ValueError(f"side must be 'requester' or 'completer', got {side!r}")
    out: List[Tuple[str, str, int]] = []
    for base, width_key, requester_drives in WB4_FIELDS:
        bridge_drives = requester_drives if side == 'requester' else not requester_drives
        out.append((base, 'output' if bridge_drives else 'input',
                    field_width(width_key, addr_width, data_width)))
    return out


def wb4_names() -> List[str]:
    """Signal bases in table order."""
    return [base for base, _w, _d in WB4_FIELDS]


def port_decl_lines(prefix: str, side: str, addr_width: int, data_width: int,
                    indent: str = "    ") -> List[str]:
    """`input  logic [W-1:0] {prefix}{BASE},` lines, every one with a trailing
    comma (callers trim the last one as their port list requires)."""
    lines = []
    for base, direction, width in wb4_ports(side, addr_width, data_width):
        kind = "input  logic" if direction == 'input' else "output logic"
        span = "" if width == 1 else f"[{width-1}:0] "
        lines.append(f"{indent}{kind} {span}{prefix}{base},")
    return lines
