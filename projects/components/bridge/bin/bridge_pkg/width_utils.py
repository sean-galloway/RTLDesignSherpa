#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
"""
Shared width/connectivity helpers for the bridge generators.

Single source of truth for the master<->slave width and connectivity
queries that AdapterGenerator, CrossbarGenerator, and
BridgeModuleGenerator previously each carried a private copy of. All
three generators MUST agree on these answers — see the bug history in
get_connected_slave_widths() for what happens when they don't.

The functions are pure: they take the master/slave config objects and
return plain values, no generator state involved. `master` needs
`.slave_connections` (indices into `slaves`) and `slaves` entries need
`.data_width`; get_masters_connecting_to_slave additionally relies on
list identity via `slaves.index(slave)`.
"""

from typing import List


def get_connected_slave_widths(master, slaves) -> List[int]:
    """
    Get sorted list of unique ADAPTER OUTPUT widths for slaves this master connects to.

    Always uses the slave's data_width — the bridge has one width
    parameter per slave, regardless of protocol. The adapter handles
    any width conversion locally for that slave; the crossbar only
    sees the slave's data_width on the wire.

    Bug history: earlier versions used a "LCD width" for APB slaves
    (min of master widths connecting to the same APB), which left the
    generators disagreeing on the suffix to use — the adapter emitted
    cpu_master_64b_*, the crossbar referenced cpu_master_32b_*, and the
    bridge top instantiated the xbar with widths that don't exist as
    ports. Dropping the LCD path means every generator reads
    slave.data_width and gets the same answer.

    Args:
        master: MasterConfig whose slave_connections index into `slaves`
        slaves: Full list of SlaveInfo objects for the bridge

    Returns:
        Sorted list of unique slave data widths (bits)
    """
    widths = set()
    for idx in master.slave_connections:
        widths.add(slaves[idx].data_width)
    return sorted(list(widths))


def get_masters_connecting_to_slave(slave, masters, slaves) -> list:
    """
    Get list of masters that connect to a specific slave.

    Args:
        slave: Slave to check connections for (must be an element of `slaves`)
        masters: Full list of MasterConfig objects for the bridge
        slaves: Full list of SlaveInfo objects for the bridge

    Returns:
        List of MasterConfig objects that have this slave in their connections
    """
    # Find slave index
    try:
        slave_idx = slaves.index(slave)
    except ValueError:
        return []

    # Find all masters that connect to this slave
    connecting_masters = []
    for master in masters:
        if slave_idx in master.slave_connections:
            connecting_masters.append(master)

    return connecting_masters
