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


# ---------------------------------------------------------------------------
# Transaction-ID widths (bridge TASK-005, was BRIDGE-016; ID remap). ONE place for the
# arithmetic: the package, the crossbar, the master and slave adapters, the
# TB generator and the validator all size IDs from these functions.
# ---------------------------------------------------------------------------

def master_id_width(masters) -> int:
    """Widest master-side ID, floored at 1 so an all-AXIL bridge (id_width 0)
    never declares a [-1:0] field."""
    return max([max(1, (m.id_width or 0)) for m in masters] or [4])


def id_prefix_width(masters) -> int:
    """Bits prepended to every ID inside the fabric: the issuing master's
    index, so two masters can never alias an ID at a slave. Zero for a single
    master (nothing to disambiguate, and single-master bridges stay
    byte-identical); $clog2(N) otherwise."""
    n = len(list(masters))
    return (n - 1).bit_length() if n > 1 else 0


def remap_slot_width(master) -> int:
    """Bits of a remap slot: $clog2(max_outstanding). A master has at most
    max_outstanding requests in flight per direction, so at most that many
    distinct IDs, and a slot this wide names each of them."""
    return max(1, int(getattr(master, 'max_outstanding', 16) or 16).bit_length() - 1)


def id_remapped(master) -> bool:
    """True when the master adapter remaps this master's IDs to slots
    (bridge_id_remap): whenever its ID is wider than a slot, so the fabric
    and every slave see the slot instead. id_remap = false on the port (or
    [bridge], or preset "xbar") turns it off: the ID passes through whole.

    A read-return atomic port (AXI5 'atomic' on an rw port) is the exception:
    its atomic AW answers on BOTH B and R under one AWID, which one table per
    direction cannot name; it keeps its own ID."""
    if not getattr(master, 'id_remap', True):
        return False
    if (master.id_width or 0) <= remap_slot_width(master):
        return False
    feats = (set(getattr(master, 'axi5_features', None) or ())
             if getattr(master, 'protocol', 'axi4') == 'axi5' else set())
    return not ('atomic' in feats and getattr(master, 'channels', '') == 'rw')


def fabric_local_id_width(masters) -> int:
    """Width of the master-local part of a fabric ID: a remapped master's
    slot, otherwise its own ID (floored at 1), widest over the bridge."""
    return max([remap_slot_width(m) if id_remapped(m) else max(1, m.id_width or 0)
                for m in masters] or [4])


def xbar_id_width(masters) -> int:
    """ID width inside the fabric and on every slave-side port:
    {master index, master-local ID}. The local part is a remap slot for a
    master whose ID is wider than one (fabric_local_id_width), so five 8-bit
    masters at max_outstanding 16 give 7-bit IDs at the slaves, not 11."""
    return fabric_local_id_width(masters) + id_prefix_width(masters)

