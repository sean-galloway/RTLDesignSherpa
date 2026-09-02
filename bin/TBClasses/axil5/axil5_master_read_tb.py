# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL5MasterReadTB
# Purpose: Drive the AXI4-Lite read master RTL with AXI5-Lite BFMs
#
# Subsystem: framework

"""AXI5-Lite master-read testbench.

This is :class:`AXIL4MasterReadTB` with the component factories swapped for
their AXI5-Lite equivalents. Nothing else changes, and that is the whole point
of the test: with no optional signal groups enabled an AXI5-Lite interface is
an AXI4-Lite interface, so AXIL5 BFMs must drive the existing
``axil4_master_rd`` RTL and pass the identical traffic, checks and randomizer
sweeps that the AXIL4 BFMs do.

Why this exists at all: ``tests/unit/test_axil5_extends_axil4.py`` in the
framework repo proves the two declare the same FIELDS, but every one of those
checks is static -- it compares field configs and class structure without ever
constructing a component or moving a beat. A BFM that resolves no signals, or
that dies in ``__init__``, would pass all of them. This testbench is the part
that cannot be faked: real RTL, real signal resolution, real read transactions
with data checked against the memory model.

Optional-group coverage stops here, but the reason has changed and the
sentence that used to be here is no longer true. It said no AXI5-Lite DUT
existed in this repo, which was correct when written; `rtl/amba/axil5/` now
holds the full sixteen-module family, every one carrying USER, TRACE, LOOP,
MPAM, MECID, NSAID, POISON and LOCK behind its own ENABLE_* parameter.

So a real optional-group test is now possible and simply has not been written.
This testbench still proves only the shared path -- construction, binding,
transactions -- which is where a subclassing mistake would land. Exercising
the optional groups against axil5_* RTL is separate work; until it exists, a
BFM-only test of them would still assert against the BFM's own beliefs.
"""

from CocoTBFramework.components.axil5.axil5_factories import (
    create_axil5_master_rd,
    create_axil5_slave_rd,
)

from TBClasses.axil4.axil4_master_read_tb import AXIL4MasterReadTB


class AXIL5MasterReadTB(AXIL4MasterReadTB):
    """AXI4-Lite read-master RTL driven by AXI5-Lite BFMs.

    Inherits every phase, check and randomizer configuration from the AXIL4
    testbench. Only the factories differ, so a change to the AXI4-Lite flow
    reaches the AXI5-Lite one automatically instead of needing to be
    remembered twice.
    """

    MASTER_RD_FACTORY = staticmethod(create_axil5_master_rd)
    SLAVE_RD_FACTORY = staticmethod(create_axil5_slave_rd)
    # No optional groups: the DUT is AXI4-Lite RTL and has no ports for them.
    # This empty dict IS the assertion that AXIL5 defaults to the AXI4-Lite
    # signal set -- enabling a group here would make the DUT fail to bind.
    COMPONENT_KWARGS = {}


class AXIL5MasterReadGroupsTB(AXIL5MasterReadTB):
    """The same read-master flow with every optional AXI5-Lite group ON.

    `AXIL5MasterReadTB` above deliberately runs with no groups, against the
    AXI4-Lite RTL, to assert the all-groups-off equivalence. That left
    `axil5_master_rd` itself -- the one AXI5-Lite module whose runner pointed
    at its AXI4-Lite counterpart -- with no coverage of its own, and the read
    master with no groups-on path at all.

    That matters because the SKID payload widths are conditional sums:

        ARSize = AW + 3 + (ENABLE_LOCK ? 1 : 0) + (ENABLE_USER ? UW : 0) + ...

    A wrong slice when a group is present is invisible to the equivalence run,
    because every one of those terms is zero there.

    Widths mirror the RTL parameter defaults in rtl/amba/axil5/; change one
    here without changing the DUT parameter and the bind fails loudly.
    """

    COMPONENT_KWARGS = {
        'user_width': 4,     # USER_WIDTH
        'trace': True,       # ENABLE_TRACE
        'loop_width': 3,     # LOOP_WIDTH
        'mpam_width': 11,    # MPAM_WIDTH
        'mecid_width': 16,   # MECID_WIDTH
        'nsaid_width': 4,    # NSAID_WIDTH
        'poison': True,      # ENABLE_POISON
        'exclusive': True,   # ENABLE_LOCK
    }
