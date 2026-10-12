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
of the test: an AXI5-Lite Manager with no ID (``ID_R_WIDTH`` = 0, which
IHI 0022L Table A5.2 permits a Manager) and no optional signal groups enabled
has exactly the AXI4-Lite signal set, so AXIL5 BFMs must drive AXI4-Lite-shaped
RTL and pass the identical traffic, checks and randomizer sweeps that the
AXIL4 BFMs do. ``val/amba/test_axil5_axil4_equivalence.py`` runs it against
both ``axil4_master_rd`` and ``axil5_master_rd`` elaborated with
``ID_WIDTH=0`` and every optional group off.

Why this exists at all: ``tests/unit/test_axil5_extends_axil4.py`` in the
framework repo proves the two declare the same FIELDS, but every one of those
checks is static -- it compares field configs and class structure without ever
constructing a component or moving a beat. A BFM that resolves no signals, or
that dies in ``__init__``, would pass all of them. This testbench is the part
that cannot be faked: real RTL, real signal resolution, real read transactions
with data checked against the memory model.

This class proves only the shared path -- construction, binding, transactions
-- which is where a subclassing mistake would land. The ID and the optional
groups against axil5_* RTL are :class:`AXIL5MasterReadGroupsTB` below, and the
groups' end-to-end echo is ``test_axil5_opt_signals.py``.
"""

from CocoTBFramework.components.axil5.axil5_factories import (
    create_axil5_master_rd,
    create_axil5_slave_rd,
)

from TBClasses.axil4.axil4_master_read_tb import AXIL4MasterReadTB
from TBClasses.axil5.axil5_id_check import (
    AXIL5_RTL_DEFAULT_COMPONENT_KWARGS,
    install as install_id_check,
)


class AXIL5MasterReadTB(AXIL4MasterReadTB):
    """AXI4-Lite read-master RTL driven by AXI5-Lite BFMs.

    Inherits every phase, check and randomizer configuration from the AXIL4
    testbench. Only the factories differ, so a change to the AXI4-Lite flow
    reaches the AXI5-Lite one automatically instead of needing to be
    remembered twice.
    """

    MASTER_RD_FACTORY = staticmethod(create_axil5_master_rd)
    SLAVE_RD_FACTORY = staticmethod(create_axil5_slave_rd)
    # No ID and no optional groups: the DUT has the AXI4-Lite port set. This
    # empty dict IS the assertion that AXIL5 defaults to the AXI4-Lite signal
    # set -- enabling the ID or a group here would make the DUT fail to bind.
    COMPONENT_KWARGS = {}


class AXIL5MasterReadGroupsTB(AXIL5MasterReadTB):
    """The same read-master flow with the ID and every optional group ON.

    `AXIL5MasterReadTB` above deliberately runs with no groups, against the
    AXI4-Lite RTL, to assert the all-groups-off equivalence. That left
    `axil5_master_rd` itself -- the one AXI5-Lite module whose runner pointed
    at its AXI4-Lite counterpart -- with no coverage of its own, and the read
    master with no groups-on path at all.

    That matters because the SKID payload widths are conditional sums:

        ARSize = AW + 3 + ID_WIDTH + (ENABLE_USER ? UW : 0) + ...

    A wrong slice when a field is present is invisible to the equivalence run,
    because every one of those terms is zero there.

    Every read issued through the Manager-side BFM carries a rotating non-zero
    ARID and must come back with the same RID (``axil5_id_check``).

    Widths mirror the RTL parameter defaults in rtl/amba/axil5/; see
    ``AXIL5_RTL_DEFAULT_COMPONENT_KWARGS``.
    """

    COMPONENT_KWARGS = AXIL5_RTL_DEFAULT_COMPONENT_KWARGS

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut, aclk, aresetn)
        self.id_check = install_id_check(
            self.master_components['interface'], self.log)
