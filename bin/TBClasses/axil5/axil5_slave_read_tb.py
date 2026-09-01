# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL5SlaveReadTB
# Purpose: Drive the AXI5-Lite read slave RTL with AXI5-Lite BFMs
#
# Subsystem: framework

"""AXI5-Lite read slave testbench.

:class:`AXIL4SlaveReadTB` with the component factories swapped for their AXI5-Lite
equivalents, and the optional signal groups TURNED ON.

That second part is what makes this different from
:class:`AXIL5MasterReadTB`, which drives AXI4-Lite RTL with AXIL5 BFMs and
therefore has to leave every group off. Here the DUT is ``axil5_slave_read``, whose
ENABLE_* parameters all default to 1, so the RTL carries
AxUSER/AxTRACE/AxLOOP/AxMPAM/AxMECID/AxNSAID/AxLOCK on AR/R -- and the BFMs
must carry them too or signal resolution binds nothing to those ports and they
sit undriven at X.

The widths below are the RTL's own defaults. They are not a preference: a BFM
configured wider or narrower than the DUT is a bind failure, and configured
with a group the DUT lacks is the same. This is the pairing the
``axil5_*`` protocol entries in ``PROTOCOL_SIGNAL_CONFIGS`` exist to make
checkable.

Every phase, check and randomizer configuration is inherited. Only the
factories and the group configuration differ, so a fix to the AXI4-Lite flow
reaches this one automatically instead of needing to be remembered twice.
"""

from CocoTBFramework.components.axil5.axil5_factories import (
    create_axil5_slave_rd,
    create_axil5_master_rd,
)

from TBClasses.axil4.axil4_slave_read_tb import AXIL4SlaveReadTB


class AXIL5SlaveReadTB(AXIL4SlaveReadTB):
    """AXI5-Lite read slave RTL, optional groups enabled."""

    SLAVE_RD_FACTORY = staticmethod(create_axil5_slave_rd)
    MASTER_RD_FACTORY = staticmethod(create_axil5_master_rd)

    # Mirrors the RTL parameter defaults in rtl/amba/axil5/. Change one here
    # without changing the DUT parameter and the bind fails loudly, which is
    # the desired failure -- silently driving nothing would not be.
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
