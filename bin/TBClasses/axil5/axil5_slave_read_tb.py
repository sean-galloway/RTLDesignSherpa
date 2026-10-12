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
equivalents, the transaction ID and the optional signal groups TURNED ON.

The DUT is ``axil5_slave_rd`` at its default parameters, so the RTL carries AxID/xID
(``ID_WIDTH``) plus the AXI5-Lite optional groups USER, TRACE and POISON --
and the BFMs carry them too, or signal resolution binds nothing to those ports
and they sit undriven. ``AXIL5_RTL_DEFAULT_COMPONENT_KWARGS`` holds the
matching BFM configuration.

On top of the inherited phases every transaction the Manager-side BFM issues
gets a rotating non-zero ID, and the response must come back with the same ID
(``axil5_id_check``). That is what proves these pass-through modules carry the
ID both ways; AXI4-Lite phases alone would only ever send ID 0.

Every phase, check and randomizer configuration is inherited. Only the
factories and the group configuration differ, so a fix to the AXI4-Lite flow
reaches this one automatically instead of needing to be remembered twice.
"""

from CocoTBFramework.components.axil5.axil5_factories import (
    create_axil5_slave_rd,
    create_axil5_master_rd,
)

from TBClasses.axil5.axil5_id_check import (
    AXIL5_RTL_DEFAULT_COMPONENT_KWARGS,
    install as install_id_check,
)
from TBClasses.axil4.axil4_slave_read_tb import AXIL4SlaveReadTB


class AXIL5SlaveReadTB(AXIL4SlaveReadTB):
    """AXI5-Lite read slave RTL, ID and optional groups enabled."""

    SLAVE_RD_FACTORY = staticmethod(create_axil5_slave_rd)
    MASTER_RD_FACTORY = staticmethod(create_axil5_master_rd)

    COMPONENT_KWARGS = AXIL5_RTL_DEFAULT_COMPONENT_KWARGS

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut, aclk, aresetn)
        self.id_check = install_id_check(
            self.master_components['interface'], self.log)
