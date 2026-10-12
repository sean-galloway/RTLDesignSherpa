# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL5SlaveMonitorTB
# Purpose: Drive the AXI5-Lite slave monitor RTL with AXI5-Lite BFMs
#
# Subsystem: framework

"""AXI5-Lite slave monitor testbench.

:class:`AXIL4SlaveMonitorTB` with the component factories swapped and the AXI5-Lite
transaction ID and optional signal groups enabled. Every monitor phase,
packet check and randomizer sweep is inherited.

Worth knowing what this does and does not cover. The monitor itself sees
what it sees on AXI4-Lite -- handshakes, addresses, responses and timing.
Its ID ports are still tied to 0, as on AXI4-Lite, so it tracks transactions
in issue order; the AXI5-Lite ID, USER, TRACE and POISON are carried THROUGH
the transport path and not observed by the monitor.

Every transaction the Manager-side BFM issues carries a rotating non-zero ID
that must come back on the response (``axil5_id_check``).

The widths mirror the RTL parameter defaults in ``rtl/amba/axil5/``
(``AXIL5_RTL_DEFAULT_COMPONENT_KWARGS``). A BFM configured differently from
its DUT is a bind failure, which is the loud version of the mistake.
"""

from CocoTBFramework.components.axil5.axil5_factories import (
    create_axil5_master_rd,
    create_axil5_master_wr,
    create_axil5_slave_rd,
    create_axil5_slave_wr,
)

from TBClasses.axil5.axil5_id_check import (
    AXIL5_RTL_DEFAULT_COMPONENT_KWARGS,
    install as install_id_check,
)
from TBClasses.axil4.monitor.axil4_slave_monitor_tb import AXIL4SlaveMonitorTB


class AXIL5SlaveMonitorTB(AXIL4SlaveMonitorTB):
    """AXI5-Lite slave monitor RTL, ID and optional groups enabled."""

    MASTER_WR_FACTORY = staticmethod(create_axil5_master_wr)
    MASTER_RD_FACTORY = staticmethod(create_axil5_master_rd)
    SLAVE_WR_FACTORY = staticmethod(create_axil5_slave_wr)
    SLAVE_RD_FACTORY = staticmethod(create_axil5_slave_rd)

    COMPONENT_KWARGS = AXIL5_RTL_DEFAULT_COMPONENT_KWARGS

    async def initialize(self):
        """Build the BFMs (inherited), then wrap the Manager for ID checks."""
        await super().initialize()
        self.id_check = install_id_check(
            self.master_components['interface'], self.log)
