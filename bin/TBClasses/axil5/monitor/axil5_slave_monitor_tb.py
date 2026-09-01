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
optional signal groups enabled. Every monitor phase, packet check and
randomizer sweep is inherited.

Worth knowing what this does and does not cover. The monitor itself sees
exactly what it sees on AXI4-Lite -- handshakes, addresses, responses and
timing -- because ``axi_monitor_filtered`` has no ports for MPAM, MECID,
NSAID, TRACE, LOOP or POISON and never observes them. So this exercises the
optional groups THROUGH the transport path while the monitor watches the
channels underneath them; it does not check the groups themselves. A monitor
that reported on MPAM would need ports it does not have.

The widths mirror the RTL parameter defaults in ``rtl/amba/axil5/``. A BFM
configured differently from its DUT is a bind failure, which is the loud
version of the mistake.
"""

from CocoTBFramework.components.axil5.axil5_factories import (
    create_axil5_master_rd,
    create_axil5_master_wr,
    create_axil5_slave_rd,
    create_axil5_slave_wr,
)

from TBClasses.axil4.monitor.axil4_slave_monitor_tb import AXIL4SlaveMonitorTB


class AXIL5SlaveMonitorTB(AXIL4SlaveMonitorTB):
    """AXI5-Lite slave monitor RTL, optional groups enabled."""

    MASTER_WR_FACTORY = staticmethod(create_axil5_master_wr)
    MASTER_RD_FACTORY = staticmethod(create_axil5_master_rd)
    SLAVE_WR_FACTORY = staticmethod(create_axil5_slave_wr)
    SLAVE_RD_FACTORY = staticmethod(create_axil5_slave_rd)

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
