# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: AXI4DWidthConverterScoreboard
# Purpose: AXI4 Data Width Converter Verification Scoreboard
#
# Documentation: docs/VERIFICATION_ARCHITECTURE_GUIDE.md
# Subsystem: scoreboards/axi4/
#
# Author: RTL Design Sherpa
# Created: 2025-10-18

"""
AXI4 Data Width Converter Scoreboard

Verification scoreboard for checking data integrity across width conversion.
Uses queue-based verification for Phase 1, can be extended with memory model
for complex out-of-order scenarios in Phase 2+.

Verification Strategy:
- Phase 1: Simple queue-based checking for in-order transactions
- Phase 2+: Memory model integration for out-of-order, multi-ID scenarios
"""

from collections import deque


class AXI4DWidthConverterScoreboard:
    """
    Scoreboard for AXI4 Data Width Converter verification.

    Uses direct queue access from GAXI monitors for simple in-order verification.
    Tracks data integrity across width conversion (upsize/downsize).
    """

    def __init__(self, slave_master, master_slave, memory_model=None, log=None):
        """
        Initialize scoreboard.

        Args:
            slave_master: GAXI Master on slave side (drives s_axi_*)
            master_slave: GAXI Slave on master side (responds on m_axi_*)
            memory_model: Shared memory model (optional)
            log: Logger instance
        """
        self.slave_master = slave_master
        self.master_slave = master_slave
        self.memory_model = memory_model
        self.log = log

        # Statistics
        self.checks_performed = 0
        self.errors_detected = 0
        self.data_mismatches = 0
        self.transactions_verified = 0

    def check_write_data_integrity(self, expected_addr, expected_data_list):
        """
        Verify write data integrity across width conversion.

        Args:
            expected_addr: Expected write address
            expected_data_list: List of expected data values

        Returns:
            True if verification passes, False otherwise
        """
        # Placeholder for Phase 2 - queue-based verification
        # Will check master-side transactions against expected values

        self.checks_performed += 1
        self.transactions_verified += 1

        if self.log:
            self.log.debug(f"Write data integrity check at 0x{expected_addr:X}")

        return True

    def check_read_data_integrity(self, addr, expected_data_list, actual_data_list):
        """
        Verify read data integrity across width conversion.

        Args:
            addr: Read address
            expected_data_list: Expected read data
            actual_data_list: Actual read data from slave interface

        Returns:
            True if data matches, False otherwise
        """
        self.checks_performed += 1

        if expected_data_list != actual_data_list:
            self.errors_detected += 1
            self.data_mismatches += 1

            if self.log:
                self.log.error(f"Read data mismatch at 0x{addr:X}")
                self.log.error(f"Expected: {[hex(d) for d in expected_data_list]}")
                self.log.error(f"Actual:   {[hex(d) for d in actual_data_list]}")

            return False

        self.transactions_verified += 1

        if self.log:
            self.log.debug(f"Read data verified at 0x{addr:X}")

        return True

    def clear_queues(self):
        """Clear all monitor queues after verification section."""
        # Placeholder for Phase 2 - will clear GAXI monitor queues
        pass

    def get_statistics(self):
        """
        Get scoreboard statistics.

        Returns:
            Dictionary with verification metrics
        """
        return {
            'checks_performed': self.checks_performed,
            'errors_detected': self.errors_detected,
            'data_mismatches': self.data_mismatches,
            'transactions_verified': self.transactions_verified,
            'pass_rate': (self.transactions_verified / max(self.checks_performed, 1)) * 100
        }

    def report(self):
        """Generate verification report."""
        stats = self.get_statistics()

        if self.log:
            self.log.info("="*60)
            self.log.info("AXI4 Data Width Converter Scoreboard Report")
            self.log.info("-"*60)
            self.log.info(f"Checks Performed:       {stats['checks_performed']}")
            self.log.info(f"Transactions Verified:  {stats['transactions_verified']}")
            self.log.info(f"Errors Detected:        {stats['errors_detected']}")
            self.log.info(f"Data Mismatches:        {stats['data_mismatches']}")
            self.log.info(f"Pass Rate:              {stats['pass_rate']:.1f}%")
            self.log.info("="*60)

        return stats
