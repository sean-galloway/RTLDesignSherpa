# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBScoreboard
# Purpose: APB Scoreboard for verifying APB transactions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""APB Scoreboard for verifying APB transactions"""
from collections import defaultdict
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.scoreboards.base_scoreboard import BaseScoreboard, ProtocolTransformer


class APBScoreboard(BaseScoreboard):
    """Scoreboard for APB transactions"""

    def __init__(self, name, addr_width=32, data_width=32, log=None):
        super().__init__(name, log)
        self.addr_width = addr_width
        self.data_width = data_width
        self.strb_width = data_width // 8

        # Track which master initiated each transaction
        self.master_transactions = defaultdict(list)

    def _compare_transactions(self, expected, actual):
        """Compare APB cycles based on direction, address, and data"""
        if not isinstance(expected, APBPacket) or not isinstance(actual, APBPacket):
            if self.log:
                self.log.error(f"{self.name} - Invalid transaction types")
                self.log.error(f"  Expected type: {type(expected)}")
                self.log.error(f"  Actual type: {type(actual)}")
            return False

        # Basic comparison already implemented in APBPacket.__eq__
        return expected == actual

    def _log_mismatch(self, expected, actual):
        """Enhanced mismatch logging for APB cycles"""
        if not self.log:
            return
        self.log.error(f"{self.name} - APB Cycle mismatch:")
        self.log.error(f"  Expected: {expected.formatted(compact=True)}")
        self.log.error(f"  Actual:   {actual.formatted(compact=True)}")

        # Detailed comparison of fields
        if expected.direction != actual.direction:
            self.log.error(f"  Direction mismatch: expected={expected.direction}, actual={actual.direction}")

        if expected.paddr != actual.paddr:
            self.log.error(f"  Address mismatch: expected=0x{expected.paddr:X}, actual=0x{actual.paddr:X}")

        if expected.direction == 'WRITE':
            if expected.pwdata != actual.pwdata:
                self.log.error(f"  Write data mismatch: expected=0x{expected.pwdata:X}, actual=0x{actual.pwdata:X}")
            if expected.pstrb != actual.pstrb:
                self.log.error(f"  Strobe mismatch: expected=0x{expected.pstrb:X}, actual=0x{actual.pstrb:X}")
        elif expected.prdata != actual.prdata:
            self.log.error(f"  Read data mismatch: expected=0x{expected.prdata:X}, actual=0x{actual.prdata:X}")

        if expected.pprot != actual.pprot:
            self.log.error(f"  Protection mismatch: expected=0x{expected.pprot:X}, actual=0x{actual.pprot:X}")

        if expected.pslverr != actual.pslverr:
            self.log.error(f"  Slave error mismatch: expected={expected.pslverr}, actual={actual.pslverr}")

    def add_expected_with_source(self, transaction, master_id):
        """Add an expected transaction with source information"""
        self.add_expected(transaction)
        self.master_transactions[master_id].append(transaction)

    def clear(self):
        """Clear all transactions from scoreboard"""
        super().clear()
        self.master_transactions.clear()


class APBCrossbarScoreboard:
    """Router scoreboard for APB crossbar testing"""

    def __init__(self, name, num_slaves, addr_width=32, data_width=32, log=None):
        """
        Initialize APB crossbar scoreboard with multiple slave scoreboards

        Args:
            name: Base name for scoreboards
            num_slaves: Number of slave scoreboards to create
            addr_width: Address width in bits
            data_width: Data width in bits
            log: Logger object
        """
        self.name = name
        self.num_slaves = num_slaves
        self.addr_width = addr_width
        self.data_width = data_width
        self.log = log
        self.strb_width = data_width // 8

        # Create scoreboard for each slave
        self.slave_scoreboards = []
        for i in range(num_slaves):
            sb = APBScoreboard(f"{name}_Slave_{i}", addr_width, data_width, log)
            self.slave_scoreboards.append(sb)

        # Default address map (can be overridden)
        self.addr_map = []
        for i in range(num_slaves):
            base_addr = i * 0x1000
            end_addr = base_addr + 0xFFC
            self.addr_map.append((base_addr, end_addr))

    def set_address_map(self, addr_map):
        """
        Set custom address map for routing transactions

        Args:
            addr_map: List of (base_addr, end_addr) tuples for each slave
        """
        if len(addr_map) != self.num_slaves:
            if self.log:
                self.log.error(f"Address map size ({len(addr_map)}) doesn't match number of slaves ({self.num_slaves})")
            return

        self.addr_map = addr_map

    def get_slave_idx(self, addr):  # sourcery skip: use-next
        """
        Determine which slave an address should go to

        Args:
            addr: Address to route

        Returns:
            int: Slave index (or None if no match)
        """
        for i, (base, end) in enumerate(self.addr_map):
            if base <= addr <= end:
                return i

        # Default to modulo routing if no match in address map
        return addr // 0x1000 % self.num_slaves

    def add_master_transaction(self, transaction, master_id):
        """
        Add a transaction from a master, routing to correct slave scoreboard

        Args:
            transaction: APB transaction to route
            master_id: ID of the master that initiated the transaction
        """
        # Determine slave based on address
        addr = transaction.paddr
        slave_idx = self.get_slave_idx(addr)

        # Don't modify transaction.pprot here, just add to scoreboard with source info
        scoreboard = self.slave_scoreboards[slave_idx]
        scoreboard.add_expected_with_source(transaction, master_id)

        if self.log:
            self.log.debug(f"Routed transaction from master {master_id} to slave {slave_idx}: addr=0x{addr:08X}")
            # Extra logging for slave 0
            if slave_idx == 0:
                self.log.info(f"SLAVE0_EXPECTED: Master {master_id} -> Slave 0, addr=0x{addr:08X}, {transaction.formatted(compact=True)}")

    def add_slave_transaction(self, transaction, slave_idx):
        """
        Add a transaction from a slave to its scoreboard

        Args:
            transaction: APB transaction from slave
            slave_idx: Index of the slave
        """
        if 0 <= slave_idx < self.num_slaves:
            scoreboard = self.slave_scoreboards[slave_idx]
            scoreboard.add_actual(transaction)

            # Extra logging for slave 0
            if self.log and slave_idx == 0:
                self.log.info(f"SLAVE0_ACTUAL: Slave 0 received transaction: {transaction.formatted(compact=True)}")

    def all_empty(self):
        """
        Check if all scoreboards are empty

        Returns:
            bool: True if all scoreboards are empty
        """
        return all(sb.is_empty() for sb in self.slave_scoreboards)

    def clear_all(self):
        """Clear all slave scoreboards"""
        for sb in self.slave_scoreboards:
            sb.clear()

    def result(self):
        """
        Get overall result as minimum of all slave results

        Returns:
            float: Overall pass rate (0.0 to 1.0)
        """
        results = [sb.result() for sb in self.slave_scoreboards]

        return 1.0 if not results else min(results)

    def report(self):
        """
        Generate detailed report of all scoreboards

        Returns:
            str: Report text
        """
        lines = [f"=== {self.name} Report ==="]

        all_passed = True
        for i, sb in enumerate(self.slave_scoreboards):
            result = sb.result()
            expected_remaining = len(sb.expected_queue)
            actual_remaining = len(sb.actual_queue)

            if result < 1.0:
                all_passed = False
                lines.append(f"Slave {i}: FAIL ({result:.2f}) - Transactions: {sb.transaction_count}, Errors: {sb.error_count}, Expected_left: {expected_remaining}, Actual_left: {actual_remaining}")

                # Extra detail for slave 0
                if i == 0 and self.log:
                    self.log.error(f"SLAVE0_REPORT: transaction_count={sb.transaction_count}, error_count={sb.error_count}")
                    self.log.error(f"SLAVE0_REPORT: expected_queue length={expected_remaining}, actual_queue length={actual_remaining}")
                    if sb.mismatched:
                        self.log.error(f"SLAVE0_REPORT: {len(sb.mismatched)} mismatched transactions:")
                        for idx, (exp, act) in enumerate(sb.mismatched[:5]):  # Show first 5
                            self.log.error(f"  Mismatch {idx}: Expected={exp.formatted(compact=True)}, Actual={act.formatted(compact=True)}")
            else:
                lines.append(f"Slave {i}: PASS")

        lines.append(f"Overall: {'PASS' if all_passed else 'FAIL'}")

        return "\n".join(lines)


class APBtoGAXITransformer(ProtocolTransformer):
    """Transformer from APB to GAXI transactions"""

    def __init__(self, gaxi_field_config, packet_class, log=None):
        super().__init__("APB", "GAXI", log)
        self.gaxi_field_config = gaxi_field_config
        self.packet_class = packet_class

    def transform(self, apb_cycle):
        """Transform APB cycle to one or more GAXI transactions"""
        if not isinstance(apb_cycle, APBPacket):
            if self.log:
                self.log.error("Invalid transaction type for APB to GAXI transformation")
            return []

        # For simplicity, we'll transform 1:1
        # In a real implementation, you might want to handle more complex transformations

        gaxi_packet = self.packet_class(self.gaxi_field_config)

        # Map fields from APB to GAXI
        if 'addr' in gaxi_packet.fields:
            gaxi_packet.fields['addr'] = apb_cycle.paddr

        if 'data' in gaxi_packet.fields:
            if apb_cycle.direction == 'WRITE':
                gaxi_packet.fields['data'] = apb_cycle.pwdata
            else:
                gaxi_packet.fields['data'] = apb_cycle.prdata

        if 'strb' in gaxi_packet.fields and apb_cycle.direction == 'WRITE':
            gaxi_packet.fields['strb'] = apb_cycle.pstrb

        # Return as a single transaction for now
        # In more complex cases, you might return multiple transactions
        return [gaxi_packet]
