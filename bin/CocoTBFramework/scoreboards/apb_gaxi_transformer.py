# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBtoGAXITransformer
# Purpose: APB to GAXI Transformer
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB to GAXI Transformer

This module provides classes for transforming between APB and GAXI protocols.
"""
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


class APBtoGAXITransformer:
    """
    Transforms APB transactions to GAXI packets and vice versa.

    This class provides:
    1. Conversion from APB transaction to GAXI packet
    2. Conversion from GAXI packet to APB transaction
    3. Support for field mapping configuration
    """

    def __init__(self, gaxi_field_config, gaxi_packet_class=GAXIPacket, log=None):
        """
        Initialize the transformer.

        Args:
            gaxi_field_config: Field configuration for GAXI packets
            gaxi_packet_class: Class to use for creating GAXI packets
            log: Logger instance
        """
        self.gaxi_field_config = gaxi_field_config
        self.gaxi_packet_class = gaxi_packet_class
        self.log = log

    def apb_to_gaxi(self, apb_transaction):
        """
        Convert APB transaction to GAXI packet.

        Args:
            apb_transaction: APB transaction to convert

        Returns:
            GAXI packet equivalent to APB transaction
        """
        # Create GAXI packet
        packet = self.gaxi_packet_class(self.gaxi_field_config)

        # Set basic fields from APB transaction
        packet.cmd = 1 if apb_transaction.direction == 'WRITE' else 0
        packet.addr = apb_transaction.paddr

        # Set data field based on direction
        if apb_transaction.direction == 'WRITE':
            packet.data = apb_transaction.pwdata

            # Set strobe if available
            if hasattr(apb_transaction, 'pstrb') and 'strb' in self.gaxi_field_config:
                packet.strb = apb_transaction.pstrb
        elif hasattr(apb_transaction, 'prdata'):
            packet.data = apb_transaction.prdata

        # Copy timing info if available
        if hasattr(apb_transaction, 'start_time'):
            packet.start_time = apb_transaction.start_time

        if hasattr(apb_transaction, 'end_time'):
            packet.end_time = apb_transaction.end_time

        # Log the transformation
        if self.log:
            self.log.debug(f"Transformed APB to GAXI: {packet.formatted(compact=True)}")

        return packet

    def gaxi_to_apb(self, gaxi_packet, apb_transaction_class):
        """
        Convert GAXI packet to APB transaction.

        Args:
            gaxi_packet: GAXI packet to convert
            apb_transaction_class: Class to use for creating APB transaction

        Returns:
            APB transaction equivalent to GAXI packet
        """
        # Create APB transaction
        transaction = apb_transaction_class()

        # Set direction
        transaction.direction = 'WRITE' if gaxi_packet.cmd == 1 else 'READ'
        transaction.pwrite = 1 if gaxi_packet.cmd == 1 else 0

        # Set address
        transaction.paddr = gaxi_packet.addr

        # Set data based on direction
        if gaxi_packet.cmd == 1:  # Write
            transaction.pwdata = gaxi_packet.data

            # Set strobe if available
            if hasattr(gaxi_packet, 'strb'):
                transaction.pstrb = gaxi_packet.strb
        else:  # Read
            transaction.prdata = gaxi_packet.data

        # Copy timing info if available
        if hasattr(gaxi_packet, 'start_time'):
            transaction.start_time = gaxi_packet.start_time

        if hasattr(gaxi_packet, 'end_time'):
            transaction.end_time = gaxi_packet.end_time

        # Log the transformation
        if self.log:
            self.log.debug(f"Transformed GAXI to APB: {transaction}")

        return transaction


class APBGAXIAdapterBase:
    """
    Base class for APB-GAXI adapters.

    Provides common functionality for both APB to GAXI and GAXI to APB adapters:
    1. Field configuration handling
    2. Transaction tracking
    3. Timing statistics
    """

    def __init__(self, transformer, field_config=None, log=None):
        """
        Initialize the adapter.

        Args:
            transformer: APBtoGAXITransformer instance
            field_config: Field configuration (if different from transformer's)
            log: Logger instance
        """
        self.transformer = transformer
        self.field_config = field_config or transformer.gaxi_field_config
        self.log = log or transformer.log

        # Statistics
        self.transaction_count = 0
        self.error_count = 0
        self.total_latency = 0

    def reset_statistics(self):
        """Reset adapter statistics."""
        self.transaction_count = 0
        self.error_count = 0
        self.total_latency = 0

    def get_average_latency(self):
        """
        Get average transaction latency.

        Returns:
            Average latency in ns, or 0 if no transactions processed
        """
        if self.transaction_count == 0:
            return 0
        return self.total_latency / self.transaction_count


class APBtoGAXIAdapter(APBGAXIAdapterBase):
    """
    Adapter for converting APB transactions to GAXI.

    This class:
    1. Accepts APB transactions
    2. Transforms them to GAXI packets
    3. Delivers the packets to a GAXI master
    """

    def __init__(self, transformer, gaxi_master, field_config=None, log=None):
        """
        Initialize the adapter.

        Args:
            transformer: APBtoGAXITransformer instance
            gaxi_master: GAXI master to send packets to
            field_config: Field configuration (if different from transformer's)
            log: Logger instance
        """
        super().__init__(transformer, field_config, log)
        self.gaxi_master = gaxi_master

        # Queue for tracking transactions
        self.pending_transactions = {}  # addr -> transaction

    async def process_transaction(self, apb_transaction):
        """
        Process an APB transaction and send to GAXI master.

        Args:
            apb_transaction: APB transaction to process

        Returns:
            GAXI packet sent to master
        """
        # Transform to GAXI packet
        packet = self.transformer.apb_to_gaxi(apb_transaction)

        # Record transaction for tracking
        addr = packet.addr
        self.pending_transactions[addr] = apb_transaction

        # Increment transaction count
        self.transaction_count += 1

        # Send through GAXI master
        await self.gaxi_master.send(packet)

        # Log the action
        if self.log:
            self.log.info(f"APB->GAXI: {'WRITE' if packet.cmd == 1 else 'READ'} addr=0x{addr:08X}")

        return packet


class GAXItoAPBAdapter(APBGAXIAdapterBase):
    """
    Adapter for converting GAXI packets to APB.

    This class:
    1. Accepts GAXI packets
    2. Transforms them to APB transactions
    3. Delivers the transactions to an APB master
    """

    def __init__(self, transformer, apb_master, apb_transaction_class,
                field_config=None, log=None):
        """
        Initialize the adapter.

        Args:
            transformer: APBtoGAXITransformer instance
            apb_master: APB master to send transactions to
            apb_transaction_class: Class to use for creating APB transactions
            field_config: Field configuration (if different from transformer's)
            log: Logger instance
        """
        super().__init__(transformer, field_config, log)
        self.apb_master = apb_master
        self.apb_transaction_class = apb_transaction_class

        # Queue for tracking packets
        self.pending_packets = {}  # addr -> packet

    async def process_packet(self, gaxi_packet):
        """
        Process a GAXI packet and send to APB master.

        Args:
            gaxi_packet: GAXI packet to process

        Returns:
            APB transaction sent to master
        """
        # Transform to APB transaction
        transaction = self.transformer.gaxi_to_apb(
            gaxi_packet,
            self.apb_transaction_class
        )

        # Record packet for tracking
        addr = gaxi_packet.addr
        self.pending_packets[addr] = gaxi_packet

        # Increment transaction count
        self.transaction_count += 1

        # Send through APB master
        await self.apb_master.send(transaction)

        # Log the action
        if self.log:
            self.log.info(f"GAXI->APB: {'WRITE' if gaxi_packet.cmd == 1 else 'READ'} addr=0x{addr:08X}")

        return transaction


def create_apb_gaxi_adapters(apb_master, gaxi_master,
                          apb_transaction_class, gaxi_field_config,
                          log=None):
    """
    Create a pair of APB-GAXI adapters for bidirectional conversion.

    Args:
        apb_master: APB master for sending transactions
        gaxi_master: GAXI master for sending packets
        apb_transaction_class: Class to use for creating APB transactions
        gaxi_field_config: Field configuration for GAXI packets
        log: Logger instance

    Returns:
        Tuple of (APBtoGAXIAdapter, GAXItoAPBAdapter)
    """
    # Create transformer
    transformer = APBtoGAXITransformer(gaxi_field_config, log=log)

    # Create adapters
    apb_to_gaxi = APBtoGAXIAdapter(transformer, gaxi_master, log=log)
    gaxi_to_apb = GAXItoAPBAdapter(transformer, apb_master,
                                apb_transaction_class, log=log)

    return (apb_to_gaxi, gaxi_to_apb)