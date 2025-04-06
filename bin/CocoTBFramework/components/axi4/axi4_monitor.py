"""
AXI4 Monitor Component for Verification

This module provides the AXI4Monitor class for observing AXI4 interfaces.
"""

import cocotb
from collections import deque
from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time

from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_monitor
from CocoTBFramework.components.field_config import FieldConfig
from .axi4_packets import AXI4Packet
from .axi4_fields_signals import (
    get_aw_signal_map,
    get_w_signal_map,
    get_b_signal_map,
    get_ar_signal_map,
    get_r_signal_map
)


class AXI4Monitor:
    """
    AXI4 Monitor component that observes AXI4 transactions.

    This class provides:
    - Separate GAXI monitors for each AXI4 channel (AW, W, B, AR, R)
    - Transaction tracking across channels
    - AXI4 protocol checking
    """

    def __init__(self, dut, title, prefix, divider, suffix, clock, channels,
                    id_width=8, addr_width=32, data_width=32, user_width=1,
                    field_configs=None, is_slave_side=False, check_protocol=False, log=None):
        """
        Initialize AXI4 Monitor component.

        Args:
            dut: Device under test
            title: Component title
            prefix: Signal prefix
            divider: used if there is an '_' between the channel and the signal
            suffix: optional suffix useed at the end
            clock: Clock signal
            channels: a list of the channels to instantiate
            id_width: Width of ID fields (default: 8)
            addr_width: Width of address fields (default: 32)
            data_width: Width of data fields (default: 32)
            user_width: Width of user fields (default: 1)
            field_configs: Dictionary of field configurations for each channel
            is_slave_side: Whether to monitor slave-side signals (default: False)
            check_protocol: Enable AXI4 protocol checking (default: True)
            log: Logger instance
        """
        self.title = title
        self.clock = clock
        self.log = log
        self.check_protocol = check_protocol
        self.is_slave_side = is_slave_side
        self.channels = [s.upper() for s in channels]

        # Calculate strobe width
        self.strb_width = data_width // 8
        
        # Store field configs
        self.field_configs = field_configs
        
        # Ensure we have proper field configs for each channel
        if not self.field_configs:
            raise ValueError(f"AXI4Monitor '{title}' requires field configs for each channel")
        
        # Extract field configs for each channel
        self.aw_field_config = self.field_configs.get('AW')
        self.w_field_config = self.field_configs.get('W')
        self.b_field_config = self.field_configs.get('B')
        self.ar_field_config = self.field_configs.get('AR')
        self.r_field_config = self.field_configs.get('R')

        # Prepare signal mappings
        aw_signal_map, aw_optional_signal_map = get_aw_signal_map(prefix, divider, suffix)
        w_signal_map, w_optional_signal_map = get_w_signal_map(prefix, divider, suffix)
        b_signal_map, b_optional_signal_map = get_b_signal_map(prefix, divider, suffix)
        ar_signal_map, ar_optional_signal_map = get_ar_signal_map(prefix, divider, suffix)
        r_signal_map, r_optional_signal_map = get_r_signal_map(prefix, divider, suffix)

        # Create channel monitors
        if 'AW' in self.channels and self.aw_field_config:
            self.aw_monitor = create_gaxi_monitor(
                dut, f"{title}_AW", "", clock,
                field_config=self.aw_field_config,
                is_slave=is_slave_side,
                multi_sig=True,
                signal_map=aw_signal_map,
                optional_signal_map=aw_optional_signal_map,
                log=log
            )
            self.aw_monitor.add_callback(self._handle_aw_transaction)
        else:
            self.aw_monitor = None

        if 'W' in self.channels and self.w_field_config:
            self.w_monitor = create_gaxi_monitor(
                dut, f"{title}_W", "", clock,
                field_config=self.w_field_config,
                is_slave=is_slave_side,
                multi_sig=True,
                signal_map=w_signal_map,
                optional_signal_map=w_optional_signal_map,
                log=log
            )
            self.w_monitor.add_callback(self._handle_w_transaction)
        else:
            self.w_monitor = None

        if 'B' in self.channels and self.b_field_config:
            self.b_monitor = create_gaxi_monitor(
                dut, f"{title}_B", "", clock,
                field_config=self.b_field_config,
                is_slave=not is_slave_side,  # B channel direction is opposite
                multi_sig=True,
                signal_map=b_signal_map,
                optional_signal_map=b_optional_signal_map,
                log=log
            )
            self.b_monitor.add_callback(self._handle_b_transaction)
        else:
            self.b_monitor = None

        if 'AR' in self.channels and self.ar_field_config:
            self.ar_monitor = create_gaxi_monitor(
                dut, f"{title}_AR", "", clock,
                field_config=self.ar_field_config,
                is_slave=is_slave_side,
                multi_sig=True,
                signal_map=ar_signal_map,
                optional_signal_map=ar_optional_signal_map,
                log=log
            )
            self.ar_monitor.add_callback(self._handle_ar_transaction)
        else:
            self.ar_monitor = None

        if 'R' in self.channels and self.r_field_config:
            self.r_monitor = create_gaxi_monitor(
                dut, f"{title}_R", "", clock,
                field_config=self.r_field_config,
                is_slave=not is_slave_side,  # R channel direction is opposite
                multi_sig=True,
                signal_map=r_signal_map,
                optional_signal_map=r_optional_signal_map,
                log=log
            )
            self.r_monitor.add_callback(self._handle_r_transaction)
        else:
            self.r_monitor = None

        # Initialize transaction tracking
        self.write_transactions = {}  # Maps IDs to write transactions
        self.read_transactions = {}   # Maps IDs to read transactions

        # Callback for completed transactions
        self.write_callback = None
        self.read_callback = None

        self.log.info(f"AXI4Monitor '{title}' initialized")

    def set_write_callback(self, callback):
        """Set callback for completed write transactions"""
        self.write_callback = callback

    def set_read_callback(self, callback):
        """Set callback for completed read transactions"""
        self.read_callback = callback

    def _handle_aw_transaction(self, transaction):
        """Process Write Address (AW) channel transaction"""
        # Extract ID for tracking
        if not hasattr(transaction, 'awid'):
            self.log.error("AW transaction missing awid field")
            return

        id_value = transaction.awid

        # Validate protocol if enabled
        if self.check_protocol:
            valid, error_msg = transaction.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error (AW): {error_msg}")

        # Create or update transaction tracking
        if id_value not in self.write_transactions:
            self.write_transactions[id_value] = {
                'aw_transaction': transaction,
                'w_transactions': [],
                'b_transaction': None,
                'start_time': get_sim_time('ns'),
                'addresses': transaction.get_burst_addresses() if hasattr(transaction, 'get_burst_addresses') else [transaction.awaddr],
                'expected_beats': transaction.awlen + 1 if hasattr(transaction, 'awlen') else 1,
                'received_beats': 0,
                'complete': False
            }
        else:
            # Update existing transaction
            self.write_transactions[id_value]['aw_transaction'] = transaction

            # If addresses not yet calculated, do it now
            if 'addresses' not in self.write_transactions[id_value]:
                self.write_transactions[id_value]['addresses'] = transaction.get_burst_addresses() if hasattr(transaction, 'get_burst_addresses') else [transaction.awaddr]

            # If expected_beats not set, do it now
            if 'expected_beats' not in self.write_transactions[id_value]:
                self.write_transactions[id_value]['expected_beats'] = transaction.awlen + 1 if hasattr(transaction, 'awlen') else 1

        self.log.debug(f"Monitored write address: ID={id_value}, ADDR=0x{transaction.awaddr:X}, LEN={getattr(transaction, 'awlen', 0)}")

        # Check if transaction is now complete
        self._check_write_complete(id_value)

    def _handle_w_transaction(self, transaction):
        """Process Write Data (W) channel transaction"""
        # Find matching transaction by looking at all pending writes
        # Note: W transactions don't have ID, so we have to match them by order
        for id_value, tx_info in self.write_transactions.items():
            # Only consider transactions with AW but not complete
            if tx_info.get('aw_transaction') and tx_info['received_beats'] < tx_info['expected_beats']:
                # This is the next transaction to receive data
                w_transactions = tx_info.get('w_transactions', [])

                # Add this transaction
                w_transactions.append(transaction)
                tx_info['w_transactions'] = w_transactions
                tx_info['received_beats'] += 1

                # If this is wlast, mark data as complete
                if hasattr(transaction, 'wlast') and transaction.wlast == 1:
                    tx_info['w_complete'] = True

                # If all expected beats received, mark data as complete
                if tx_info['received_beats'] >= tx_info['expected_beats']:
                    tx_info['w_complete'] = True

                self.log.debug(f"Monitored write data: ID={id_value}, DATA=0x{transaction.wdata:X}, STRB=0x{transaction.wstrb:X}, LAST={getattr(transaction, 'wlast', 0)}")

                # Check if transaction is now complete
                self._check_write_complete(id_value)

                # Found a match, no need to check other IDs
                break

    def _handle_b_transaction(self, transaction):
        """Process Write Response (B) channel transaction"""
        # Extract ID for tracking
        if not hasattr(transaction, 'bid'):
            self.log.error("B transaction missing bid field")
            return

        id_value = transaction.bid

        # Validate protocol if enabled
        if self.check_protocol:
            valid, error_msg = transaction.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error (B): {error_msg}")

        # Create or update transaction tracking
        if id_value not in self.write_transactions:
            self.write_transactions[id_value] = {
                'b_transaction': transaction,
                'start_time': get_sim_time('ns')
            }
        else:
            # Update existing transaction
            self.write_transactions[id_value]['b_transaction'] = transaction

            # Mark as having response
            self.write_transactions[id_value]['b_complete'] = True

        self.log.debug(f"Monitored write response: ID={id_value}, RESP={transaction.bresp}")

        # Check if transaction is now complete
        self._check_write_complete(id_value)

    def _handle_ar_transaction(self, transaction):
        """Process Read Address (AR) channel transaction"""
        # Extract ID for tracking
        if not hasattr(transaction, 'arid'):
            self.log.error("AR transaction missing arid field")
            return

        id_value = transaction.arid

        # Validate protocol if enabled
        if self.check_protocol:
            valid, error_msg = transaction.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error (AR): {error_msg}")

        # Calculate addresses
        addresses = transaction.get_burst_addresses() if hasattr(transaction, 'get_burst_addresses') else [transaction.araddr]

        # Create or update transaction tracking
        if id_value not in self.read_transactions:
            self.read_transactions[id_value] = {
                'ar_transaction': transaction,
                'r_transactions': [],
                'start_time': get_sim_time('ns'),
                'addresses': addresses,
                'expected_beats': transaction.arlen + 1 if hasattr(transaction, 'arlen') else 1,
                'received_beats': 0,
                'complete': False
            }
        else:
            # Update existing transaction
            self.read_transactions[id_value]['ar_transaction'] = transaction

            # If addresses not yet calculated, do it now
            if 'addresses' not in self.read_transactions[id_value]:
                self.read_transactions[id_value]['addresses'] = addresses

            # If expected_beats not set, do it now
            if 'expected_beats' not in self.read_transactions[id_value]:
                self.read_transactions[id_value]['expected_beats'] = transaction.arlen + 1 if hasattr(transaction, 'arlen') else 1

        self.log.debug(f"Monitored read address: ID={id_value}, ADDR=0x{transaction.araddr:X}, LEN={getattr(transaction, 'arlen', 0)}")

    def _handle_r_transaction(self, transaction):
        """Process Read Data (R) channel transaction"""
        # Extract ID for tracking
        if not hasattr(transaction, 'rid'):
            self.log.error("R transaction missing rid field")
            return

        id_value = transaction.rid

        # Validate protocol if enabled
        if self.check_protocol:
            valid, error_msg = transaction.validate_axi4_protocol()
            if not valid:
                self.log.error(f"AXI4 protocol error (R): {error_msg}")

        # Create or update transaction tracking
        if id_value not in self.read_transactions:
            self.read_transactions[id_value] = {
                'r_transactions': [transaction],
                'start_time': get_sim_time('ns'),
                'received_beats': 1,
                'complete': transaction.rlast == 1 if hasattr(transaction, 'rlast') else True
            }
        else:
            # Update existing transaction
            r_transactions = self.read_transactions[id_value].get('r_transactions', [])
            r_transactions.append(transaction)
            self.read_transactions[id_value]['r_transactions'] = r_transactions

            # Update received beats
            self.read_transactions[id_value]['received_beats'] = len(r_transactions)

            # If this is rlast, mark as complete
            if hasattr(transaction, 'rlast') and transaction.rlast == 1:
                self.read_transactions[id_value]['r_complete'] = True

                # Mark transaction as complete
                self._check_read_complete(id_value)

        self.log.debug(f"Monitored read data: ID={id_value}, DATA=0x{transaction.rdata:X}, RESP={transaction.rresp}, LAST={getattr(transaction, 'rlast', 0)}")

    def _check_write_complete(self, id_value):
        """Check if a write transaction is complete and invoke callback if so"""
        if id_value in self.write_transactions:
            tx_info = self.write_transactions[id_value]

            # Check if all components are present and complete
            if (tx_info.get('aw_transaction') and
                tx_info.get('w_complete') and
                tx_info.get('b_complete') and
                not tx_info.get('complete', False)):

                # Mark as complete
                tx_info['complete'] = True
                tx_info['end_time'] = get_sim_time('ns')
                tx_info['duration'] = tx_info['end_time'] - tx_info['start_time']

                self.log.debug(f"Write transaction complete: ID={id_value}, " +
                                f"ADDR=0x{tx_info['aw_transaction'].awaddr:X}, " +
                                f"LEN={getattr(tx_info['aw_transaction'], 'awlen', 0)}, " +
                                f"RESP={tx_info['b_transaction'].bresp}")

                # Invoke callback if set
                if self.write_callback:
                    self.write_callback(id_value, tx_info)

    def _check_read_complete(self, id_value):
        """Check if a read transaction is complete and invoke callback if so"""
        if id_value in self.read_transactions:
            tx_info = self.read_transactions[id_value]

            # Check if both address and all data beats are present
            if (tx_info.get('ar_transaction') and
                tx_info.get('r_complete') and
                not tx_info.get('complete', False)):

                # Mark as complete
                tx_info['complete'] = True
                tx_info['end_time'] = get_sim_time('ns')
                tx_info['duration'] = tx_info['end_time'] - tx_info['start_time']

                # Extract data values for convenience
                tx_info['data'] = [r.rdata for r in tx_info.get('r_transactions', [])]

                self.log.debug(f"Read transaction complete: ID={id_value}, " +
                                f"ADDR=0x{tx_info['ar_transaction'].araddr:X}, " +
                                f"LEN={getattr(tx_info['ar_transaction'], 'arlen', 0)}, " +
                                f"DATA_COUNT={len(tx_info.get('r_transactions', []))}")

                # Invoke callback if set
                if self.read_callback:
                    self.read_callback(id_value, tx_info)
        