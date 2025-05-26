"""
Base test class for AXI Error Monitor.

This module provides a base test class with common utilities used by all
specialized test classes for the AXI Error Monitor Base module.
"""
import cocotb
from cocotb.utils import get_sim_time
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


class AXIErrorMonBaseTest:
    """
    Base class for AXI Error Monitor tests.
    Provides common utilities for all test classes.
    """

    def __init__(self, tb):
        """
        Initialize with a reference to the testbench

        Args:
            tb: Reference to the AXIErrorMonitorTB wrapper class
        """
        self.tb = tb
        self.dut = tb.dut
        self.log = tb.log
        self.is_read = tb.is_read
        self.is_axi = tb.is_axi

        # Transaction tracking
        self.active_transactions = {}
        self.completed_transactions = []

        # New: Per-channel state tracking
        self.channel_states = [{'busy': False, 'last_tx_time': 0} for _ in range(self.tb.channels)]

        # New: Transaction queue and processor state
        self.transaction_queue = []
        self.queue_processor_active = False

        # New: Expected errors tracking
        self.expected_errors = []

    # Helper method to determine channel index from ID
    def get_channel_idx(self, id_value):
        """Get channel index from transaction ID"""
        return id_value % self.tb.channels if self.tb.is_axi else 0

    async def drive_basic_transaction(self,
                                    addr=0x1000,
                                    id_value=0,
                                    resp_value=0,  # 0=OKAY, 2=SLVERR, etc.
                                    control_ready=False,  # If True, use ready control parameters
                                    addr_ready_delay=0,  # Cycles to delay addr_ready
                                    data_ready_delay=0,  # Cycles to delay data_ready
                                    resp_ready_delay=0,  # Cycles to delay resp_ready
                                    intrbus_ready_speed='fixed',  # Speed for intrbus ready signal
                                    pipeline_phases=True,  # If True, enable AXI parallelism for AW/W channels
                                    wait_for_completion=True,    # If True, wait for all phases to complete
                                    wait_prev_completion=True):    # Wait for previous transactions on this channel
        # sourcery skip: hoist-similar-statement-from-if, hoist-statement-from-if
        """
        Drive a complete AXI transaction through the DUT with full phase control.

        This method drives all phases of an AXI transaction (address, data, response)
        with configurable control over ready signal timing for each phase.
        Supports AXI parallelism where AW and W channels can operate simultaneously.

        Updated to handle the single shared FIFO in write mode.

        Args:
            addr: Address for the transaction
            id_value: ID for the transaction
            resp_value: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            control_ready: If True, use the ready delay parameters
            addr_ready_delay: Cycles to delay address ready
            data_ready_delay: Cycles to delay data ready
            resp_ready_delay: Cycles to delay response ready
            intrbus_ready_speed: Speed setting for intrbus ready ('fixed', 'slow_consumer', etc.)
            pipeline_phases: If True, enable AXI parallelism (AW/W in same cycle)
            wait_for_completion: If True, wait for all phases to complete
            wait_prev_completion: If True, wait for previous transactions on same channel

        Returns:
            Dict with transaction details and status
        """
        # Calculate channel index from ID
        ch_idx = self.get_channel_idx(id_value)

        # Set intrbus ready speed using the slave's randomizer
        if intrbus_ready_speed in self.tb.randomizer_configs:
            self.tb.intrbus_slave.set_randomizer(
                FlexRandomizer(self.tb.randomizer_configs[intrbus_ready_speed]))

        # New: For write mode, check if we need to wait for the shared FIFO to have space
        if not self.tb.is_read and wait_prev_completion:
            # Wait for master to be ready before starting transaction
            while self.tb.addr_master.transfer_busy:
                await self.tb.wait_clocks('aclk', 1)

            # Check if the block_ready signal is asserted (shared FIFO full)
            if self.dut.o_block_ready.value:
                self.log.info(f"Waiting for block_ready to deassert before starting transaction{self.tb.get_time_ns_str()}")
                timeout_count = 0
                max_timeout = 100
                while self.dut.o_block_ready.value and timeout_count < max_timeout:
                    await self.tb.wait_clocks('aclk', 1)
                    timeout_count += 1

                if timeout_count >= max_timeout:
                    self.log.error(f"Timeout waiting for block_ready to deassert{self.tb.get_time_ns_str()}")
                    return {
                        'addr': addr,
                        'id': id_value,
                        'resp': resp_value,
                        'start_time': get_sim_time('ns'),
                        'end_time': get_sim_time('ns'),
                        'addr_phase_complete': False,
                        'data_phase_complete': False,
                        'resp_phase_complete': False,
                        'completed': False,
                        'error': "Timeout waiting for block_ready to deassert",
                        'channel': ch_idx,
                    }
        # Wait for previous transactions on this channel to complete if requested
        if wait_prev_completion:
            await self._wait_for_channel_ready(ch_idx)

        # Mark channel as busy
        self.channel_states[ch_idx]['busy'] = True

        # Create transaction record
        transaction = {
            'addr': addr,
            'id': id_value,
            'resp': resp_value,
            'start_time': get_sim_time('ns'),
            'addr_phase_complete': False,
            'data_phase_complete': False,
            'resp_phase_complete': False,
            'completed': False,
            'error': None,
            'channel': ch_idx
        }

        # Store in active transactions
        tx_id = f"{id_value}_{addr}_{get_sim_time('ns')}"
        self.active_transactions[tx_id] = transaction

        self.log.info(f"Starting transaction: addr=0x{addr:X}, id={id_value}, resp={resp_value}, pipeline_phases={pipeline_phases}{self.tb.get_time_ns_str()}")

        # Configure ready signals using the ReadySignalController
        if control_ready:
            # Configure delayed ready signals
            if addr_ready_delay > 0:
                await self.tb.ready_ctrl.delay_addr_ready(addr_ready_delay)
            else:
                self.tb.ready_ctrl.set_addr_ready(1)

            if data_ready_delay > 0:
                await self.tb.ready_ctrl.delay_data_ready(data_ready_delay)
            else:
                self.tb.ready_ctrl.set_data_ready(1)

            if not self.tb.is_read and resp_ready_delay > 0:
                await self.tb.ready_ctrl.delay_resp_ready(resp_ready_delay)
            else:
                self.tb.ready_ctrl.set_resp_ready(1)
        else:
            # Default settings
            self.tb.ready_ctrl.set_addr_ready(1)
            self.tb.ready_ctrl.set_data_ready(1)
            self.tb.ready_ctrl.set_resp_ready(1)

        # Create packets for all phases
        addr_packet = GAXIPacket(self.tb.addr_field_config)
        addr_packet.addr = addr
        addr_packet.id = id_value

        # Set AXI-specific fields if needed
        if self.is_axi:
            addr_packet.len = 0  # Single transfer (0 means 1 beat)
            addr_packet.size = 2  # 4 bytes (log2 of 4)
            addr_packet.burst = 1  # INCR

        data_packet = None
        if self.is_read:
            # For read transactions, we create a data packet for ID, last, resp
            data_packet = GAXIPacket(self.tb.data_field_config)
            data_packet.id = id_value
            data_packet.last = 1  # Single transfer
            data_packet.resp = resp_value  # Response code for read data
        else:
            # For write transactions, we create a data packet for last signal
            data_packet = GAXIPacket(self.tb.data_field_config)
            data_packet.last = 1  # Single transfer
            # Note: no data value is needed as it's just for monitoring

        resp_packet = None
        if not self.tb.is_read:  # Only create response packet for write transactions
            resp_packet = GAXIPacket(self.tb.resp_field_config)
            resp_packet.id = id_value
            resp_packet.resp = resp_value

        # Start address phase
        addr_task = cocotb.start_soon(self._complete_addr_phase(tx_id, addr_packet))

        # Handle phases according to transaction type and pipelining settings
        if self.is_read:
            # For read transactions, data is a response so no parallelism
            # Wait for address phase to complete before preparing for data
            await addr_task

            # Launch data phase
            data_task = cocotb.start_soon(self._complete_data_phase(tx_id, data_packet))

        elif pipeline_phases:
            # Special handling for write mode with shared FIFO
            if not self.tb.is_read and not self.dut.o_block_ready.value:
                # True AXI parallelism - launch data phase immediately in parallel with address
                data_task = cocotb.start_soon(self._complete_data_phase(tx_id, data_packet))

                # New: Create futures for address and data completion
                addr_phase_done = cocotb.start_soon(self._wait_for_phase_completion(tx_id, 'addr_phase_complete'))
                data_phase_done = cocotb.start_soon(self._wait_for_phase_completion(tx_id, 'data_phase_complete'))

                # New: Wait for both to complete more efficiently
                while not (self.active_transactions[tx_id]['addr_phase_complete'] and
                        self.active_transactions[tx_id]['data_phase_complete']):
                    await self.tb.wait_clocks('aclk', 1)

                # Now start response phase
                resp_task = cocotb.start_soon(self._complete_resp_phase(tx_id, resp_packet, wait_for_data=False))
            else:
                # If block_ready is asserted, we need to be more cautious
                # Wait for address phase to complete first
                await addr_task

                # Then launch data phase
                data_task = cocotb.start_soon(self._complete_data_phase(tx_id, data_packet))

                # Wait for data phase to complete
                await data_task

                # Then launch response phase
                resp_task = cocotb.start_soon(self._complete_resp_phase(tx_id, resp_packet, wait_for_data=False))

        else:
            # Sequential behavior - wait for address phase to complete first
            await addr_task

            # Then launch data phase
            data_task = cocotb.start_soon(self._complete_data_phase(tx_id, data_packet))

            # Wait for data phase to complete
            await data_task

            # Then launch response phase
            resp_task = cocotb.start_soon(self._complete_resp_phase(tx_id, resp_packet, wait_for_data=False))

        # Wait for completion if requested
        if wait_for_completion:
            # New: Adaptive timeout based on test conditions and delays
            timeout_multiplier = 2  # Base multiplier
            if addr_ready_delay > 0:
                timeout_multiplier += addr_ready_delay // 10
            if data_ready_delay > 0:
                timeout_multiplier += data_ready_delay // 10
            if resp_ready_delay > 0:
                timeout_multiplier += resp_ready_delay // 10

            timeout_limit = 100 * timeout_multiplier  # Scale based on complexity

            # Simple timeout mechanism
            timeout_count = 0

            while not transaction['completed'] and timeout_count < timeout_limit:
                await self.tb.wait_clocks('aclk', 1)
                timeout_count += 1

                # Check for completion
                if self.tb.is_read:
                    transaction['completed'] = transaction['addr_phase_complete'] and transaction['data_phase_complete']
                else:
                    transaction['completed'] = transaction['addr_phase_complete'] and \
                                                    transaction['data_phase_complete'] and \
                                                    transaction['resp_phase_complete']

            # Check for timeout
            if timeout_count >= timeout_limit:
                transaction['error'] = "Transaction timed out"
                self.log.error(f"Transaction timed out: addr=0x{addr:X}, id={id_value}{self.tb.get_time_ns_str()}")

                # Mark channel as free even on timeout
                self.channel_states[ch_idx]['busy'] = False
                self.channel_states[ch_idx]['last_tx_time'] = get_sim_time('ns')
                return transaction

            # Transaction completed
            transaction['end_time'] = get_sim_time('ns')
            self.log.info(f"Transaction completed: addr=0x{addr:X}, id={id_value}{self.tb.get_time_ns_str()}")

            # Move to completed list
            self.completed_transactions.append(transaction)
            del self.active_transactions[tx_id]

        # Reset intrbus ready speed to fixed (normal)
        self.tb.intrbus_slave.set_randomizer(FlexRandomizer(self.tb.randomizer_configs['fixed']))

        # Mark channel as free
        self.channel_states[ch_idx]['busy'] = False
        self.channel_states[ch_idx]['last_tx_time'] = get_sim_time('ns')

        return transaction

    async def _wait_for_channel_ready(self, ch_idx):
        """
        Wait for a channel to be ready (not busy)

        Args:
            ch_idx: Channel index to wait for
        """
        timeout_count = 0
        timeout_limit = 10000  # Maximum cycles to wait

        while self.channel_states[ch_idx]['busy'] and timeout_count < timeout_limit:
            await self.tb.wait_clocks('aclk', 1)
            timeout_count += 1

        if timeout_count >= timeout_limit:
            self.log.error(f"Channel {ch_idx} never became ready{self.tb.get_time_ns_str()}")
            # Force channel to ready state to prevent deadlock
            self.channel_states[ch_idx]['busy'] = False

    async def _complete_addr_phase(self, tx_id, addr_packet):
        """
        Complete the address phase of a transaction

        Args:
            tx_id: Transaction ID to update
            addr_packet: Address packet to send
        """
        if tx_id in self.active_transactions:
            transaction = self.active_transactions[tx_id]

            # Send address packet
            await self.tb.addr_master.send(addr_packet)

        # Mark address phase as complete
        if tx_id in self.active_transactions:
            self.active_transactions[tx_id]['addr_phase_complete'] = True
            self.log.debug(f"Address phase completed for tx {tx_id}{self.tb.get_time_ns_str()}")

    async def _complete_data_phase(self, tx_id, data_packet):
        """
        Complete the data phase of a transaction

        Args:
            tx_id: Transaction ID to update
            data_packet: Data packet to send
        """
        # New: Wait for master to be ready instead of checking transfer_busy
        while self.tb.addr_master.transfer_busy:
            await self.tb.wait_clocks('aclk', 1)

        if tx_id in self.active_transactions:
            transaction = self.active_transactions[tx_id]

            # Use the data master to send the packet for both read and write modes
            await self.tb.data_master.send(data_packet)

        # Mark data phase as complete
        if tx_id in self.active_transactions:
            self.active_transactions[tx_id]['data_phase_complete'] = True
            self.log.debug(f"Data phase completed for tx {tx_id}{self.tb.get_time_ns_str()}")

    async def _wait_for_phase_completion(self, tx_id, phase_name):
        """
        Wait for a specific phase of a transaction to complete

        Args:
            tx_id: Transaction ID to monitor
            phase_name: Name of the phase to wait for ('addr_phase_complete', etc.)
        """
        # New: Wait for data master to be ready instead of checking transfer_busy
        while self.tb.data_master.transfer_busy:
            await self.tb.wait_clocks('aclk', 1)

        if tx_id not in self.active_transactions:
            return

        transaction = self.active_transactions[tx_id]

        # Wait for the phase to complete
        timeout_count = 0
        timeout_limit = 500  # Maximum cycles to wait

        while not transaction.get(phase_name, False) and timeout_count < timeout_limit:
            await self.tb.wait_clocks('aclk', 1)
            timeout_count += 1

            # Check if transaction is still active
            if tx_id not in self.active_transactions:
                return

            transaction = self.active_transactions[tx_id]

        if timeout_count >= timeout_limit:
            self.log.error(f"{phase_name} timed out for tx {tx_id}{self.tb.get_time_ns_str()}")

    async def _complete_resp_phase(self, tx_id, resp_packet, wait_for_data=True):
        """
        Complete the response phase of a transaction (write only)

        Args:
            tx_id: Transaction ID to update
            resp_packet: Response packet to send
            wait_for_data: If True, wait for data phase to complete first
        """
        # Only applicable for write transactions
        if self.tb.is_read:
            return

        if tx_id in self.active_transactions:
            transaction = self.active_transactions[tx_id]

            # Wait for data phase to complete if requested
            if wait_for_data:
                # Wait for data phase completion
                while tx_id in self.active_transactions and not self.active_transactions[tx_id]['data_phase_complete']:
                    await self.tb.wait_clocks('aclk', 1)

                # Check if transaction still exists
                if tx_id not in self.active_transactions:
                    return

                if not self.active_transactions[tx_id]['data_phase_complete']:
                    transaction['error'] = "Data phase timed out"
                    self.log.error(f"Data phase timed out for tx {tx_id}{self.tb.get_time_ns_str()}")
                    return

            # Send response packet
            await self.tb.resp_master.send(resp_packet)

        # Mark response phase as complete
        if tx_id in self.active_transactions:
            self.active_transactions[tx_id]['resp_phase_complete'] = True
            self.log.debug(f"Response phase completed for tx {tx_id}{self.tb.get_time_ns_str()}")

            # Check if this completes the transaction
            if (self.active_transactions[tx_id]['addr_phase_complete'] and
                self.active_transactions[tx_id]['data_phase_complete'] and
                self.active_transactions[tx_id]['resp_phase_complete']):
                self.active_transactions[tx_id]['completed'] = True
                self.active_transactions[tx_id]['end_time'] = get_sim_time('ns')

    async def queue_transaction(self, tx_params):
        """
        Queue a transaction and process in order

        Args:
            tx_params: Dictionary of parameters for drive_basic_transaction

        Returns:
            Transaction ID
        """
        # Add to queue
        tx_id = len(self.transaction_queue)
        self.transaction_queue.append((tx_id, tx_params))

        # Process queue in order
        if not self.queue_processor_active:
            self.queue_processor_active = True
            cocotb.start_soon(self._process_transaction_queue())

        return tx_id

    async def _process_transaction_queue(self):
        """Process transactions from queue in order"""
        while self.transaction_queue:
            tx_id, tx_params = self.transaction_queue.pop(0)
            await self.drive_basic_transaction(**tx_params)
            # Add small delay between transactions
            await self.tb.wait_clocks('aclk', 2)
        self.queue_processor_active = False

    async def drive_error_scenario(self,
                                error_type,
                                addr=0x2000,
                                id_value=1,
                                resp_value=0,
                                intrbus_ready_speed='fixed'):
        """
        Drive a transaction that will trigger a specific error with improved waiting logic

        Updated to handle the single shared FIFO in write mode.

        Args:
            error_type: Type of error to generate ('addr_timeout', 'data_timeout', 'resp_timeout', or 'resp_error')
            addr: Address for the transaction
            id_value: ID for the transaction
            resp_value: Response code (overridden for resp_error)
            intrbus_ready_speed: Speed setting for intrbus ready ('fixed', 'slow_consumer', etc.)

        Returns:
            True if error was detected, False otherwise
        """
        self.log.info("="*80)
        self.log.info(f"Driving error scenario: type={error_type}, addr=0x{addr:X}, id={id_value}{self.tb.get_time_ns_str()}")
        self.log.info("="*80)

        # Set intrbus ready speed using the slave's randomizer
        if intrbus_ready_speed in self.tb.randomizer_configs:
            self.tb.intrbus_slave.set_randomizer(
                FlexRandomizer(self.tb.randomizer_configs[intrbus_ready_speed]))

        # Log expected error for debug
        expected_error_bit = self._get_expected_error_bit(error_type)
        self.log.info(f"Expecting {error_type} (0x{expected_error_bit:X}) error for addr=0x{addr:X}, id={id_value}{self.tb.get_time_ns_str()}")

        # Clear any previous errors
        initial_events_count = len(self.tb.intrbus_events)
        self.tb.errors_detected = []
        self.expected_errors = []

        # Clear any forced low settings
        self.tb.ready_ctrl.force_addr_ready_low(False)
        self.tb.ready_ctrl.force_data_ready_low(False)
        self.tb.ready_ctrl.force_resp_ready_low(False)

        # Ensure error FIFO ready is high to receive errors
        self.tb.error_slave.set_randomizer(FlexRandomizer(self.tb.randomizer_configs['fixed']))

        await self.tb.wait_clocks('aclk', 5)

        # Create transaction record
        transaction = {
            'addr': addr,
            'id': id_value,
            'resp': resp_value,
            'error_type': error_type,
            'start_time': get_sim_time('ns'),
            'completed': False,
            'error_detected': False
        }

        # Store transaction for tracking
        self.tb.axi_transactions.append(transaction)

        # Configure different error scenarios with specific waiting logic
        if error_type == 'addr_timeout':
            self.log.info(f"Starting address timeout scenario{self.tb.get_time_ns_str()}")

            # Force addr_ready low to ensure timeout
            self.tb.ready_ctrl.force_addr_ready_low(True)

            # Start address phase and hold valid high
            addr_packet = GAXIPacket(self.tb.addr_field_config)
            addr_packet.addr = addr
            addr_packet.id = id_value

            # Set AXI-specific fields if needed
            if self.is_axi:
                addr_packet.len = 0  # Single transfer (0 means 1 beat)
                addr_packet.size = 2  # 4 bytes (log2 of 4)
                addr_packet.burst = 1  # INCR

            # Send the address packet (won't complete due to ready=0)
            await self.tb.addr_master.send(addr_packet)

            # Wait for timeout to occur (timeout value plus margin)
            timeout_wait = self.tb.timeout_addr + 50
            self.log.info(f"Waiting for error detection{self.tb.get_time_ns_str()}")
            await self.tb.wait_clocks('aclk', timeout_wait)

            # Check for error detection with extended time
            error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)
            if not error_detected:
                # Wait longer if not detected yet - some implementations might need more time
                await self.tb.wait_clocks('aclk', 50)
                error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)

            # Release forced ready signal regardless of test outcome
            self.tb.ready_ctrl.force_addr_ready_low(False)

        elif error_type == 'data_timeout':
            self.log.info(f"Starting data timeout scenario{self.tb.get_time_ns_str()}")

            # For write mode, we need to make sure we have room in the shared FIFO
            if not self.tb.is_read:
                # Make sure we start with a clean state
                await self.reset_and_setup_for_test()

            # Let address phase complete normally
            self.tb.ready_ctrl.set_addr_ready(1)

            # Start with a normal transaction
            addr_packet = GAXIPacket(self.tb.addr_field_config)
            addr_packet.addr = addr
            addr_packet.id = id_value

            # Set AXI-specific fields if needed
            if self.is_axi:
                addr_packet.len = 0  # Single transfer (0 means 1 beat)
                addr_packet.size = 2  # 4 bytes (log2 of 4)
                addr_packet.burst = 1  # INCR

            await self.tb.addr_master.send(addr_packet)

            # Wait for address phase to complete
            while self.tb.addr_master.transfer_busy:
                await self.tb.wait_clocks('aclk', 1)
            await self.tb.wait_clocks('aclk', 5)

            # Force data_ready low to create timeout
            self.tb.ready_ctrl.force_data_ready_low(True)

            # Send data packet (which will timeout waiting for ready)
            data_packet = GAXIPacket(self.tb.data_field_config)
            if self.is_read:
                data_packet.id = id_value
                data_packet.last = 1
                data_packet.resp = resp_value
            else:
                data_packet.last = 1  # Single beat

            # Send the data packet (won't complete due to ready=0)
            await self.tb.data_master.send(data_packet)

            # Wait for timeout to occur (timeout value plus margin)
            timeout_wait = self.tb.timeout_data + 50
            self.log.info(f"Waiting for error detection{self.tb.get_time_ns_str()}")
            await self.tb.wait_clocks('aclk', timeout_wait)

            # Check for error detection with extended time
            error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)
            if not error_detected:
                # Wait longer if not detected yet
                await self.tb.wait_clocks('aclk', 50)
                error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)

            # Release forced ready signal regardless of outcome
            self.tb.ready_ctrl.force_data_ready_low(False)

        elif error_type == 'resp_timeout':
            if not self.tb.is_read:
                self.log.info(f"Starting response timeout scenario{self.tb.get_time_ns_str()}")

                # For write mode, we need to make sure we have room in the shared FIFO
                # Make sure we start with a clean state
                await self.reset_and_setup_for_test()

                # Let address and data phases complete normally
                self.tb.ready_ctrl.set_addr_ready(1)
                self.tb.ready_ctrl.set_data_ready(1)

                # Start with a normal transaction
                addr_packet = GAXIPacket(self.tb.addr_field_config)
                addr_packet.addr = addr
                addr_packet.id = id_value

                # Set AXI-specific fields if needed
                if self.is_axi:
                    addr_packet.len = 0  # Single transfer (0 means 1 beat)
                    addr_packet.size = 2  # 4 bytes (log2 of 4)
                    addr_packet.burst = 1  # INCR

                await self.tb.addr_master.send(addr_packet)

                # Wait for address phase to complete
                while self.tb.addr_master.transfer_busy:
                    await self.tb.wait_clocks('aclk', 1)
                await self.tb.wait_clocks('aclk', 5)

                # Send data packet
                data_packet = GAXIPacket(self.tb.data_field_config)
                data_packet.last = 1  # Single beat

                await self.tb.data_master.send(data_packet)

                # Wait for data phase to complete
                while self.tb.data_master.transfer_busy:
                    await self.tb.wait_clocks('aclk', 1)
                await self.tb.wait_clocks('aclk', 5)

                # Force resp_ready low to create timeout
                self.tb.ready_ctrl.force_resp_ready_low(True)

                # Send response packet (which will timeout waiting for ready)
                resp_packet = GAXIPacket(self.tb.resp_field_config)
                resp_packet.id = id_value
                resp_packet.resp = resp_value

                await self.tb.resp_master.send(resp_packet)

                # Wait for timeout to occur (timeout value plus margin)
                timeout_wait = self.tb.timeout_resp + 50
                self.log.info(f"Waiting for error detection{self.tb.get_time_ns_str()}")
                await self.tb.wait_clocks('aclk', timeout_wait)

                # Check for error with extended time
                error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)
                if not error_detected:
                    # Wait longer if not detected yet
                    await self.tb.wait_clocks('aclk', 50)
                    error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)

                # Release forced ready signal regardless of outcome
                self.tb.ready_ctrl.force_resp_ready_low(False)
            else:
                self.log.warning(f"Response timeout test not applicable for read mode{self.tb.get_time_ns_str()}")
                return True  # Skip this test for read mode

        elif error_type == 'resp_error':
            self.log.info(f"Starting response error scenario{self.tb.get_time_ns_str()}")

            # For write mode, make sure we have a clean state
            if not self.tb.is_read:
                await self.reset_and_setup_for_test()

            error_resp = resp_value if resp_value in [2, 3] else 2
            # Set all ready signals high for maximum throughput
            self.tb.ready_ctrl.force_resp_ready_low(False)
            self.tb.ready_ctrl.set_addr_ready(1)
            self.tb.ready_ctrl.set_data_ready(1)
            self.tb.ready_ctrl.set_resp_ready(1)

            # Different handling for read vs. write mode
            if self.tb.is_read:
                # For read, we need to complete address phase then send data with error response
                self.log.info(f"Sending read address packet{self.tb.get_time_ns_str()}")

                # Start with a normal address transaction
                addr_packet = GAXIPacket(self.tb.addr_field_config)
                addr_packet.addr = addr
                addr_packet.id = id_value

                # Set AXI-specific fields if needed
                if self.is_axi:
                    addr_packet.len = 0  # Single transfer (0 means 1 beat)
                    addr_packet.size = 2  # 4 bytes (log2 of 4)
                    addr_packet.burst = 1  # INCR

                await self.tb.addr_master.send(addr_packet)

                # Wait for address phase to complete - shorter wait
                while self.tb.addr_master.transfer_busy:
                    await self.tb.wait_clocks('aclk', 1)

                self.log.info(f"Sending read data packet with error response={error_resp}{self.tb.get_time_ns_str()}")

                # Send data packet with error response immediately after address completes
                data_packet = GAXIPacket(self.tb.data_field_config)
                data_packet.id = id_value
                data_packet.last = 1
                data_packet.resp = error_resp  # Error response
                await self.tb.data_master.send(data_packet)

                # Only a brief wait for data phase to complete
                while self.tb.data_master.transfer_busy:
                    await self.tb.wait_clocks('aclk', 1)

            else:
                # For write, we need to complete address and data phases then send error response
                self.log.info(f"Sending write address packet{self.tb.get_time_ns_str()}")

                # Start with a normal address transaction
                addr_packet = GAXIPacket(self.tb.addr_field_config)
                addr_packet.addr = addr
                addr_packet.id = id_value

                # Set AXI-specific fields if needed
                if self.is_axi:
                    addr_packet.len = 0  # Single transfer (0 means 1 beat)
                    addr_packet.size = 2  # 4 bytes (log2 of 4)
                    addr_packet.burst = 1  # INCR

                await self.tb.addr_master.send(addr_packet)

                # Wait for address phase to complete - shorter wait
                while self.tb.addr_master.transfer_busy:
                    await self.tb.wait_clocks('aclk', 1)

                self.log.info(f"Sending write data packet{self.tb.get_time_ns_str()}")

                # Send data packet immediately after address completes
                data_packet = GAXIPacket(self.tb.data_field_config)
                data_packet.last = 1  # Last beat

                await self.tb.data_master.send(data_packet)

                # Only a brief wait for data phase to complete
                while self.tb.data_master.transfer_busy:
                    await self.tb.wait_clocks('aclk', 1)

                self.log.info(f"Sending write response packet with error response={error_resp}{self.tb.get_time_ns_str()}")

                # Send response packet with error response immediately after data completes
                resp_packet = GAXIPacket(self.tb.resp_field_config)
                resp_packet.id = id_value
                resp_packet.resp = error_resp  # Error response
                await self.tb.resp_master.send(resp_packet)

                # Only a brief wait for response phase to complete
                while self.tb.resp_master.transfer_busy:
                    await self.tb.wait_clocks('aclk', 1)

            # Wait for error to be detected - shorter initial wait
            self.log.info(f"Waiting for error detection{self.tb.get_time_ns_str()}")
            await self.tb.wait_clocks('aclk', 20)

            # Check for error detection
            error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)
            if not error_detected:
                # Wait a bit longer if not detected yet, but not excessively
                self.log.info(f"No error detected yet, waiting a bit longer{self.tb.get_time_ns_str()}")
                await self.tb.wait_clocks('aclk', 30)
                error_detected = self._check_for_expected_error(initial_events_count, error_type, id_value, addr)
