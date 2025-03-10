"""Enhanced Generic AXI Style Master/Slave/Monitor with Transaction Callbacks"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from Components.gaxi_components import GAXIMaster, GAXISlave, GAXIMonitor


class EnhancedGAXIMaster(GAXIMaster):
    """
    Enhanced Master driver for GAXI transactions with transaction callbacks.
    Provides callbacks for when transactions are sent and completed.
    """
    def __init__(self, *args, **kwargs):
        # Extract callbacks before passing to parent
        self.pre_send_callback = kwargs.pop('pre_send_callback', None)
        self.post_send_callback = kwargs.pop('post_send_callback', None)
        
        # Initialize the parent class
        super().__init__(*args, **kwargs)
        
        # Initialize transaction ID tracking
        self.transaction_id_counter = 0
        self.pending_transactions = {}

    async def _driver_send(self, transaction, sync=True, hold=False, **kwargs):
        """
        Enhanced send method with pre-send callback.
        
        Args:
            transaction: The transaction to send
            sync: Whether to synchronize with the clock
            hold: Whether to hold off starting a new transmit pipeline
            **kwargs: Additional arguments
        """
        # Assign transaction ID if not already present
        if not hasattr(transaction, 'transaction_id'):
            transaction.transaction_id = self.transaction_id_counter
            self.transaction_id_counter += 1
        
        # Store in pending transactions
        self.pending_transactions[transaction.transaction_id] = transaction
            
        # Call pre-send callback if defined
        if self.pre_send_callback:
            await self.pre_send_callback(transaction)
            
        # Call the parent method to perform the actual send
        await super()._driver_send(transaction, sync, hold, **kwargs)

    async def _xmit_phase1(self):
        """Handles the first phase of a GAXI transaction.

        This method retrieves a transaction from the queue, applies any
        configured delays, and asserts the valid signal with the transaction data.
        """
        # Get next transaction from the queue
        transaction = self.transmit_queue.popleft()
        transaction.start_time = get_sim_time('ns')
        self.log.debug(f"Master({self.title}) Processing transaction, remaining: "
                        f"{len(self.transmit_queue)} at {transaction.start_time}ns\n"
                        f"transaction={transaction.formatted(compact=True)}")

        # Apply any configured delay before asserting valid
        delay_dict = self.randomizer.set_constrained_random()
        valid_delay = delay_dict.get('valid_delay', 0)
        if valid_delay > 0:
            self.log.debug(f"Master({self.title}) Delaying valid assertion for {valid_delay} cycles")
            # Deassert valid during the wait period to prevent early handshake
            self.bus.i_wr_valid.value = 0
            self.bus.i_wr_data.value = 0
            await self.wait_cycles(valid_delay)

        # Assert valid for this transaction
        self.bus.i_wr_valid.value = 1
        # Drive the next data on the bus
        fifo_data = transaction.pack_for_fifo()
        if 'data' in fifo_data:
            self.bus.i_wr_data.value = fifo_data['data']
        self.log.debug(f"Master({self.title}): Asserting i_wr_valid with data {self.bus.i_wr_data.value}")

        return transaction

    async def _transmit_pipeline(self):
        """
        Enhanced pipeline for transmitting transactions with post-send callback.
        """
        self.log.debug(f'Master({self.title}): Transmit pipeline started, queue length: {len(self.transmit_queue)}')
        self.transfer_busy = True

        while len(self.transmit_queue):

            transaction = await self._xmit_phase1()

            # Wait for the DUT to assert o_wr_ready (handshake completion)
            timeout_counter = 0
            while not self.bus.o_wr_ready.value:
                await FallingEdge(self.clock)
                timeout_counter += 1
                if timeout_counter >= self.timeout_cycles:
                    self.log.error(f"Master({self.title}) TIMEOUT waiting for ready after {self.timeout_cycles} cycles")
                    # Stop driving if timeout (prevent hang)
                    self.bus.i_wr_valid.value = 0
                    self.bus.i_wr_data.value = 0
                    self.transfer_busy = False
                    
                    # Remove from pending transactions
                    if hasattr(transaction, 'transaction_id'):
                        self.pending_transactions.pop(transaction.transaction_id, None)
                    return

            # Handshake occurred – capture completion time
            await RisingEdge(self.clock)
            current_time_ns = get_sim_time('ns')
            self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                            f"{transaction.formatted(compact=True)}")
            transaction.end_time = current_time_ns
            self.sent_queue.append(transaction)
            
            # Call post-send callback if defined
            if self.post_send_callback and hasattr(transaction, 'transaction_id'):
                # Remove from pending transactions
                if transaction.transaction_id in self.pending_transactions:
                    await self.post_send_callback(self.pending_transactions.pop(transaction.transaction_id))
                else:
                    await self.post_send_callback(transaction)

            # If more data is queued, pre-load next data for continuous transfer
            if len(self.transmit_queue) > 0:
                next_trans = self.transmit_queue[0]
                next_fifo = next_trans.pack_for_fifo()
                if 'data' in next_fifo:
                    self.bus.i_wr_data.value = next_fifo['data']
                # (Keep i_wr_valid asserted for pipelining)
            else:
                # No more transactions – deassert valid
                self.bus.i_wr_valid.value = 0
                self.bus.i_wr_data.value = 0

            # Wait for next clock edge before processing subsequent transactions
            await RisingEdge(self.clock)

        self.log.debug(f"Master({self.title}) Transmit pipeline completed")
        self.transfer_busy = False
        self.transmit_coroutine = None
        # Ensure signals are deasserted at the end
        self.bus.i_wr_valid.value = 0
        self.bus.i_wr_data.value = 0


class EnhancedGAXISlave(GAXISlave):
    """
    Enhanced Slave driver for GAXI transactions with transaction callbacks.
    Provides callbacks for when transactions are received.
    """
    def __init__(self, *args, **kwargs):
        # Extract callbacks before passing to parent
        self.transaction_received_callback = kwargs.pop('transaction_received_callback', None)
        
        # Initialize the parent class
        super().__init__(*args, **kwargs)
        
        # Initialize transaction tracking
        self.transaction_id_counter = 0
        self.received_transactions = {}  # Store processed transactions by ID

    async def _monitor_recv(self):
        """
        Enhanced monitor for incoming transactions with callbacks.
        Supports all the same modes as the parent class.
        """
        try:
            last_packet = None
            last_xfer = False
            while True:
                # Wait a brief moment for signal stability
                await Timer(200, units='ps')

                current_time = get_sim_time('ns')
                # Check if last transfer
                if last_xfer:
                    packet = last_packet
                    data_val = int(self.bus.o_rd_data.value)
                    self._finish_packet(current_time, packet, data_val)
                    
                    # Clear last transfer data
                    last_xfer = False
                    last_packet = None

                # Determine ready delay for this cycle
                delay_cfg = self.randomizer.set_constrained_random()
                ready_delay = delay_cfg.get('ready_delay', 0)
                if ready_delay > 0:
                    self.log.debug(f"Slave({self.title}) Delaying ready assertion for {ready_delay} cycles")
                    self.bus.i_rd_ready.value = 0
                    await self.wait_cycles(ready_delay)
                # Assert ready to accept data
                self.bus.i_rd_ready.value = 1

                # Wait for a falling edge to sample o_rd_valid (allow combinatorial settle)
                await FallingEdge(self.clock)
                if self.bus.o_rd_valid.value == 1:
                    # Create the packet
                    packet = self.packet_class(self.field_config)
                    packet.start_time = current_time
                    
                    # Assign transaction ID
                    packet.transaction_id = self.transaction_id_counter
                    self.transaction_id_counter += 1

                    if self.mode != 'fifo_flop':
                        # Immediate capture (normal and mux modes)
                        # Select appropriate data signal based on mode
                        if self.mode == 'fifo_mux' and hasattr(self.bus, 'ow_rd_data'):
                            data_val = int(self.bus.ow_rd_data.value)
                        else:
                            data_val = int(self.bus.o_rd_data.value)
                        self._finish_packet(current_time, packet, data_val)
                    else:
                        # 'fifo_flop' mode: note handshake time, defer data capture
                        last_xfer = True
                        last_packet = packet
                # Deassert ready on the rising edge (prepare for next cycle or delay)
                await RisingEdge(self.clock)
                self.bus.i_rd_ready.value = 0

        except Exception as e:
            self.log.error(f"Slave({self.title}) Exception in _monitor_recv: {e}")
            raise

    def _finish_packet(self, current_time, packet, data_val):
        """
        Enhanced packet finishing with callback support
        """
        fifo_data = {'data': data_val}
        packet.unpack_from_fifo(fifo_data)
        
        # Apply memory model data, if applicable
        if self.memory_model and self.memory_fields:
            data_field = self.memory_fields.get('data', 'data')
            mem_val = self._read_from_memory(packet)
            if mem_val is not None:
                setattr(packet, data_field, mem_val)
                
        # Record completion time and store packet
        packet.end_time = current_time
        
        # Store in received transactions dictionary
        self.received_transactions[packet.transaction_id] = packet
        
        # Add to received queue
        self.received_queue.append(packet)
        
        self.log.debug(f"Slave({self.title}) Transaction received at {packet.end_time}ns: {packet.formatted(compact=True)}")
        
        # Trigger callbacks
        self._recv(packet)  # Original callback mechanism
        
        # Call the transaction received callback if defined
        if self.transaction_received_callback:
            cocotb.start_soon(self.transaction_received_callback(packet))


class EnhancedGAXIMonitor(GAXIMonitor):
    """
    Enhanced Monitor for GAXI bus transactions with transaction callbacks.
    """
    def __init__(self, *args, **kwargs):
        # Extract callbacks before passing to parent
        self.transaction_observed_callback = kwargs.pop('transaction_observed_callback', None)
        
        # Initialize the parent class
        super().__init__(*args, **kwargs)
        
        # Initialize transaction tracking
        self.transaction_id_counter = 0
        self.observed_transactions = {}

    def _finish_packet(self, current_time, packet, data_val):
        """Enhanced packet finishing with callback support"""
        fifo_data = {'data': data_val}
        packet.unpack_from_fifo(fifo_data)
        
        # Record completion time and store packet
        packet.end_time = current_time
        
        # Assign transaction ID if not already present
        if not hasattr(packet, 'transaction_id'):
            packet.transaction_id = self.transaction_id_counter
            self.transaction_id_counter += 1
            
        # Store in observed transactions dictionary
        self.observed_transactions[packet.transaction_id] = packet
        
        # Add to observed queue
        self.observed_queue.append(packet)
        
        self.log.debug(f"Monitor({self.title}) Transaction observed at {packet.end_time}ns: {packet.formatted(compact=True)}")
        
        # Trigger callbacks
        self._recv(packet)  # Original callback mechanism
        
        # Call the transaction observed callback if defined
        if self.transaction_observed_callback:
            cocotb.start_soon(self.transaction_observed_callback(packet))
