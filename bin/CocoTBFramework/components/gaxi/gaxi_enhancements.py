"""
Enhanced GAXI Master and Slave Components

These enhanced components provide higher-level functionality by wrapping
the basic GAXI master/slave components.
"""
import cocotb
from cocotb.triggers import RisingEdge, Timer
from collections import deque
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket

class EnhancedGAXIMaster:
    """
    Enhanced GAXI Master Component

    Wraps a basic GAXIMaster to provide higher-level functionality:
    - Direct memory read/write methods
    - Support for automated address sequencing
    - Integration with memory model
    - Command interface to coordinate with slave responses
    """

    def __init__(self, master, memory_model=None, log=None):
        """
        Initialize enhanced GAXI master.

        Args:
            master: Base GAXIMaster instance to wrap
            memory_model: Optional memory model for data storage
            log: Logger instance
        """
        self.master = master
        self.memory_model = memory_model or master.memory_model
        self.log = log or master.log
        self.field_config = master.field_config
        self.packet_class = master.packet_class

        # Command processor task
        self.processor_task = None
        self.response_queue = deque()
        self.command_queue = deque()
        self.running = False

    async def reset_bus(self):
        """Reset the master and clear queues."""
        await self.master.reset_bus()
        self.command_queue.clear()
        self.response_queue.clear()

    async def send(self, packet):
        # sourcery skip: hoist-statement-from-if, reintroduce-else
        """
        Send a packet through the master.

        Args:
            packet: Packet to send

        Returns:
            Response packet for read operations, None for writes
        """
        # For writes with memory model, update memory
        if packet.cmd == 1 and self.memory_model:  # Write
            addr = packet.addr
            data = packet.data

            # Convert to bytes for memory model
            data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)
            strb = packet.strb if hasattr(packet, 'strb') else 0xFF
            # Write to memory model
            self.memory_model.write(addr, data_bytes, strb)
            self.log.debug(f"EnhancedGAXIMaster: Write to memory addr=0x{addr:08X}, data=0x{data:08X}")

        # Send through base master
        await self.master.send(packet)

        # For reads, return response
        if packet.cmd == 0:  # Read
            # Create a future to wait for the response
            # In real implementation, this would be more sophisticated,
            # connecting to the slave response queue
            return None  # Placeholder

        return None

    async def read(self, addr):  # sourcery skip: assign-if-exp, reintroduce-else
        """
        Read data from specified address.

        Args:
            addr: Address to read from

        Returns:
            Data read from address
        """
        # Create read packet
        packet = self.packet_class(self.field_config)
        packet.cmd = 0  # Read
        packet.addr = addr

        # If we have a memory model, read directly
        if self.memory_model:
            # Read from memory model
            data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
            data = self.memory_model.bytearray_to_integer(data_bytes)
            packet.data = data
            self.log.debug(f"EnhancedGAXIMaster: Read from memory addr=0x{addr:08X}, data=0x{data:08X}")

        # Send through base master
        await self.master.send(packet)

        # In a real implementation, we would wait for the response
        # For now, if we have a memory model, return the data
        if self.memory_model:
            return packet.data

        return None

    async def write(self, addr, data, strb=None):
        """
        Write data to specified address.

        Args:
            addr: Address to write to
            data: Data to write
            strb: Byte strobe mask (default: all bytes enabled)

        Returns:
            None
        """
        # Create write packet
        packet = self.packet_class(self.field_config)
        packet.cmd = 1  # Write
        packet.addr = addr
        packet.data = data

        # Set strobe if provided and supported
        if strb is not None and 'strb' in self.field_config:
            packet.strb = strb

        # Send through base master
        await self.send(packet)

    async def start_processor(self):
        """Start command processor task."""
        if self.processor_task is None:
            self.running = True
            self.processor_task = cocotb.start_soon(self._command_processor())
            self.log.info("EnhancedGAXIMaster: Command processor started")

    async def stop_processor(self):
        """Stop command processor task."""
        self.running = False
        if self.processor_task is not None:
            await Timer(10, units='ns')  # Allow task to complete
            self.processor_task = None
            self.log.info("EnhancedGAXIMaster: Command processor stopped")

    async def _command_processor(self):
        """Command processor background task."""
        self.log.debug("EnhancedGAXIMaster: Command processor running")

        while self.running:
            # Check for commands to process
            if self.command_queue:
                cmd = self.command_queue.popleft()

                # Process command
                if cmd['type'] == 'read':
                    await self.read(cmd['addr'])
                elif cmd['type'] == 'write':
                    await self.write(cmd['addr'], cmd['data'], cmd.get('strb'))

                # Log command execution
                self.log.debug(f"EnhancedGAXIMaster: Processed command {cmd['type']} addr=0x{cmd['addr']:08X}")

            # Wait a bit before checking again
            await Timer(100, units='ps')


class EnhancedGAXISlave:
    """
    Enhanced GAXI Slave Component

    Wraps a basic GAXISlave to provide higher-level functionality:
    - Automatic processing of incoming transactions
    - Integration with memory model for data storage/retrieval
    - Response queue management
    - Support for custom processing callbacks
    """

    def __init__(self, slave, memory_model=None, log=None):
        """
        Initialize enhanced GAXI slave.

        Args:
            slave: Base GAXISlave instance to wrap
            memory_model: Optional memory model for data storage
            log: Logger instance
        """
        self.slave = slave
        self.memory_model = memory_model or slave.memory_model
        self.log = log or slave.log
        self.field_config = slave.field_config
        self.packet_class = slave.packet_class

        # Processor task
        self.processor_task = None
        self.running = False

        # Callbacks for custom processing
        self.read_callback = None
        self.write_callback = None

    async def reset_bus(self):
        """Reset the slave."""
        await self.slave.reset_bus()

    def set_read_callback(self, callback):
        """
        Set callback for custom read processing.

        Args:
            callback: Function to call with (addr, packet) arguments
        """
        self.read_callback = callback

    def set_write_callback(self, callback):
        """
        Set callback for custom write processing.

        Args:
            callback: Function to call with (addr, data, packet) arguments
        """
        self.write_callback = callback

    @property
    def received_queue(self):
        """Get the received packet queue from the base slave."""
        return self.slave.received_queue

    async def start_processor(self):
        """Start automatic transaction processor."""
        if self.processor_task is None:
            self.running = True
            self.processor_task = cocotb.start_soon(self._transaction_processor())
            self.log.info("EnhancedGAXISlave: Transaction processor started")

    async def stop_processor(self):
        """Stop automatic transaction processor."""
        self.running = False
        if self.processor_task is not None:
            await Timer(10, units='ns')  # Allow task to complete
            self.processor_task = None
            self.log.info("EnhancedGAXISlave: Transaction processor stopped")

    async def _transaction_processor(self):
        """
        Process incoming transactions automatically.

        For reads: Read from memory model or call custom callback
        For writes: Write to memory model or call custom callback
        """
        self.log.debug("EnhancedGAXISlave: Transaction processor running")

        while self.running:
            # Check if we have received packets to process
            if self.slave.received_queue:
                packet = self.slave.received_queue.popleft()

                addr = packet.addr

                if packet.cmd == 0:  # Read
                    # Handle read operation
                    if self.read_callback:
                        # Custom processing
                        self.read_callback(addr, packet)
                    elif self.memory_model:
                        # Default memory model processing
                        data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
                        data = self.memory_model.bytearray_to_integer(data_bytes)
                        packet.data = data
                        self.log.debug(f"EnhancedGAXISlave: Read addr=0x{addr:08X}, data=0x{data:08X}")

                elif packet.cmd == 1:  # Write
                    data = packet.data
                    strb = 0xFF  # Default to all bytes enabled
                    if hasattr(packet, 'strb'):
                        strb = packet.strb

                    # Handle write operation
                    if self.write_callback:
                        # Custom processing
                        self.write_callback(addr, data, packet)
                    elif self.memory_model:
                        # Default memory model processing
                        data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)
                        self.memory_model.write(addr, data_bytes, strb)
                        self.log.debug(f"EnhancedGAXISlave: Write addr=0x{addr:08X}, data=0x{data:08X}")

            # Wait before checking again
            await Timer(10, units='ns')


class GAXICommandHandler:
    """
    Command Handler for APB slave command/response to GAXI interfaces

    This component:
    1. Monitors APB slave command interface
    2. Generates GAXI transactions from commands
    3. Collects GAXI slave responses
    4. Drives APB slave response interface
    """

    def __init__(self, dut, gaxi_master, gaxi_slave, field_config=None, log=None):
        """
        Initialize GAXI command handler.

        Args:
            dut: Device under test (for accessing command/response signals)
            gaxi_master: GAXIMaster or EnhancedGAXIMaster instance
            gaxi_slave: GAXISlave or EnhancedGAXISlave instance
            field_config: Field configuration for GAXI packets
            log: Logger instance
        """
        self.dut = dut
        self.gaxi_master = gaxi_master
        self.gaxi_slave = gaxi_slave
        self.log = log or getattr(dut, '_log', None)

        # Get field config from master if not provided
        self.field_config = field_config or gaxi_master.field_config
        self.packet_class = GAXIPacket  # Default packet class

        # Command/response tasks
        self.cmd_task = None
        self.rsp_task = None
        self.running = False

    async def start(self):
        """Start command handler tasks."""
        if not self.running:
            self.running = True
            self.cmd_task = cocotb.start_soon(self._monitor_cmd_interface())
            self.rsp_task = cocotb.start_soon(self._monitor_rsp_interface())
            self.log.info("GAXICommandHandler: Started")

    async def stop(self):
        """Stop command handler tasks."""
        self.running = False
        await Timer(10, units='ns')  # Allow tasks to complete
        self.cmd_task = None
        self.rsp_task = None
        self.log.info("GAXICommandHandler: Stopped")

    async def _monitor_cmd_interface(self):
        """
        Monitor APB slave command interface and generate GAXI transactions.
        """
        while self.running:
            # Wait for command valid signal
            while not self.dut.o_cmd_valid.value and self.running:
                await RisingEdge(self.dut.pclk)

            if not self.running:
                break

            # Capture command details
            pwrite = int(self.dut.o_cmd_pwrite.value)
            paddr = int(self.dut.o_cmd_paddr.value)
            pwdata = int(self.dut.o_cmd_pwdata.value)
            pstrb = int(self.dut.o_cmd_pstrb.value) if hasattr(self.dut, 'o_cmd_pstrb') else 0xFF

            # Create and send GAXI packet
            packet = self.packet_class(self.field_config)
            packet.cmd = pwrite  # 1=Write, 0=Read
            packet.addr = paddr

            if pwrite:  # Write command
                packet.data = pwdata
                if 'strb' in self.field_config:
                    packet.strb = pstrb
                self.log.info(f"Command: WRITE addr=0x{paddr:08X}, data=0x{pwdata:08X}")
            else:  # Read command
                self.log.info(f"Command: READ addr=0x{paddr:08X}")

            # Send through GAXI master
            await self.gaxi_master.send(packet)

            # Assert command ready to acknowledge
            self.dut.i_cmd_ready.value = 1
            await RisingEdge(self.dut.pclk)
            self.dut.i_cmd_ready.value = 0

    async def _monitor_rsp_interface(self):
        """
        Monitor GAXI slave responses and drive APB slave response interface.
        """
        while self.running:
            # Wait for data in slave received queue
            while not self.gaxi_slave.received_queue and self.running:
                await RisingEdge(self.dut.pclk)

            if not self.running:
                break

            # Get response packet
            packet = self.gaxi_slave.received_queue.popleft()

            # Drive response interface
            self.dut.i_rsp_valid.value = 1
            self.dut.i_rsp_prdata.value = packet.data
            self.dut.i_rsp_pslverr.value = 0  # No error by default

            self.log.info(f"Response: data=0x{packet.data:08X}")

            # Wait for ready acknowledgement
            while not self.dut.o_rsp_ready.value and self.running:
                await RisingEdge(self.dut.pclk)

            if not self.running:
                break

            # Deassert valid
            await RisingEdge(self.dut.pclk)
            self.dut.i_rsp_valid.value = 0
