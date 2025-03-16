"""
Enhanced GAXI Master/Slave Components with Command-Response Communication
"""
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from collections import deque

from Components.gaxi_packet import GAXIPacket


class EnhancedGAXIMaster:
    """
    Enhanced wrapper for GAXIMaster with memory access functionality
    
    This class wraps the existing GAXIMaster and adds methods to:
    1. Send commands to a slave
    2. Wait for responses from a slave
    3. Support memory read/write operations
    """
    
    def __init__(self, master, log=None):
        """
        Initialize the enhanced master wrapper.
        
        Args:
            master: Existing GAXIMaster instance
            log: Logger instance
        """
        self.master = master
        self.log = log or master.log
        self.clock = master.clock
        self.field_config = master.field_config
        self.packet_class = master.packet_class
        
        # Response handling
        self.response_queue = deque()
        self.pending_commands = deque()  # Commands waiting for responses
        
    async def send_command(self, cmd_type, address, data=None, strobe=None):
        """
        Send a command to a slave device.
        
        Args:
            cmd_type: Command type ('READ' or 'WRITE')
            address: Target address
            data: Data to write (for WRITE commands)
            strobe: Byte enable strobe (for WRITE commands)
            
        Returns:
            Command packet that was sent
        """
        # Create command packet
        cmd_packet = self.packet_class(self.field_config)
        
        # Set command fields
        cmd_packet.fields['cmd'] = 1 if cmd_type == 'WRITE' else 0
        cmd_packet.fields['addr'] = address
        
        if cmd_type == 'WRITE' and data is not None:
            cmd_packet.fields['data'] = data
            
        if cmd_type == 'WRITE' and strobe is not None and 'strb' in cmd_packet.fields:
            cmd_packet.fields['strb'] = strobe
        
        # Log command
        self.log.debug(f"Sending {cmd_type} command to address 0x{address:X}" + 
                      (f" with data 0x{data:X}" if cmd_type == 'WRITE' and data is not None else ""))
        
        # Store in pending commands queue
        self.pending_commands.append(cmd_packet)
        
        # Send packet
        await self.master.send(cmd_packet)
        
        return cmd_packet

    async def wait_for_response(self, timeout_cycles=None):
        """
        Wait for a response from a slave device.
        
        Args:
            timeout_cycles: Maximum cycles to wait before timeout
            
        Returns:
            Response packet, or None if timeout
        """
        if not timeout_cycles:
            timeout_cycles = self.master.timeout_cycles
            
        # Wait for response or timeout
        cycles_waited = 0
        while not self.response_queue and cycles_waited < timeout_cycles:
            await RisingEdge(self.clock)
            cycles_waited += 1
            
        # Check if timed out
        if cycles_waited >= timeout_cycles:
            self.log.error(f"Timeout waiting for response after {timeout_cycles} cycles")
            return None
            
        # Get and return response
        response = self.response_queue.popleft()
        self.log.debug(f"Received response: {response.formatted(compact=True)}")
        return response
        
    def handle_response(self, response_packet):
        """
        Handle an incoming response packet.
        
        Args:
            response_packet: Response packet from slave
        """
        self.log.debug(f"Got response: {response_packet.formatted(compact=True)}")
        self.response_queue.append(response_packet)
        
    async def read_memory(self, address):
        """
        Read from memory via slave.
        
        Args:
            address: Memory address to read
            
        Returns:
            Data read from memory, or None if error
        """
        # Send READ command
        await self.send_command('READ', address)
        
        # Wait for response
        response = await self.wait_for_response()
        if response is None:
            return None
            
        # Return data from response
        return response.fields.get('data')
        
    async def write_memory(self, address, data, strobe=None):
        """
        Write to memory via slave.
        
        Args:
            address: Memory address to write
            data: Data to write
            strobe: Byte enable mask (optional)
            
        Returns:
            True if successful, False if error
        """
        # Send WRITE command
        await self.send_command('WRITE', address, data, strobe)
        
        # Wait for acknowledgement (simple response)
        response = await self.wait_for_response()
        
        # Check if write was successful
        return response is not None


class EnhancedGAXISlave:
    """
    Enhanced wrapper for GAXISlave with command handling functionality
    
    This class wraps the existing GAXISlave and adds methods to:
    1. Receive and process commands from a master
    2. Send responses back to the master
    3. Access memory based on commands
    """
    
    def __init__(self, slave, memory_model=None, log=None):
        """
        Initialize the enhanced slave wrapper.
        
        Args:
            slave: Existing GAXISlave instance
            memory_model: Optional memory model for storage
            log: Logger instance
        """
        self.slave = slave
        self.log = log or slave.log
        self.clock = slave.clock
        self.field_config = slave.field_config
        self.packet_class = slave.packet_class
        
        # Memory model
        self.memory_model = memory_model
        
        # Command processing
        self.command_queue = deque()  # Received commands
        self.memory_fields = {
            'addr': 'addr',
            'data': 'data',
            'strb': 'strb'
        }
        
        # Start command processor
        self.processor_task = None
        
    def start_processor(self):
        """Start the command processor coroutine"""
        if self.processor_task is None:
            self.processor_task = cocotb.start_soon(self._process_commands())
            
    def stop_processor(self):
        """Stop the command processor coroutine"""
        if self.processor_task is not None:
            self.processor_task.kill()
            self.processor_task = None
            
    def handle_command(self, command_packet):
        """
        Handle an incoming command packet.
        
        Args:
            command_packet: Command packet from master
        """
        self.log.debug(f"Received command: {command_packet.formatted(compact=True)}")
        self.command_queue.append(command_packet)
        
    async def _process_commands(self):
        """Process commands from the command queue"""
        try:
            while True:
                # Wait for a command
                while not self.command_queue:
                    await RisingEdge(self.clock)
                    
                # Get next command
                cmd = self.command_queue.popleft()
                
                # Process the command
                cmd_value = cmd.fields.get('cmd', 0)
                cmd_type = 'WRITE' if cmd_value == 1 else 'READ'
                address = cmd.fields.get('addr', 0)
                
                if cmd_type == 'READ':
                    await self._handle_read_command(cmd, address)
                else:
                    await self._handle_write_command(cmd, address)
                    
        except cocotb.result.SimTimeoutError:
            self.log.info("Command processor terminated due to timeout")
        except Exception as e:
            self.log.error(f"Command processor error: {e}")
            
    async def _handle_read_command(self, cmd, address):
        """Handle a READ command"""
        # Create response packet
        response = self.packet_class(self.field_config)
        
        # Read from memory if available
        if self.memory_model:
            data_bytes = self.memory_model.read(address, self.memory_model.bytes_per_line)
            data = self.memory_model.bytearray_to_integer(data_bytes)
            response.fields['data'] = data
            self.log.debug(f"Read from memory: addr=0x{address:X}, data=0x{data:X}")
        else:
            # Default data if no memory model
            response.fields['data'] = 0xDEADBEEF
            self.log.debug(f"No memory model, returning default data for addr=0x{address:X}")
        
        # Send response
        await self.slave.send(response)
        
    async def _handle_write_command(self, cmd, address):
        """Handle a WRITE command"""
        data = cmd.fields.get('data', 0)
        strb = cmd.fields.get('strb', 0xFF)
        
        # Write to memory if available
        if self.memory_model:
            data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)
            self.memory_model.write(address, data_bytes, strb)
            self.log.debug(f"Write to memory: addr=0x{address:X}, data=0x{data:X}, strb=0x{strb:X}")
        else:
            self.log.debug(f"No memory model, write ignored: addr=0x{address:X}, data=0x{data:X}")
        
        # Send acknowledgement
        response = self.packet_class(self.field_config)
        response.fields['ack'] = 1
        await self.slave.send(response)
        
    async def send_response(self, command, data):
        """
        Send a response to a command.
        
        Args:
            command: Command to respond to
            data: Data to include in response
        """
        # Create response packet
        response = self.packet_class(self.field_config)
        
        # Copy command fields for correlation
        if 'addr' in command.fields and 'addr' in response.fields:
            response.fields['addr'] = command.fields['addr']
            
        # Set response data
        if 'data' in response.fields:
            response.fields['data'] = data
            
        # Send response
        await self.slave.send(response)
        
    def set_memory_model(self, memory_model, memory_fields=None):
        """
        Set or update the memory model.
        
        Args:
            memory_model: Memory model for storage
            memory_fields: Optional mapping of memory fields to packet fields
        """
        self.memory_model = memory_model
        if memory_fields:
            self.memory_fields = memory_fields
