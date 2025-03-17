"""
APB-GAXI Integration Using Factories

This module provides functions for setting up APB-GAXI integration using 
the factory pattern for component creation.
"""
import cocotb
from cocotb.triggers import RisingEdge, Timer

from CocoTBFramework.Components.gaxi_factories import (
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor, 
    create_gaxi_scoreboard, create_gaxi_components,
    get_command_response_field_config
)
from CocoTBFramework.Components.apb_factories import (
    create_apb_master, create_apb_slave, create_apb_monitor,
    create_apb_scoreboard, create_apb_components,
    create_apb_transformer
)
from CocoTBFramework.Components.memory_model import MemoryModel
from CocoTBFramework.Components.gaxi_sequence import GAXISequence
from CocoTBFramework.Components.gaxi_packet import GAXIPacket
from CocoTBFramework.Components.gaxi_enhancements import GAXICommandHandler
from Scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from Scoreboards.gaxi_scoreboard import GAXIScoreboard


async def create_apb_gaxi_integration(dut, clock, log=None, 
                                    addr_width=32, data_width=32,
                                    use_enhanced=True):
    """
    Create and configure APB-GAXI integration components.
    
    Args:
        dut: Device under test
        clock: Clock signal
        log: Logger instance
        addr_width: Address width in bits
        data_width: Data width in bits
        use_enhanced: Whether to use enhanced GAXI components
        
    Returns:
        Dictionary with all created components
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)
    
    # Create shared memory model
    memory_model = MemoryModel(
        num_lines=1024,
        bytes_per_line=data_width // 8,
        log=log
    )
    
    # Get field configuration for GAXI command-response
    field_config = get_command_response_field_config(addr_width, data_width)
    
    # Create APB components
    apb_components = create_apb_components(
        dut, 
        clock,
        title_prefix="APB_",
        addr_width=addr_width,
        data_width=data_width,
        memory_lines=1024,
        log=log
    )
    
    # Create GAXI components
    gaxi_components = create_gaxi_components(
        dut,
        clock,
        title_prefix="GAXI_",
        field_config=field_config,
        enhanced=use_enhanced,
        memory_model=memory_model,
        log=log
    )
    
    # Create APB-GAXI scoreboard
    apb_gaxi_scoreboard = APBGAXIScoreboard(
        "APB-GAXI_Scoreboard",
        log=log
    )
    
    # Connect APB slave command/response to GAXI master/slave
    # Get master and slave components
    gaxi_master = gaxi_components['master']
    gaxi_slave = gaxi_components['slave']
    
    # Create command handler
    command_handler = GAXICommandHandler(
        dut,
        gaxi_master,
        gaxi_slave,
        field_config=field_config,
        log=log
    )
    
    # Connect monitors to scoreboard
    apb_monitor = apb_components['monitor']
    gaxi_master_monitor = gaxi_components['master_monitor']
    gaxi_slave_monitor = gaxi_components['slave_monitor']
    
    # Register callbacks
    apb_monitor.add_callback(lambda tx: apb_gaxi_scoreboard.add_apb_transaction(tx))
    gaxi_master_monitor.add_callback(lambda tx: apb_gaxi_scoreboard.add_gaxi_transaction(tx))
    
    # Return all components
    result = {
        'apb_components': apb_components,
        'gaxi_components': gaxi_components,
        'command_handler': command_handler,
        'apb_gaxi_scoreboard': apb_gaxi_scoreboard,
        'memory_model': memory_model,
        'field_config': field_config,
    }
    
    log.info("APB-GAXI integration components created")
    return result


class APBGAXIIntegrationTest:
    """
    Test harness for APB-GAXI integration testing.
    
    This class provides methods for:
    1. Setting up test components
    2. Running test sequences
    3. Verifying results using scoreboards
    """
    
    def __init__(self, dut, log=None):
        """
        Initialize the test harness.
        
        Args:
            dut: Device under test
            log: Logger instance
        """
        self.dut = dut
        self.log = log or getattr(dut, '_log', None)
        self.components = None
        self.command_handler = None
    
    async def setup(self, addr_width=32, data_width=32, use_enhanced=True):
        """
        Set up test components.
        
        Args:
            addr_width: Address width in bits
            data_width: Data width in bits
            use_enhanced: Whether to use enhanced GAXI components
        """
        # Create integration components
        self.components = await create_apb_gaxi_integration(
            self.dut,
            self.dut.pclk,
            log=self.log,
            addr_width=addr_width,
            data_width=data_width,
            use_enhanced=use_enhanced
        )
        
        # Get command handler
        self.command_handler = self.components['command_handler']
        
        # Reset components
        await self._reset_components()
        
        self.log.info("Test harness setup complete")
    
    async def _reset_components(self):
        """Reset all components."""
        # Reset DUT
        self.dut.presetn.value = 0
        self.dut.i_cmd_ready.value = 0
        self.dut.i_rsp_valid.value = 0
        self.dut.i_rsp_prdata.value = 0
        self.dut.i_rsp_pslverr.value = 0
        
        # Wait for a few cycles
        for _ in range(5):
            await RisingEdge(self.dut.pclk)
        
        # Release reset
        self.dut.presetn.value = 1
        
        # Wait for stabilization
        for _ in range(5):
            await RisingEdge(self.dut.pclk)
        
        # Reset APB and GAXI components
        apb_master = self.components['apb_components']['master']
        gaxi_master = self.components['gaxi_components']['master']
        gaxi_slave = self.components['gaxi_components']['slave']
        
        await apb_master.reset_bus()
        await gaxi_master.reset_bus()
        await gaxi_slave.reset_bus()
        
        # Clear scoreboard
        self.components['apb_gaxi_scoreboard'].clear()
    
    async def start_command_handler(self):
        """Start the command handler."""
        await self.command_handler.start()
        self.log.info("Command handler started")
    
    async def stop_command_handler(self):
        """Stop the command handler."""
        await self.command_handler.stop()
        self.log.info("Command handler stopped")
    
    async def run_apb_test(self, base_addr=0, num_registers=10, pattern="alternating"):
        """
        Run an APB test.
        
        Args:
            base_addr: Base address for test
            num_registers: Number of registers to test
            pattern: Test pattern ("alternating", "burst", "strobe", "stress")
            
        Returns:
            Test results
        """
        from CocoTBFramework.Components.apb_factories import create_apb_sequence
        
        # Create APB sequence
        sequence = create_apb_sequence(
            name=f"apb_{pattern}",
            num_regs=num_registers,
            base_addr=base_addr,
            pattern=pattern,
            data_width=32,
            randomize_delays=True
        )
        
        # Get APB master
        apb_master = self.components['apb_components']['master']
        
        # Create transaction
        transaction = apb_master.create_transaction()
        
        # Reset iterators
        sequence.reset_iterators()
        
        # Start command handler if not already running
        was_running = hasattr(self.command_handler, 'running') and self.command_handler.running
        if not was_running:
            await self.start_command_handler()
        
        try:
            # Run sequence
            self.log.info(f"Running APB test with pattern '{pattern}'")
            
            # Get sequence length
            sequence_length = len(sequence.pwrite_seq)
            
            # Execute each transaction in sequence
            for i in range(sequence_length):
                # Get transaction parameters
                is_write = sequence.next_pwrite()
                addr = sequence.next_addr()
                
                # Set transaction fields
                transaction.pwrite = 1 if is_write else 0
                transaction.direction = "WRITE" if is_write else "READ"
                transaction.paddr = addr
                
                # For writes, set data and strobe
                if is_write:
                    transaction.pwdata = sequence.next_data()
                    transaction.pstrb = sequence.next_strb()
                    self.log.info(f"APB {i+1}/{sequence_length}: WRITE addr=0x{addr:08X}, data=0x{transaction.pwdata:08X}")
                else:
                    self.log.info(f"APB {i+1}/{sequence_length}: READ addr=0x{addr:08X}")
                
                # Send transaction
                await apb_master.send(transaction)
                
                # Apply any delay
                delay = sequence.next_delay()
                if delay > 0:
                    await Timer(delay * 10, units='ns')  # Assuming 10ns clock
            
            # Allow time for transactions to complete
            await Timer(500, units='ns')
            
            # Check scoreboard
            result = await gaxi_scoreboard.check_scoreboard()
            
            self.log.info(f"GAXI test with pattern '{pattern}' completed")
            self.log.info(gaxi_scoreboard.report())
            
            return result
            
        finally:
            # Stop command handler if we started it
            if not was_running:
                await self.stop_command_handler()
    
    async def run_apb_gaxi_combined_test(self, base_addr=0, num_registers=10):
        """
        Run a combined test with both APB and GAXI transactions.
        
        This test verifies the end-to-end integration of APB and GAXI.
        
        Args:
            base_addr: Base address for test
            num_registers: Number of registers to test
            
        Returns:
            Test results
        """
        # Start command handler
        await self.start_command_handler()
        
        try:
            # First run APB writes to populate memory
            self.log.info("Running APB writes...")
            apb_result = await self.run_apb_test(
                base_addr=base_addr,
                num_registers=num_registers,
                pattern="burst"
            )
            
            # Then run GAXI reads to verify data
            self.log.info("Running GAXI reads...")
            gaxi_result = await self.run_gaxi_test(
                base_addr=base_addr,
                num_registers=num_registers,
                pattern="address_sweep"
            )
            
            # Then run GAXI writes
            self.log.info("Running GAXI writes...")
            await self.run_gaxi_test(
                base_addr=base_addr + 0x100,
                num_registers=num_registers,
                pattern="burst"
            )
            
            # Then run APB reads to verify
            self.log.info("Running APB reads...")
            apb_verify_result = await self.run_apb_test(
                base_addr=base_addr + 0x100,
                num_registers=num_registers,
                pattern="burst"
            )
            
            # Check APB-GAXI scoreboard
            apb_gaxi_scoreboard = self.components['apb_gaxi_scoreboard']
            cross_result = await apb_gaxi_scoreboard.check_scoreboard()
            
            self.log.info("Combined APB-GAXI test completed")
            self.log.info(apb_gaxi_scoreboard.report())
            
            # Return overall results
            return all([apb_result, gaxi_result, apb_verify_result, cross_result])
            
        finally:
            # Stop command handler
            await self.stop_command_handler()
    
    def dump_memory(self, base_addr=0, length=64):
        """
        Dump memory contents for debugging.
        
        Args:
            base_addr: Base address to start dump
            length: Number of bytes to dump
        """
        memory_model = self.components['memory_model']
        dump = memory_model.dump()
        
        self.log.info(f"Memory dump from 0x{base_addr:08X} ({length} bytes):")
        self.log.info(dump)


@cocotb.test()
async def test_apb_gaxi_integration(dut):
    """
    Example test for APB-GAXI integration.
    
    Args:
        dut: Device under test
    """
    # Get logger
    log = dut._log
    
    # Start clock
    cocotb.start_soon(cocotb.clock.Clock(dut.pclk, 10, units='ns').start())
    
    # Create test harness
    test_harness = APBGAXIIntegrationTest(dut, log)
    
    # Setup harness
    await test_harness.setup(use_enhanced=True)
    
    # Run tests
    try:
        # Run APB test
        log.info("=== Test 1: APB Alternating Pattern ===")
        apb_result = await test_harness.run_apb_test(
            base_addr=0,
            num_registers=8,
            pattern="alternating"
        )
        
        # Run GAXI test
        log.info("=== Test 2: GAXI Alternating Pattern ===")
        gaxi_result = await test_harness.run_gaxi_test(
            base_addr=0x100,
            num_registers=8,
            pattern="alternating"
        )
        
        # Run GAXI burst test
        log.info("=== Test 3: GAXI Burst Pattern ===")
        gaxi_burst_result = await test_harness.run_gaxi_test(
            base_addr=0x200,
            num_registers=16,
            pattern="burst"
        )
        
        # Run combined test
        log.info("=== Test 4: Combined APB-GAXI Test ===")
        combined_result = await test_harness.run_apb_gaxi_combined_test(
            base_addr=0x300,
            num_registers=8
        )
        
        # Report overall results
        log.info("=== Overall Test Results ===")
        log.info(f"Test 1 (APB Alternating): {'PASS' if apb_result else 'FAIL'}")
        log.info(f"Test 2 (GAXI Alternating): {'PASS' if gaxi_result else 'FAIL'}")
        log.info(f"Test 3 (GAXI Burst): {'PASS' if gaxi_burst_result else 'FAIL'}")
        log.info(f"Test 4 (Combined APB-GAXI): {'PASS' if combined_result else 'FAIL'}")
        
        all_passed = all([apb_result, gaxi_result, gaxi_burst_result, combined_result])
        log.info(f"Overall: {'PASS' if all_passed else 'FAIL'}")
        
        # Dump memory for debugging
        test_harness.dump_memory()
        
    except Exception as e:
        log.error(f"Test failed with exception: {str(e)}")
        raise
    
    finally:
        # Cleanup
        await Timer(100, units='ns') units='ns')
            
            # Check scoreboard
            apb_gaxi_scoreboard = self.components['apb_gaxi_scoreboard']
            result = await apb_gaxi_scoreboard.check_scoreboard()
            
            self.log.info(f"APB test with pattern '{pattern}' completed")
            self.log.info(apb_gaxi_scoreboard.report())
            
            return result
            
        finally:
            # Stop command handler if we started it
            if not was_running:
                await self.stop_command_handler()
    
    async def run_gaxi_test(self, base_addr=0, num_registers=10, pattern="alternating"):
        """
        Run a GAXI test.
        
        Args:
            base_addr: Base address for test
            num_registers: Number of registers to test
            pattern: Test pattern ("alternating", "burst", "address_sweep", "data_pattern", "random")
            
        Returns:
            Test results
        """
        # Get field config
        field_config = self.components['field_config']
        
        # Create GAXI sequence based on pattern
        if pattern == "alternating":
            sequence = GAXISequence.create_alternating(
                name=f"gaxi_{pattern}",
                base_addr=base_addr,
                num_registers=num_registers,
                field_config=field_config
            )
        elif pattern == "burst":
            sequence = GAXISequence.create_burst(
                name=f"gaxi_{pattern}",
                base_addr=base_addr,
                num_registers=num_registers,
                field_config=field_config
            )
        elif pattern == "address_sweep":
            sequence = GAXISequence.create_address_sweep(
                name=f"gaxi_{pattern}",
                base_addr=base_addr,
                num_addresses=num_registers,
                field_config=field_config
            )
        elif pattern == "data_pattern":
            sequence = GAXISequence.create_data_pattern(
                name=f"gaxi_{pattern}",
                addr=base_addr,
                field_config=field_config
            )
        elif pattern == "random":
            sequence = GAXISequence.create_random(
                name=f"gaxi_{pattern}",
                base_addr=base_addr,
                num_transactions=num_registers*2,
                field_config=field_config
            )
        else:
            raise ValueError(f"Unknown pattern: {pattern}")
        
        # Get GAXI master and slave
        gaxi_master = self.components['gaxi_components']['master']
        gaxi_scoreboard = self.components['gaxi_components']['scoreboard']
        
        # Generate packets
        packets = sequence.generate_packets()
        
        # Start command handler if not already running
        was_running = hasattr(self.command_handler, 'running') and self.command_handler.running
        if not was_running:
            await self.start_command_handler()
        
        try:
            # Run sequence
            self.log.info(f"Running GAXI test with pattern '{pattern}'")
            
            # Register packets with scoreboard
            for packet in packets:
                gaxi_scoreboard.add_expected(packet)
            
            # Send each packet
            for i, packet in enumerate(packets):
                self.log.info(f"GAXI {i+1}/{len(packets)}: "
                           f"{'WRITE' if packet.cmd == 1 else 'READ'} "
                           f"addr=0x{packet.addr:08X}"
                           f"{' data=0x{:08X}'.format(packet.data) if packet.cmd == 1 else ''}")
                
                # Send packet through GAXI master
                await gaxi_master.send(packet)
                
                # Apply delay from sequence
                delay = sequence.delay_seq[i % len(sequence.delay_seq)]
                if delay > 0:
                    await Timer(delay * 10, units='ns')  # Assuming 10ns clock
            
            # Allow time for transactions to complete
            await Timer(500,