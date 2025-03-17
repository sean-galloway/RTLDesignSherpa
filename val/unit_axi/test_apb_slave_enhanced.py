"""
Enhanced APB Slave Test with GAXI Integration

This test module demonstrates how to use the enhanced GAXI components
and factories to connect an APB slave's command/response interface
to GAXI master/slave components.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd

from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.memory_model import MemoryModel

# Import APB components
from CocoTBFramework.components.apb.apb import (
    APBSequence, APBCycle, APBTransaction, APBMonitor, APBMaster
)
from CocoTBFramework.components.apb.apb_factories import (
    create_apb_master, create_apb_monitor, create_apb_sequence
)

# Import GAXI components
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.components.gaxi.gaxi_factories import (
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor,
    create_gaxi_scoreboard, create_gaxi_components,
    get_command_response_field_config
)

# Import enhanced components
from CocoTBFramework.components.gaxi.gaxi_enhancements import (
    EnhancedGAXIMaster, EnhancedGAXISlave, GAXICommandHandler
)

# Import transformers and scoreboards
from CocoTBFramework.scoreboards.Transformers.apb_gaxi_transformer import (
    APBtoGAXITransformer, create_apb_gaxi_adapters
)
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard


class APBSlaveEnhancedTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.IDLE_CNTR_WIDTH = self.convert_to_int(os.environ.get('TEST_IDLE_CNTR_WIDTH', '4'))
        
        # Task termination flag
        self.done = False
        
        # Number of registers to test
        self.registers = 64
        
        # Create memory model
        self.num_line = 32768
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)
        
        # Initialize components
        self._init_apb_components()
        self._init_gaxi_components()
        self._init_scoreboard()
        self._init_command_handler()
    
    def _init_apb_components(self):
        """Initialize APB components."""
        # Create APB master
        self.apb_master_randomizer = FlexRandomizer({
            'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
            'penable': ([[0, 0], [1, 3]], [3, 1]),
        })
        
        self.apb_master = create_apb_master(
            self.dut, 
            'APB Master', 
            's_apb', 
            self.dut.pclk,
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            randomizer=self.apb_master_randomizer,
            log=self.log
        )
        
        # Create APB Monitor
        self.apb_monitor = create_apb_monitor(
            self.dut, 
            'APB Monitor', 
            self.dut.pclk,
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            log=self.log
        )
    
    def _init_gaxi_components(self):
        """Initialize GAXI components."""
        # Get field configuration for GAXI
        self.gaxi_field_config = get_command_response_field_config(
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH
        )
        
        # Create GAXI components
        self.gaxi_components = create_gaxi_components(
            self.dut,
            self.dut.pclk,
            title_prefix="GAXI_",
            field_config=self.gaxi_field_config,
            enhanced=True,
            memory_model=self.mem,
            log=self.log
        )
        
        # Extract components for convenience
        self.gaxi_master = self.gaxi_components['master']
        self.gaxi_slave = self.gaxi_components['slave']
        self.gaxi_master_monitor = self.gaxi_components['master_monitor']
        self.gaxi_slave_monitor = self.gaxi_components['slave_monitor']
        self.gaxi_scoreboard = self.gaxi_components['scoreboard']
    
    def _init_scoreboard(self):
        """Initialize scoreboards."""
        # Create APB-GAXI scoreboard
        self.apb_gaxi_scoreboard = APBGAXIScoreboard("APB-GAXI Scoreboard", self.log)
        
        # Connect monitors to scoreboard
        self.apb_monitor.add_callback(lambda tx: self.apb_gaxi_scoreboard.add_apb_transaction(tx))
        self.gaxi_master_monitor.add_callback(lambda tx: self.apb_gaxi_scoreboard.add_gaxi_transaction(tx))
        self.gaxi_master_monitor.add_callback(lambda tx: self.gaxi_scoreboard.add_expected(tx))
        self.gaxi_slave_monitor.add_callback(lambda tx: self.gaxi_scoreboard.add_actual(tx))
    
    def _init_command_handler(self):
        """Initialize command handler."""
        # Create command handler
        self.command_handler = GAXICommandHandler(
            self.dut,
            self.gaxi_master,
            self.gaxi_slave,
            field_config=self.gaxi_field_config,
            log=self.log
        )
    
    async def reset_dut(self):
        """Reset the DUT and all components."""
        self.log.debug('Starting reset_dut')
        
        # Reset DUT control signals
        self.dut.presetn.value = 0
        
        # Reset command/response interface
        self.dut.i_cmd_ready.value = 0
        self.dut.i_rsp_valid.value = 0
        self.dut.i_rsp_prdata.value = 0
        self.dut.i_rsp_pslverr.value = 0 
        
        # Reset APB master
        await self.apb_master.reset_bus()
        
        # Reset GAXI components
        await self.gaxi_master.reset_bus()
        await self.gaxi_slave.reset_bus()
        
        # Hold reset for multiple cycles
        await self.wait_clocks('pclk', 5)
        
        # Release reset
        self.dut.presetn.value = 1
        
        # Wait for stabilization
        await self.wait_clocks('pclk', 10)
        
        # Clear scoreboards
        self.apb_gaxi_scoreboard.clear()
        self.gaxi_scoreboard.clear()
        
        self.log.debug('Ending reset_dut')
    
    async def run_apb_sequence(self, sequence, num_transactions=None):
        """
        Run an APB test sequence.
        
        Args:
            sequence: APBSequence instance
            num_transactions: Number of transactions to run (default: sequence length)
            
        Returns:
            True if sequence completes successfully, False otherwise
        """
        # Start command handler
        await self.command_handler.start()
        
        try:
            # Reset sequence iterators
            sequence.reset_iterators()
            
            # Determine transaction count
            if num_transactions is None:
                num_transactions = len(sequence.pwrite_seq)
            
            self.log.info(f"Running APB sequence '{sequence.name}' ({num_transactions} transactions)")
            
            for i in range(num_transactions):
                # Get next transaction parameters
                is_write = sequence.next_pwrite()
                addr = sequence.next_addr()
                
                # Create transaction
                transaction = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
                transaction = transaction.next()
                
                # Set transaction fields
                transaction.pwrite = 1 if is_write else 0
                transaction.direction = "WRITE" if is_write else "READ"
                transaction.paddr = addr
                
                # For write, set data and strobe
                if is_write:
                    transaction.pwdata = sequence.next_data()
                    transaction.pstrb = sequence.next_strb()
                    self.log.info(f"APB {i+1}/{num_transactions}: WRITE addr=0x{addr:08X}, data=0x{transaction.pwdata:08X}")
                else:
                    self.log.info(f"APB {i+1}/{num_transactions}: READ addr=0x{addr:08X}")
                
                # Send transaction
                await self.apb_master.send(transaction)
                
                # Add any delay
                delay = sequence.next_delay()
                if delay > 0:
                    await self.wait_clocks('pclk', delay)
            
            # Wait for any pending transactions to complete
            await self.wait_clocks('pclk', 20)
            
            self.log.info(f"APB sequence '{sequence.name}' completed")
            
            return True
        
        except Exception as e:
            self.log.error(f"Error running APB sequence: {str(e)}")
            return False
        
        finally:
            # Stop command handler
            await self.command_handler.stop()
    
    async def run_gaxi_sequence(self, sequence, num_packets=None):
        """
        Run a GAXI test sequence.
        
        Args:
            sequence: GAXISequence instance
            num_packets: Number of packets to send (default: all generated packets)
            
        Returns:
            True if sequence completes successfully, False otherwise
        """
        # Start command handler
        await self.command_handler.start()
        
        try:
            # Generate packets
            packets = sequence.generate_packets()
            
            # Limit packet count if specified
            if num_packets is not None:
                packets = packets[:num_packets]
            
            self.log.info(f"Running GAXI sequence '{sequence.name}' ({len(packets)} packets)")
            
            # Send each packet
            for i, packet in enumerate(packets):
                cmd_str = "WRITE" if packet.cmd == 1 else "READ"
                addr_str = f"addr=0x{packet.addr:08X}"
                data_str = f", data=0x{packet.data:08X}" if packet.cmd == 1 else ""
                
                self.log.info(f"GAXI {i+1}/{len(packets)}: {cmd_str} {addr_str}{data_str}")
                
                # Send through GAXI master
                await self.gaxi_master.send(packet)
                
                # Add delay between packets if specified
                if i < len(packets) - 1 and hasattr(sequence, 'delay_seq') and sequence.delay_seq:
                    delay = sequence.delay_seq[i % len(sequence.delay_seq)]
                    if delay > 0:
                        await self.wait_clocks('pclk', delay)
            
            # Wait for any pending transactions to complete
            await self.wait_clocks('pclk', 20)
            
            self.log.info(f"GAXI sequence '{sequence.name}' completed")
            
            return True
        
        except Exception as e:
            self.log.error(f"Error running GAXI sequence: {str(e)}")
            return False
        
        finally:
            # Stop command handler
            await self.command_handler.stop()
    
    async def verify_scoreboards(self):
        """
        Verify all scoreboards.
        
        Returns:
            True if all scoreboards pass, False otherwise
        """
        # Wait a bit for any pending transactions
        await self.wait_clocks('pclk', 10)
        
        # Check GAXI scoreboard
        gaxi_result = await self.gaxi_scoreboard.check_scoreboard()
        self.log.info(self.gaxi_scoreboard.report())
        
        # Check APB-GAXI scoreboard
        apb_gaxi_result = await self.apb_gaxi_scoreboard.check_scoreboard()
        self.log.info(self.apb_gaxi_scoreboard.report())
        
        # Return overall result
        return gaxi_result and apb_gaxi_result
    
    def dump_memory(self, base_addr=0, length=64):
        """
        Dump memory contents for debugging.
        
        Args:
            base_addr: Base address to start dump
            length: Number of bytes to dump
        """
        dump = self.mem.dump()
        self.log.info(f"Memory dump from 0x{base_addr:08X} ({length} bytes):")
        self.log.info(dump)
    
    async def test_basic_transfers(self):
        """Run a series of basic transfers."""
        self.log.info("Running basic transfers test")
        
        # Create alternating read/write sequence
        sequence = create_apb_sequence(
            name="basic",
            num_regs=10,
            base_addr=0,
            pattern="alternating",
            data_width=self.DATA_WIDTH
        )
        
        # Run sequence
        result = await self.run_apb_sequence(sequence)
        
        # Verify scoreboards
        scoreboard_result = await self.verify_scoreboards()
        
        self.log.info(f"Basic transfers test {'passed' if result and scoreboard_result else 'failed'}")
        return result and scoreboard_result
    
    async def test_burst_transfers(self):
        """Test burst transfers (back-to-back transactions)."""
        self.log.info("Running burst transfers test")
        
        # Create burst sequence
        sequence = create_apb_sequence(
            name="burst",
            num_regs=16,
            base_addr=0x100,
            pattern="burst",
            data_width=self.DATA_WIDTH
        )
        
        # Run sequence
        result = await self.run_apb_sequence(sequence)
        
        # Verify scoreboards
        scoreboard_result = await self.verify_scoreboards()
        
        # Dump memory
        self.dump_memory(base_addr=0x100, length=16*4)
        
        self.log.info(f"Burst transfers test {'passed' if result and scoreboard_result else 'failed'}")
        return result and scoreboard_result
    
    async def test_gaxi_transfers(self):
        """Test GAXI transfers directly."""
        self.log.info("Running GAXI transfers test")
        
        # Create GAXI sequence
        sequence = GAXISequence.create_alternating(
            name="gaxi_alternating",
            base_addr=0x200,
            num_registers=8,
            field_config=self.gaxi_field_config
        )
        
        # Run sequence
        result = await self.run_gaxi_sequence(sequence)
        
        # Verify scoreboards
        scoreboard_result = await self.verify_scoreboards()
        
        # Dump memory
        self.dump_memory(base_addr=0x200, length=8*4)
        
        self.log.info(f"GAXI transfers test {'passed' if result and scoreboard_result else 'failed'}")
        return result and scoreboard_result
    
    async def test_cross_protocol(self):
        """Test cross-protocol interaction (APB writes, GAXI reads and vice versa)."""
        self.log.info("Running cross-protocol test")
        
        # First, APB writes
        apb_write_sequence = create_apb_sequence(
            name="apb_writes",
            num_regs=8,
            base_addr=0x300,
            pattern="write_only",
            data_width=self.DATA_WIDTH
        )
        
        # Run APB writes
        apb_result = await self.run_apb_sequence(apb_write_sequence)
        
        # Then GAXI reads to same addresses
        gaxi_read_sequence = GAXISequence.create_address_sweep(
            name="gaxi_reads",
            base_addr=0x300,
            num_addresses=8,
            field_config=self.gaxi_field_config
        )
        
        # Run GAXI reads
        gaxi_result = await self.run_gaxi_sequence(gaxi_read_sequence)
        
        # Now GAXI writes to different addresses
        gaxi_write_sequence = GAXISequence.create_burst(
            name="gaxi_writes",
            base_addr=0x400,
            num_registers=8,
            field_config=self.gaxi_field_config
        )
        
        # Run GAXI writes
        gaxi_write_result = await self.run_gaxi_sequence(gaxi_write_sequence)
        
        # Finally APB reads from those addresses
        apb_read_sequence = create_apb_sequence(
            name="apb_reads",
            num_regs=8,
            base_addr=0x400,
            pattern="read_only",
            data_width=self.DATA_WIDTH
        )
        
        # Run APB reads
        apb_read_result = await self.run_apb_sequence(apb_read_sequence)
        
        # Verify scoreboards
        scoreboard_result = await self.verify_scoreboards()
        
        # Overall result
        overall_result = (apb_result and gaxi_result and 
                         gaxi_write_result and apb_read_result and 
                         scoreboard_result)
        
        self.log.info(f"Cross-protocol test {'passed' if overall_result else 'failed'}")
        return overall_result
    
    async def test_strobe_functionality(self):
        """Test byte strobe functionality."""
        self.log.info("Running strobe functionality test")
        
        # Create strobe sequence
        sequence = create_apb_sequence(
            name="strobe",
            num_regs=8,
            base_addr=0x500,
            pattern="strobe",
            data_width=self.DATA_WIDTH
        )
        
        # Run sequence
        result = await self.run_apb_sequence(sequence)
        
        # Verify scoreboards
        scoreboard_result = await self.verify_scoreboards()
        
        # Dump memory
        self.dump_memory(base_addr=0x500, length=8*4)
        
        self.log.info(f"Strobe functionality test {'passed' if result and scoreboard_result else 'failed'}")
        return result and scoreboard_result
    
    async def stress_test(self, num_transactions=100):
        """Run a stress test with many random transactions."""
        self.log.info(f"Running stress test with {num_transactions} transactions")
        
        # Create stress sequence
        sequence = create_apb_sequence(
            name="stress",
            num_regs=20,
            base_addr=0x600,
            pattern="stress",
            data_width=self.DATA_WIDTH
        )
        
        # Run sequence
        result = await self.run_apb_sequence(sequence, num_transactions)
        
        # Verify scoreboards
        scoreboard_result = await self.verify_scoreboards()
        
        self.log.info(f"Stress test {'passed' if result and scoreboard_result else 'failed'}")
        return result and scoreboard_result
    
    async def run_test(self):
        # sourcery skip: merge-dict-assign, move-assign-in-block
        """Main test executor."""
        try:
            results = {}
            
            print('# Test 1: Basic transfers')
            self.log.info("=== Test 1: Basic transfers ===")
            results['basic'] = await self.test_basic_transfers()
            
            print('# Test 2: Burst transfers')
            self.log.info("=== Test 2: Burst transfers ===")
            results['burst'] = await self.test_burst_transfers()
            
            print('# Test 3: GAXI transfers')
            self.log.info("=== Test 3: GAXI transfers ===")
            results['gaxi'] = await self.test_gaxi_transfers()
            
            print('# Test 4: Cross-protocol transfers')
            self.log.info("=== Test 4: Cross-protocol transfers ===")
            results['cross'] = await self.test_cross_protocol()
            
            print('# Test 5: Strobe functionality')
            self.log.info("=== Test 5: Strobe functionality ===")
            results['strobe'] = await self.test_strobe_functionality()
            
            print('# Test 6: Stress test')
            self.log.info("=== Test 6: Stress test ===")
            results['stress'] = await self.stress_test(50)
            
            # Print summary
            self.log.info("=== Test Summary ===")
            for name, result in results.items():
                self.log.info(f"Test {name}: {'PASSED' if result else 'FAILED'}")
            
            all_passed = all(results.values())
            self.log.info(f"Overall: {'PASSED' if all_passed else 'FAILED'}")
            
            return all_passed
            
        finally:
            # Set done flag to terminate handlers
            self.done = True
            # Wait for the tasks to complete
            await self.wait_clocks('pclk', 10)


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def apb_slave_enhanced_test(dut):
    tb = APBSlaveEnhancedTB(dut)
    
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    
    # Start the clock
    print('Starting clk')
    await tb.start_clock('pclk', 10, 'ns')
    
    # Reset the DUT
    print('DUT reset')
    await tb.reset_dut()

    # Run the test
    print('Run the test')
    passed = await tb.run_test()
    await tb.wait_clocks('pclk', 50)
    
    if passed:
        tb.log.info("All tests passed successfully!")
    else:
        tb.log.error("Some tests failed. See logs for details.")
    
    # Print test summary
    print("APB Slave Enhanced test completed")
    print("Verified APB slave command/response interface with GAXI components")
    print("Used factories and enhanced components for integration")
    
    assert passed, "Test failed!"


@pytest.mark.parametrize("addr_width, data_width, depth", 
    [
        (
            32,  # addr_width
            32,  # data_width
            2,   # depth
        )
    ])
def test_apb_slave_enhanced(request, addr_width, data_width, depth):
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_axi'], "axi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi'], "apb_slave.sv")
    ]

    # create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_enhanced_aw{aw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it int he simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["addr_width", "data_width", "depth"]}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        # 'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add test parameters; these are passed to the environment, but not the RTL
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure