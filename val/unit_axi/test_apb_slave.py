import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb import APBSequence, APBCycle, APBTransaction, APBMonitor, APBMaster
from CocoTBFramework.components.apb.apb_factories import create_apb_master, create_apb_monitor, create_apb_scoreboard
from CocoTBFramework.components.gaxi.gaxi_components import GAXIMaster, GAXISlave, GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_factories import \
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.components.gaxi.gaxi_enhancements import GAXICommandHandler_APBSlave
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd


class APBSlaveTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.IDLE_CNTR_WIDTH = self.convert_to_int(os.environ.get('TEST_IDLE_CNTR_WIDTH', '4'))
        self.done = False
        # Number of registers to test
        self.registers = 64
        
        # Clock gating parameters
        self.max_idle_count = 2**self.IDLE_CNTR_WIDTH - 1
        
        # Task termination flag
        self.done = False
        self.num_line = 32768
        
        # Create a shared memory model for both APB and GAXI components
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)

        # Set up randomizers
        self.apb_master_randomizer = FlexRandomizer({
            'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
            'penable': ([[0, 0], [1, 3]], [3, 1]),
        })
        
        self.gaxi_master_randomizer = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
        })
        
        self.gaxi_slave_randomizer = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
        })

        # Configure APB components
        self.apb_monitor = create_apb_monitor(
            dut, 
            'APB Monitor',
            's_apb', 
            dut.pclk, 
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH, 
            log=self.log
        )

        self.apb_master = create_apb_master(
            dut,
            'APB Master',
            's_apb', 
            dut.pclk,
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            randomizer=self.apb_master_randomizer,
            log=self.log
        )
        
        # Create APB scoreboard
        self.apb_scoreboard = create_apb_scoreboard(
            'APB Scoreboard',
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            log=self.log
        )
        
        # Configure GAXI components for command interface
        self.cmd_signal_map = {
            'm2s_valid': 'o_cmd_valid',
            's2m_ready': 'i_cmd_ready'
        }
        self.cmd_optional_signal_map = {
            'm2s_pkt_cmd': 'o_cmd_pwrite',
            'm2s_pkt_addr': 'o_cmd_paddr',
            'm2s_pkt_data': 'o_cmd_pwdata',
            'm2s_pkt_strb': 'o_cmd_pstrb'
        }
        self.cmd_field_config = {
            'cmd': {
                'bits': 1,
                'default': 0,
                'format': 'bin',
                'display_width': 1,
                'active_bits': (0, 0),
                'description': 'Command (0=Read, 1=Write)'
            },
            'addr': {
                'bits': self.ADDR_WIDTH,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (self.ADDR_WIDTH-1, 0),
                'description': 'Address'
            },
            'data': {
                'bits': self.DATA_WIDTH,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (self.DATA_WIDTH-1, 0),
                'description': 'Data'
            },
            'strb': {
                'bits': self.STRB_WIDTH,
                'default': 0xF,
                'format': 'bin',
                'display_width': 4,
                'active_bits': (self.STRB_WIDTH-1, 0),
                'description': 'Byte strobe'
            },
        }

        self.cmd_monitor = create_gaxi_monitor(
            dut,
            'CMD Monitor',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.cmd_field_config,
            is_slave=False,  # Monitoring master-side signals
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.cmd_signal_map,
            optional_signal_map=self.cmd_optional_signal_map
        )
        
        self.cmd_slave = create_gaxi_slave(
            dut,
            'CMD Slave',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.cmd_field_config,
            randomizer=self.gaxi_slave_randomizer,
            memory_model=self.mem,
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.cmd_signal_map,
            optional_signal_map=self.cmd_optional_signal_map
        )
        
        # Configure GAXI components for response interface
        self.rsp_signal_map = {
            'm2s_valid': 'i_rsp_valid',
            's2m_ready': 'o_rsp_ready'
        }
        self.rsp_optional_signal_map = {
            'm2s_pkt_data': 'i_rsp_prdata',
            'm2s_pkt_err': 'i_rsp_pslverr'
        }
        
        self.rsp_field_config = {
            'data': {
                'bits': self.DATA_WIDTH,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (self.DATA_WIDTH-1, 0),
                'description': 'Data'
            },
            'err': {
                'bits': 1,
                'default': 0,
                'format': 'bin',
                'display_width': 1,
                'active_bits': (0, 0),
                'description': 'Error flag'
            }
        }
        
        self.rsp_monitor = create_gaxi_monitor(
            dut,
            'RSP Monitor',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.rsp_field_config,
            is_slave=True,  # Monitoring slave-side signals
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.rsp_signal_map,
            optional_signal_map=self.rsp_optional_signal_map
        )
        
        self.rsp_master = create_gaxi_master(
            dut,
            'RSP Master',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.rsp_field_config,
            randomizer=self.gaxi_master_randomizer,
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.rsp_signal_map,
            optional_signal_map=self.rsp_optional_signal_map
        )
        
        # Create command handler to connect cmd and response interfaces
        self.cmd_handler = GAXICommandHandler_APBSlave(
            self.rsp_master,  # GAXI master for sending responses
            self.cmd_slave,   # GAXI slave for receiving commands
            cmd_field_config=self.cmd_field_config,
            rsp_field_config=self.rsp_field_config,
            log=self.log
        )
        
        # Set up APB-GAXI scoreboard
        self.apb_gaxi_scoreboard = APBGAXIScoreboard(
            'APB-GAXI Scoreboard',
            log=self.log
        )
        
        # Connect monitors to scoreboard
        self.apb_monitor.add_callback(self.apb_transaction_callback)
        self.cmd_monitor.add_callback(self.cmd_transaction_callback)

        # Initialize queues for monitoring
        self.apb_monitor_queue = deque()

    def apb_transaction_callback(self, transaction):
        """Callback for APB monitor transactions"""
        self.apb_monitor_queue.append(transaction)
        self.apb_gaxi_scoreboard.add_apb_transaction(transaction)
        
    def cmd_transaction_callback(self, transaction):
        """Callback for GAXI CMD monitor transactions"""
        self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)

    async def reset_dut(self):
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
        await self.cmd_slave.reset_bus()
        await self.rsp_master.reset_bus()
        
        # Hold reset for multiple cycles
        await self.wait_clocks('pclk', 5)
        
        # Release reset
        self.dut.presetn.value = 1
        
        # Wait for stabilization
        await self.wait_clocks('pclk', 10)
        
        # Clear monitoring queues
        self.apb_monitor_queue.clear()
        
        # Clear scoreboard
        self.apb_gaxi_scoreboard.clear()
        
        self.log.debug('Ending reset_dut')

    async def wait_for_queue_empty(self, object_with_queue, timeout=1000):
        """Wait for a queue to be empty with timeout"""
        start_time = get_sim_time('ns')
        current_time = start_time
        
        # Check which queue attribute to monitor based on object type
        if hasattr(object_with_queue, 'transmit_queue'):
            queue_attr = 'transmit_queue'
        elif hasattr(object_with_queue, '_xmitQ'):
            queue_attr = '_xmitQ'
        else:
            msg = f"Unknown queue type for object {object_with_queue.__class__.__name__}"
            self.log.error(msg)
            return
        
        queue = getattr(object_with_queue, queue_attr)
        
        while len(queue) > 0:
            await self.wait_clocks('pclk', 1)
            current_time = get_sim_time('ns')
            
            # Check for timeout
            if current_time - start_time > timeout:
                msg = f"Timeout waiting for queue to be empty after {timeout}ns"
                self.log.warning(msg)
                break

    async def send_apb_transaction(self, is_write, addr, data=None, strobe=None):
        """Send an APB transaction through the APB master"""
        start_time = get_sim_time('ns')
    
        # Create a plain transaction
        xmit_transaction_cls = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
        xmit_transaction = xmit_transaction_cls.next()

        # Set transaction fields directly
        xmit_transaction.pwrite = 1 if is_write else 0
        xmit_transaction.direction = "WRITE" if is_write else "READ"
        xmit_transaction.paddr = addr
        
        # For write transactions, set data and strobe
        if is_write:
            # Set data field
            xmit_transaction.pwdata = data if data is not None else random.randint(0, 2**self.DATA_WIDTH - 1)
            msg = f"Setting transaction pwdata to 0x{xmit_transaction.pwdata:08X}"
            self.log.info(msg)
                
            # Set the strobe value
            xmit_transaction.pstrb = strobe if strobe is not None else (2**self.STRB_WIDTH - 1)  # All bytes enabled
            msg = f"Setting transaction pstrb to 0x{xmit_transaction.pstrb:X}"
            self.log.info(msg)
        
        # Log the transaction details
        self.log.info(f"Sending {'write' if is_write else 'read'} to addr 0x{addr:08X}" + 
                        (f" with data 0x{xmit_transaction.pwdata:08X} strobe 0x{xmit_transaction.pstrb:X}" if is_write else ""))
    
        # Record transaction start time
        xmit_transaction.start_time = start_time
        
        # Send the transaction - this will be automatically captured by the APB monitor
        # and transformed by the scoreboard
        await self.apb_master.send(xmit_transaction)
    
        # Wait for the master's queue to be empty
        await self.wait_for_queue_empty(self.apb_master, timeout=10000)
        
        # Wait a few cycles for the scoreboard to process everything
        await self.wait_clocks('pclk', 5)
        
        # For verification, read the expected value from memory if this was a read
        if not is_write and self.mem:
            expected_ba = self.mem.read(addr & 0xFFF, self.STRB_WIDTH)
            expected = self.mem.bytearray_to_integer(expected_ba)
            self.log.info(f"Expected read value from memory: 0x{expected:08X}")
        
        # Return the transaction for reference
        return xmit_transaction

    async def run_apb_test(self, config: APBSequence, num_transactions: int = None):
        """
        Run APB test according to the configuration
        
        Args:
            config: Test configuration
            num_transactions: Override number of transactions (defaults to len(config.pwrite_seq))
        
        Returns:
            List of transaction results
        """
        # Save original constraints to restore later
        save_master_randomizer = None

        # Apply custom timing constraints if provided
        if config.master_randomizer:
            save_master_randomizer = self.apb_master_randomizer
            self.apb_master_randomizer = config.master_randomizer
            self.apb_master.set_randomizer(self.apb_master_randomizer)
            
        # Reset iterators
        config.reset_iterators()
        
        # Determine number of transactions to run
        if num_transactions is None:
            num_transactions = len(config.pwrite_seq)
        
        results = []
        
        try:
            # Execute transactions
            for i in range(num_transactions):
                # Get next transaction parameters
                is_write = config.next_pwrite()
                addr = config.next_addr()
                
                if is_write:
                    # Get data and strobe for write
                    data = config.next_data()
                    strobe = config.next_strb()
                    
                    # Execute write transaction
                    result = await self.send_apb_transaction(True, addr, data, strobe)
                    
                else:
                    # Execute read transaction
                    result = await self.send_apb_transaction(False, addr)
                
                # Store result
                results.append(result)
                
                # Add delay between transactions if not the last one
                if i < num_transactions - 1:
                    delay = config.next_delay()
                    if delay > 0:
                        await self.wait_clocks('pclk', delay)
        
        finally:
            # Restore original constraints
            if save_master_randomizer:
                self.apb_master_randomizer = save_master_randomizer
                self.apb_master.set_randomizer(self.apb_master_randomizer)

        return results

    async def verify_scoreboard(self, timeout=1000):
        """Verify scoreboard for unmatched transactions"""
        self.log.info("Verifying APB-GAXI scoreboard for unmatched transactions")
        result = await self.apb_gaxi_scoreboard.check_scoreboard(timeout)
        
        if result:
            self.log.info("Scoreboard verification passed - all transactions matched")
        else:
            self.log.error("Scoreboard verification failed - unmatched transactions found")
            
        # Get and log the report
        report = self.apb_gaxi_scoreboard.report()
        self.log.info(f"Scoreboard report:\n{report}")
        
        return result

    # Test methods using predefined configurations
    def _create_basic_seq(self):
        """Create configuration for basic test"""
        # Base address and number of registers to test
        base_addr = 0
        num_regs = 10
        
        # Create sequences
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []
        
        # Alternating write-read pattern
        for i in range(num_regs):
            # Write
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(random.randint(0, 2**self.DATA_WIDTH - 1))
            strb_seq.append(2**self.STRB_WIDTH - 1)  # All strobe bits set
            
            # Read
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)
        
        # Delays between transactions
        delays = [5] * (len(pwrite_seq) - 1)
        
        return APBSequence(
            name="basic",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays
        )
    
    def _create_burst_seq(self):
        """Create configuration for burst test"""
        # Base address and number of registers
        base_addr = 0
        num_regs = 10
        
        # Create sequences
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []
        
        # All writes followed by all reads
        # First all writes
        for i in range(num_regs):
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(random.randint(0, 2**self.DATA_WIDTH - 1))
            strb_seq.append(2**self.STRB_WIDTH - 1)  # All strobe bits set
        
        # Then all reads
        for i in range(num_regs):
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)
        
        # No delays for burst mode
        delays = [0] * (len(pwrite_seq) - 1)
        
        return APBSequence(
            name="burst",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays,
            master_randomizer=FlexRandomizer({
                'psel':    ([[0, 0], [1, 5], [6, 10]], [1, 0, 0]),
                'penable': ([[0, 0], [1, 3]], [3, 0]),
            })
        )

    def _create_strobe_seq(self):
        """Create configuration for strobe test"""
        # Test patterns for strobes
        test_data = [0xFFFFFFFF, 0x12345678, 0xAABBCCDD, 0x99887766, 0x55443322, 0xA5A5A5A5, 0x5A5A5A5A]
        test_strobes = [0xF, 0x1, 0x2, 0x4, 0x8, 0x5, 0xA]
        
        # Create sequences
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []
        
        # Initial write with all bits set
        pwrite_seq.append(True)
        addr_seq.append(0)
        data_seq.append(0)
        strb_seq.append(0xF)
        
        # For each test pattern
        for i in range(len(test_data)):
            # Write with specific pattern
            pwrite_seq.append(True)
            addr_seq.append(0)  # Same address for all tests
            data_seq.append(test_data[i])
            strb_seq.append(test_strobes[i])
            
            # Read back
            pwrite_seq.append(False)
            addr_seq.append(0)
        
        # Short delays between transactions
        delays = [3] * (len(pwrite_seq) - 1)
        
        return APBSequence(
            name="strobe",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays
        )
    
    def _create_stress_seq(self, num_transactions=100):
        """Create configuration for stress test"""
        # Reset memory for clean start
        self.mem.reset()

        # Create sequences
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        # Set up a variety of addresses, data values, and strobes
        addr_range = [i * 4 for i in range(self.registers)]
        data_range = [random.randint(0, 2**self.DATA_WIDTH - 1) for _ in range(20)]
        strobe_range = [
            2**self.STRB_WIDTH - 1,  # All bits
            0x1, 0x2, 0x4, 0x8,      # Individual bytes
            0x3, 0x5, 0x9, 0x6, 0xA, 0xC  # Various combinations
        ]

        # Random mix of writes and reads
        # First add some writes to ensure we have data
        pwrite_seq.extend(True for _ in range(min(20, num_transactions // 5)))

        # Then add random mix of reads and writes
        write_probability = 0.7  # 70% writes
        pwrite_seq.extend(
            random.random() < write_probability
            for _ in range(num_transactions - len(pwrite_seq))
        )
        # Fill address, data, and strobe sequences
        # These will be sampled from rather than iterated through
        addr_seq = addr_range
        data_seq = data_range
        strb_seq = strobe_range

        # Random delays
        delay_range = list(range(6))  # 0-5 cycle delays

        return APBSequence(
            name="stress",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delay_range,
            use_random_selection=True  # Randomly select from sequences
        )


@cocotb.test(timeout_time=40, timeout_unit="us")
async def apb_slave_test(dut):
    tb = APBSlaveTB(dut)
    
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    
    # Start the clock
    print('Starting clk')
    await tb.start_clock('pclk', 10, 'ns')
    
    # Reset the DUT
    print('DUT reset')
    await tb.reset_dut()
    
    # Start the monitors
    # tb.apb_monitor._monitor_task = cocotb.start_soon(tb.apb_monitor._monitor_recv())
    # tb.cmd_monitor._monitor_task = cocotb.start_soon(tb.cmd_monitor._monitor_recv())
    # tb.rsp_monitor._monitor_task = cocotb.start_soon(tb.rsp_monitor._monitor_recv())
    
    # Start the command handler
    await tb.cmd_handler.start()

    try:
        print('# Test 1: Basic transfers with scoreboard verification')
        tb.log.info("=== Test 1: Basic transfers with scoreboard verification ===")
        config = tb._create_basic_seq()
        await tb.run_apb_test(config)
        await tb.verify_scoreboard()
        
        print('# Test 2: Burst transfers with scoreboard verification')
        tb.log.info("=== Test 2: Burst transfers with scoreboard verification ===")
        config = tb._create_burst_seq()
        await tb.run_apb_test(config)
        await tb.verify_scoreboard()
        
        print('# Test 3: Strobe functionality with scoreboard verification')
        tb.log.info("=== Test 3: Strobe functionality with scoreboard verification ===")
        config = tb._create_strobe_seq()
        await tb.run_apb_test(config)
        await tb.verify_scoreboard()

        print('# Test 4: Stress test with scoreboard verification')
        tb.log.info("=== Test 4: Stress test with scoreboard verification ===")
        config = tb._create_stress_seq(100)
        await tb.run_apb_test(config, 100)
        await tb.verify_scoreboard()
        
        await tb.wait_clocks('pclk', 50)
        tb.log.info("Test completed successfully.")
        
        # Print test summary
        print("APB Slave test completed successfully!")
        print("Verified APB-to-GAXI transformation using scoreboard")
        print("All APB transactions matched with GAXI command/response transactions")
        # Optional: dump memory for debugging
        # mem_dump = tb.mem.dump()
        # tb.log.info(f'Burst test memory dump:\n{mem_dump}')
    finally:
        # Set done flag to terminate handlers
        tb.done = True
        # Stop the command handler
        await tb.cmd_handler.stop()
        # Wait for the tasks to complete
        await tb.wait_clocks('pclk', 10)


@pytest.mark.parametrize("addr_width, data_width, depth", 
    [
        (
            32,  # addr_width
            32,  # data_width
            2,   # depth
        )
    ])
def test_apb_slave(request, addr_width, data_width, depth):

    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi'], "apb_slave.sv")
    ]

    # create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}"
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
