import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from Components.memory_model import MemoryModel
from Components.flex_randomizer import FlexRandomizer
from Components.apb import APBSequence, APBCycle, APBTransaction, APBMonitor, APBMaster
from TBClasses.tbbase import TBBase
from TBClasses.utilities import get_paths, create_view_cmd


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
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)

        # Create the APB Monitor
        self.apb_monitor = APBMonitor(
            dut, 
            's_apb', 
            dut.pclk, 
            bus_width=self.DATA_WIDTH, 
            addr_width=self.ADDR_WIDTH, 
            log=self.log
        )

        # Create the APB Master
        self.apb_master_randomizer = FlexRandomizer({
            'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
            'penable': ([[0, 0], [1, 3]], [3, 1]),
        })
        self.apb_master = APBMaster(
            dut,
            'APB Master',
            's_apb', 
            dut.pclk,
            bus_width=self.DATA_WIDTH, 
            addr_width=self.ADDR_WIDTH,
            randomizer=self.apb_master_randomizer
        )

        self.other_randomizer = FlexRandomizer({
            'cmd_delay': ([(0, 1), (2, 5)], [3, 1]),
            'rsp_delay': ([(0, 1), (2, 5)], [3, 1]),
            'slv_error': ([(0, 0), (1, 1)], [9, 1]),
        })

        # Initialize queues for monitoring and verification
        self.apb_monitor_queue = deque()
        self.cmd_interface_queue = deque()
        self.rsp_interface_queue = deque()
        self.current_apb_transaction = None

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
        
        # Hold reset for multiple cycles
        await self.wait_clocks('pclk', 5)
        
        # Release reset
        self.dut.presetn.value = 1
        
        # Wait for stabilization
        await self.wait_clocks('pclk', 10)
        
        # Clear tracking variables
        self.current_apb_transaction = None
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

    async def cmd_rsp_interface(self, use_rand=False):
        # sourcery skip: move-assign
        if use_rand:
            rand_dict = self.other_randomizer.next()
            self.log.debug(f'{rand_dict=}')
            crand  = rand_dict['cmd_delay']
            rrand  = rand_dict['rsp_delay']
            slverr = rand_dict['slv_error']
        else:
            crand = 0
            rrand = 0
            slverr = 0
    
        while self.dut.o_cmd_valid.value == 0:
            await self.wait_clocks('pclk', 1)
        start_time = get_sim_time('ns')
        pwrite = int(self.dut.o_cmd_pwrite.value)
        paddr  = int(self.dut.o_cmd_paddr.value)
        pwdata = int(self.dut.o_cmd_pwdata.value)
        pstrb  = int(self.dut.o_cmd_pstrb.value)
        pprot  = int(self.dut.o_cmd_pprot.value) if hasattr(self.dut, "o_cmd_pprot") else 0
    
        if pwrite == 1:
            direction = "WRITE"
            pwdata_ba = self.mem.integer_to_bytearray(pwdata, self.STRB_WIDTH)
            self.mem.write(paddr & 0xFFF, pwdata_ba, pstrb)
            prdata = 0
        else:
            direction = "READ"
            prdata_ba = self.mem.read(paddr & 0xFFF, self.STRB_WIDTH)
            prdata = self.mem.bytearray_to_integer(prdata_ba)
    
        current = APBCycle(
                start_time=start_time,
                count=0,
                direction=direction,
                pwrite=pwrite,
                paddr=paddr,
                pwdata=pwdata,
                pstrb=pstrb,
                prdata=prdata,
                pprot=pprot,
                pslverr=slverr,
        )
        # wait for cmd delay
        await self.wait_clocks('pclk', crand)
    
        # accept the command
        self.dut.i_cmd_ready.value = 1
        await self.wait_clocks('pclk', 1)
        self.dut.i_cmd_ready.value = 0
    
        # wait for rsp delay
        await self.wait_clocks('pclk', rrand)
    
        # give the response
        self.dut.i_rsp_valid.value = 1
        self.dut.i_rsp_prdata.value = prdata
        self.dut.i_rsp_pslverr.value = slverr
        await self.wait_clocks('pclk', 1)
        
        while self.dut.o_rsp_ready.value == 0:
            await self.wait_clocks('pclk', 1)
        
        # Clear the response valid signal after it's been accepted
        self.dut.i_rsp_valid.value = 0
    
        return current

    async def verify_cmd_rsp_against_apb_monitor(self, cmd_rsp_cycle, timeout=1000):
        """
        Verify that the cmd/rsp cycle matches with APB monitor
        
        Args:
            cmd_rsp_cycle (APBCycle): The cycle from cmd_rsp_interface to verify
            timeout (int): Maximum time to wait for a matching cycle
        
        Returns:
            bool: True if a match was found, False if timeout
        """
        start_time = get_sim_time('ns')
        
        while True:
            # Check if we've exceeded timeout
            current_time = get_sim_time('ns')
            if current_time - start_time > timeout:
                msg = f"Timeout waiting for matching APB cycle after {timeout}ns"
                self.log.error(msg)
                return False
            
            # Check if we have any APB transactions to compare against
            if self.apb_monitor._recvQ:
                monitor_cycle = self.apb_monitor._recvQ.popleft()
                if monitor_cycle == cmd_rsp_cycle:
                    msg = f"Found matching APB cycle for cmd/rsp interface transaction at {start_time}ns"
                    self.log.info(msg)
                    return monitor_cycle
                else:
                    assert cmd_rsp_cycle == monitor_cycle, \
                        f'Cycle mismatch at {start_time}ns:\nExpected:\n{monitor_cycle}\nFound:\n{cmd_rsp_cycle}'

            # Wait a cycle before checking again
            await self.wait_clocks('pclk', 1)

    async def send_apb_transaction(self, is_write, addr, data=None, strobe=None):
        """Send an APB transaction and verify cmd/rsp interface handling"""
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
            self.log.debug(msg)
                
            # Set the strobe value
            xmit_transaction.pstrb = strobe if strobe is not None else (2**self.STRB_WIDTH - 1)  # All bytes enabled
            msg = f"Setting transaction pstrb to 0x{xmit_transaction.pstrb:X}"
            self.log.debug(msg)
        
        # Log the transaction details
        self.log.info(f"Sending {'write' if is_write else 'read'} to addr 0x{addr:08X}" + 
                        (f" with data 0x{xmit_transaction.pwdata:08X} strobe 0x{xmit_transaction.pstrb:X}" if is_write else ""))
    
        # Record transaction start time
        xmit_transaction.start_time = start_time
    
        # Start a concurrent task to handle cmd/rsp interface
        cmd_rsp_task = cocotb.start_soon(self.cmd_rsp_interface(use_rand=True))
        
        # Send the transaction
        await self.apb_master.send(xmit_transaction)
    
        # Wait for the master's queue to be empty
        await self.wait_for_queue_empty(self.apb_master, timeout=10000)
        
        # Get the cmd/rsp cycle
        cmd_rsp_cycle = await cmd_rsp_task
        
        # Verify the cmd/rsp cycle matches what was monitored by APB monitor
        return await self.verify_cmd_rsp_against_apb_monitor(cmd_rsp_cycle)

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
        save_other_randomizer = None

        # Apply custom timing constraints if provided
        if config.master_randomizer:
            save_master_randomizer = self.apb_master_randomizer
            self.apb_master_randomizer = config.master_randomizer
            self.apb_master.set_randomizer(self.apb_master_randomizer)

        if config.other_randomizer:
            save_other_randomizer = self.other_randomizer
            self.other_randomizer = config.other_randomizer
            
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
                    
                    # Verify read data if needed
                    if config.verify_data:
                        # Read from memory model
                        expected_ba = self.mem.read(addr & 0xFFF, self.STRB_WIDTH)
                        expected = self.mem.bytearray_to_integer(expected_ba)
                        
                        assert result.prdata == expected, \
                            f"Data mismatch at addr 0x{addr:08X}: expected 0x{expected:08X}, got 0x{result.prdata:08X}"
                
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
            
            if save_other_randomizer:
                self.other_randomizer = save_other_randomizer

        return results

    # Test methods using predefined configurations
    def _create_basic_config(self):
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
    
    def _create_burst_config(self):
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
            }),
            other_randomizer=FlexRandomizer({
                'cmd_delay': ([(0, 1), (2, 5)], [3, 1]),
                'rsp_delay': ([[0, 1], [2, 5], [6, 10]], [5, 2, 1]),
                'slv_error': ([[0, 0], [1, 1]], [10, 0]),
            })
        )

    def _create_strobe_config(self):
        # sourcery skip: merge-list-append, move-assign-in-block
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
    
    def _create_stress_config(self, num_transactions=100):
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
            use_random_selection=True,  # Randomly select from sequences
            verify_data=True
        )

    async def test_basic_transfers(self):
        """Run a series of basic transfers"""
        self.log.info("Running basic transfers test")
        
        # Create and run basic test configuration
        config = self._create_basic_config()
        await self.run_apb_test(config)
        
        self.log.info("Basic transfers test completed")

    async def test_burst_transfers(self):
        """Test burst transfers (back-to-back transactions)"""
        self.log.info("Running burst transfers test")
        
        # Create and run burst test configuration
        config = self._create_burst_config()
        await self.run_apb_test(config)
        
        # Optional: dump memory for debugging
        await self.wait_clocks('pclk', 5)
        mem_dump = self.mem.dump()
        self.log.info(f'Burst test memory dump:\n{mem_dump}')
        
        self.log.info("Burst transfers test completed")

    async def test_strobe_functionality(self):
        """Test byte strobe functionality"""
        self.log.info("Running strobe functionality test")
        
        # Create and run strobe test configuration
        config = self._create_strobe_config()
        await self.run_apb_test(config)
        
        self.log.info("Strobe functionality test completed")

    async def stress_test(self, num_transactions=100):
        """Run a stress test with many random transactions"""
        self.log.info(f"Running stress test with {num_transactions} transactions")
        
        # Create and run stress test configuration
        config = self._create_stress_config(num_transactions)
        await self.run_apb_test(config, num_transactions)
        
        self.log.info("Stress test completed successfully")

    async def run_test(self):
        """Main test executor"""
        try:
            print('# Test 2: Burst transfers without clock gating')
            self.log.info("=== Test 2: Burst transfers without clock gating ===")
            await self.test_burst_transfers()
            
            print('# Test 3: Strobe functionality without clock gating')
            self.log.info("=== Test 3: Strobe functionality without clock gating ===")
            await self.test_strobe_functionality()

            print('# Test 4: Stress test')
            self.log.info("=== Test 4: Stress test ===")
            await self.stress_test(100)

        finally:
            # Set done flag to terminate handlers
            self.done = True
            # Wait for the tasks to complete
            await self.wait_clocks('pclk', 10)

@cocotb.test(timeout_time=1, timeout_unit="ms")
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

    # Run the test
    print('Run the test')
    await tb.run_test()
    await tb.wait_clocks('pclk', 50)
    tb.log.info("Test completed successfully.")
    
    # Print test summary
    print("APB Slave test completed successfully!")
    print("Verified that command interface signals match APB bus signals for writes")
    print("Verified that response interface signals match APB bus signals for reads")


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
        os.path.join(rtl_dict['rtl_axi'], "axi_skid_buffer.sv"),
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

    # Add test parameters; these are passed t the environment, but not the RTL
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
