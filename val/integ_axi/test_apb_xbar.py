"""
APB Crossbar Test

This test verifies the behavior of an APB crossbar using different models:
- Feedthru model (simple pass-through)
- Thin model (basic routing)
- Full model (complete functionality)

Supports multiple masters and slaves based on parameters.
"""

import os
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

# Import TBBase and utility functions
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Import APB components
from CocoTBFramework.components.apb.apb_packet import APBTransaction
from CocoTBFramework.components.apb.apb_factories import (
    create_apb_master, create_apb_slave, create_apb_monitor, 
    create_apb_sequence
)

# Import APB scoreboard
from CocoTBFramework.scoreboards.apb_scoreboard import APBCrossbarScoreboard


class APBXbarTest(TBBase):
    """
    APB Crossbar Test Class

    This class tests an APB crossbar by sending transactions through
    and verifying correct behavior at the output.
    Supports multiple masters and slaves with different test models.
    """
    
    def __init__(self, dut):
        """
        Initialize the test class with DUT and configuration
        """
        super().__init__(dut)
        
        # Extract configuration from environment variables
        self.M = self.convert_to_int(os.environ.get('PARAM_M', '1'))
        self.S = self.convert_to_int(os.environ.get('PARAM_S', '1'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('PARAM_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '32'))
        self.strb_width = self.DATA_WIDTH // 8
        self.num_transactions = self.convert_to_int(os.environ.get('PARAM_NUM_TRANSACTIONS', '50'))
        self.clock_period = self.convert_to_int(os.environ.get('PARAM_CLOCK_PERIOD', '10'))
        self.reset_cycles = self.convert_to_int(os.environ.get('PARAM_RESET_CYCLES', '5'))
        self.model_type = os.environ.get('PARAM_MODEL_TYPE', 'feedthru').lower()
        
        # Test case selection
        self.test_basic = os.environ.get('PARAM_TEST_BASIC', 'True').lower() in ('true', '1', 'yes')
        self.test_sequence = os.environ.get('PARAM_TEST_SEQUENCE', 'True').lower() in ('true', '1', 'yes')
        self.test_mixed = os.environ.get('PARAM_TEST_MIXED', 'True').lower() in ('true', '1', 'yes')
        
        # Get optional test configurations
        self.use_coverage = os.environ.get('PARAM_USE_COVERAGE', 'False').lower() in ('true', '1', 'yes')
        self.randomize_delays = os.environ.get('PARAM_RANDOMIZE_DELAYS', 'True').lower() in ('true', '1', 'yes')
        self.error_injection = os.environ.get('PARAM_ERROR_INJECTION', 'False').lower() in ('true', '1', 'yes')
        self.seed = self.convert_to_int(os.environ.get('SEED', '0'))
        
        # Initialize random seed if provided
        if self.seed:
            random.seed(int(self.seed))
        
        # Component handles
        self.apb_masters = []
        self.apb_slaves = []
        self.apb_in_monitors = []
        self.apb_out_monitors = []
        
        # Address mapping for slaves
        self.addr_map = []
        for i in range(10):  # Support up to 10 slaves
            base_addr = i * 0x1000
            end_addr = base_addr + 0xFFC
            self.addr_map.append((base_addr, end_addr))
        
        # Test addresses - multiple addresses per slave range
        self.addresses = []
        for i in range(10):
            base_addr = i * 0x1000
            self.addresses.extend([base_addr, base_addr + 0x800, base_addr + 0xFFC])
        
        # Create crossbar scoreboard
        self.crossbar_scoreboard = APBCrossbarScoreboard(
            "APB_Xbar",
            self.S,
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            log=self.log
        )
        self.crossbar_scoreboard.set_address_map(self.addr_map[:self.S])
        
        # Log configuration
        self.log.info("Test configuration:")
        self.log.info(f"  Model type: {self.model_type}")
        self.log.info(f"  Masters: {self.M}")
        self.log.info(f"  Slaves: {self.S}")
        self.log.info(f"  Address width: {self.ADDR_WIDTH}")
        self.log.info(f"  Data width: {self.DATA_WIDTH}")
        self.log.info(f"  Transactions: {self.num_transactions}")
        self.log.info(f"  Random seed: {self.seed}")

    async def reset_dut(self):
        """Reset the device under test"""
        self.log.info("Resetting DUT")
        self.dut.presetn.value = 0
        for master in self.apb_masters:
            await master.reset_bus()
        for slave in self.apb_slaves:
            await slave.reset_bus()
        await self.wait_clocks('pclk', self.reset_cycles)
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', self.reset_cycles)
        self.log.info("Reset complete")

    async def create_components(self):
        """Create all APB components"""
        self.log.info("Creating APB components")

        # Create master constraints based on model type
        if self.model_type == 'thin':
            # Fast response for simple models
            master_constraints = {
                'psel':    ([[0, 0], [1, 2]], [5, 1]),
                'penable': ([[0, 0], [1, 1]], [4, 1]),
            }
        else:
            # More realistic timing for full model
            master_constraints = {
                'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
                'penable': ([[0, 0], [1, 2]], [4, 1]),
            }
        master_randomizer = FlexRandomizer(master_constraints)

        # Create APB masters
        for i in range(self.M):
            # Generate prefix based on master index
            master_prefix = f"m{i}_apb" if self.M > 1 else "m_apb"

            master = create_apb_master(
                self.dut, 
                f"APB_Master_{i}", 
                master_prefix, 
                self.dut.pclk, 
                addr_width=self.ADDR_WIDTH, 
                data_width=self.DATA_WIDTH, 
                randomizer=master_randomizer,
                log=self.log
            )
            self.apb_masters.append(master)

            # Create corresponding monitor and connect to master monitor callback
            monitor = create_apb_monitor(
                self.dut, 
                f"APB_Monitor_In_{i}", 
                master_prefix, 
                self.dut.pclk, 
                addr_width=self.ADDR_WIDTH, 
                data_width=self.DATA_WIDTH, 
                log=self.log
            )
            # Set up callback to track master transactions and set master source ID
            def master_monitor_callback(transaction, master_id=i):
                self.crossbar_scoreboard.add_master_transaction(transaction, master_id)

            # Add callback to master monitor
            monitor.add_callback(master_monitor_callback)
            self.apb_in_monitors.append(monitor)

        # Create slave constraints based on model type
        if self.model_type in ['feedthru', 'thin']:
            # Fast response for simple models
            slave_constraints = {
                'ready': ([[0, 0], [1, 1]], [5, 0]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
            }
        else:
            # More realistic timing for full model
            slave_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
            }

        slave_randomizer = FlexRandomizer(slave_constraints)

        # Create APB slaves with monitors
        for i in range(self.S):
            # Generate prefix based on slave index
            slave_prefix = f"s{i}_apb" if self.S > 1 else "s_apb"

            # Create slave registers
            slave_registers = list(range(self.DATA_WIDTH * self.strb_width))

            # Create the slave
            slave = create_apb_slave(
                self.dut,
                f"APB_Slave_{i}",
                slave_prefix,
                self.dut.pclk,
                registers=slave_registers,
                addr_width=self.ADDR_WIDTH,
                data_width=self.DATA_WIDTH,
                randomizer=slave_randomizer,
                log=self.log
            )
            self.apb_slaves.append(slave)

            # Create corresponding monitor and connect to slave scoreboard
            monitor = create_apb_monitor(
                self.dut, 
                f"APB_Monitor_Out_{i}", 
                slave_prefix, 
                self.dut.pclk, 
                addr_width=self.ADDR_WIDTH, 
                data_width=self.DATA_WIDTH, 
                log=self.log
            )

            # Set up callback to add transactions to slave scoreboard
            def slave_monitor_callback(transaction, slave_id=i):
                self.crossbar_scoreboard.add_slave_transaction(transaction, slave_id)

            # Add callback to slave monitor
            monitor.add_callback(slave_monitor_callback)
            self.apb_out_monitors.append(monitor)

        # Reset all components
        await self.reset_dut()

        # Wait for a few clock cycles after reset
        await self.wait_clocks('pclk', self.reset_cycles)

    async def wait_for_queue_empty(self, master, timeout=None):
        """Wait for master's transaction queue to empty"""
        start_time = get_sim_time('ns')
        while len(master.transmit_queue) > 0 or master.transfer_busy:
            if timeout and (get_sim_time('ns') - start_time) > timeout:
                raise TimeoutError(f"Timeout waiting for queue to empty after {timeout} ns")
            await RisingEdge(self.dut.pclk)

    async def run_test_basic(self):
        """Run basic transaction test"""
        self.log.info("Running basic APB crossbar transaction test")
        
        # Clear scoreboard before starting test
        self.crossbar_scoreboard.clear_all()
        
        # Generate and send test transactions
        # Round-robin between masters if multiple exist
        for i in range(self.num_transactions):
            # Select master in round-robin fashion
            master_idx = i % self.M
            master = self.apb_masters[master_idx]
            
            # Create transaction
            trans = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.strb_width)
            
            # Set slave address - round robin through slaves
            slave_idx = i % self.S
            addr_base = slave_idx * 0x1000
            addr_offset = (i // self.S) * 4 % 0xFFC  # 4-byte offset increments, wrap at 0xFFC
            trans.paddr = addr_base + addr_offset
            
            # Set pprot to indicate master source for verification
            trans.pprot = master_idx
            
            # Alternate between reads and writes
            trans.pwrite = i % 2
            trans.direction = "WRITE" if trans.pwrite else "READ"
            
            # Get cycle from transaction
            cycle = trans.next()
            
            # Send transaction through selected master
            self.log.info(f"Sending {'write' if trans.pwrite else 'read'} from master {master_idx} to addr 0x{trans.paddr:08X}")
            await master.busy_send(cycle)
            
            # Wait a few cycles between transactions
            delay = random.randint(1, 5)
            await self.wait_clocks('pclk', delay)
        
        # Wait for all masters' transaction queues to be empty
        for i, master in enumerate(self.apb_masters):
            self.log.info(f"Waiting for transaction queue of master {i} to empty...")
            await self.wait_for_queue_empty(master, timeout=10000)
        
        # Give time for transactions to complete
        await self.wait_clocks('pclk', 10)
        
        # Check results
        await self.check_results()

    async def run_test_sequence(self):
        """Run sequence-based test using APBSequence"""
        self.log.info("Running APB crossbar sequence test")
        
        # Clear scoreboard before starting test
        self.crossbar_scoreboard.clear_all()
        
        # Create test sequences
        sequences = [
            create_apb_sequence(
                name="alternating", 
                num_regs=10, 
                base_addr=0x000, 
                pattern="alternating", 
                data_width=self.DATA_WIDTH, 
                randomize_delays=self.randomize_delays
            ),
            create_apb_sequence(
                name="burst", 
                num_regs=8, 
                base_addr=0x1000, 
                pattern="burst", 
                data_width=self.DATA_WIDTH, 
                randomize_delays=False
            ),
            create_apb_sequence(
                name="strobe", 
                num_regs=5, 
                base_addr=0x2000, 
                pattern="strobe", 
                data_width=self.DATA_WIDTH, 
                randomize_delays=self.randomize_delays
            ),
            create_apb_sequence(
                name="stress", 
                num_regs=15, 
                base_addr=0x3000, 
                pattern="stress", 
                data_width=self.DATA_WIDTH, 
                randomize_delays=self.randomize_delays
            )
        ]
        
        # Execute each sequence
        # If multiple masters, distribute sequences among them
        for seq_idx, sequence in enumerate(sequences):
            # Select master in round-robin fashion
            master_idx = seq_idx % self.M
            master = self.apb_masters[master_idx]
            
            self.log.info(f"Running sequence: {sequence.name} on master {master_idx}")
            
            # Reset sequence iterators
            sequence.reset_iterators()
            
            # Determine number of transactions for this sequence
            num_transactions = len(sequence.pwrite_seq)
            
            for _ in range(num_transactions):
                # Get next cycle from sequence
                cycle = sequence.next()
                
                # Set pprot to indicate master source for verification
                if hasattr(cycle, 'pprot'):
                    cycle.pprot = master_idx
                
                # Send transaction through selected master
                await master.busy_send(cycle)
                
                # Add inter-cycle delay
                delay = sequence.next_delay()
                await self.wait_clocks('pclk', delay)
            
            # Allow time for sequence to complete
            await self.wait_clocks('pclk', 10)
        
        # Wait for all masters' transaction queues to be empty
        for i, master in enumerate(self.apb_masters):
            self.log.info(f"Waiting for transaction queue of master {i} to empty...")
            await self.wait_for_queue_empty(master, timeout=10000)
        
        # Check results
        await self.check_results()

    async def run_test_mixed(self):
        """Run mixed transaction and sequence test"""
        self.log.info("Running APB crossbar mixed test")
        
        # Clear scoreboard before starting test
        self.crossbar_scoreboard.clear_all()
        
        # PART 1: Use raw transactions for specific tests
        self.log.info("Running part 1: Raw transactions to specific addresses")
        
        # Test specific address regions with raw transactions
        address_regions = [0x000, 0x1000, 0x2000, 0x3000]
        
        for i, region in enumerate(address_regions):
            if i >= self.S:
                break
                
            # Select master in round-robin fashion
            master_idx = i % self.M
            master = self.apb_masters[master_idx]
            
            # Generate write transaction
            write_trans = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.strb_width)
            write_trans.paddr = region
            write_trans.pwrite = 1
            write_trans.direction = "WRITE"
            write_trans.pstrb = (1 << self.strb_width) - 1  # All strobes active
            write_trans.pprot = master_idx
            write_cycle = write_trans.next()
            
            # Send write transaction
            self.log.info(f"Sending write from master {master_idx} to addr 0x{region:08X}")
            await master.busy_send(write_cycle)
            
            # Short delay
            await self.wait_clocks('pclk', 3)
            
            # Generate read transaction for same address
            read_trans = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.strb_width)
            read_trans.paddr = region
            read_trans.pwrite = 0
            read_trans.direction = "READ"
            read_trans.pprot = master_idx
            read_cycle = read_trans.next()
            
            # Send read transaction
            self.log.info(f"Sending read from master {master_idx} to addr 0x{region:08X}")
            await master.busy_send(read_cycle)
            
            # Delay between regions
            await self.wait_clocks('pclk', 5)
        
        # PART 2: Use sequences for more comprehensive testing
        self.log.info("Running part 2: Stress sequences on all masters")
        
        # Create stress test sequences for each master
        for master_idx, master in enumerate(self.apb_masters):
            # Create a stress test sequence with slightly different base address per master
            stress_seq = create_apb_sequence(
                name=f"stress_test_master_{master_idx}",
                num_regs=10,
                base_addr=0x1000 * master_idx % (0x1000 * self.S),  # Different base address per master
                pattern="stress",
                data_width=self.DATA_WIDTH,
                randomize_delays=self.randomize_delays
            )
            
            self.log.info(f"Running stress sequence on master {master_idx}")
            
            # Determine number of transactions
            num_transactions = len(stress_seq.pwrite_seq)
            
            for _ in range(num_transactions):
                # Get next cycle from sequence
                cycle = stress_seq.next()
                
                # Set pprot to indicate master source for verification
                if hasattr(cycle, 'pprot'):
                    cycle.pprot = master_idx
                
                # Send transaction through this master
                await master.busy_send(cycle)
                
                # Add inter-cycle delay
                delay = stress_seq.next_delay()
                await self.wait_clocks('pclk', delay)
        
        # Wait for all masters' transaction queues to be empty
        for i, master in enumerate(self.apb_masters):
            self.log.info(f"Waiting for transaction queue of master {i} to empty...")
            await self.wait_for_queue_empty(master, timeout=10000)
        
        # Check results
        await self.check_results()

    async def check_results(self):
        """
        Check scoreboard results and log detailed report
        """
        self.log.info("Checking test results")
        
        # Get scoreboard result
        result = self.crossbar_scoreboard.result()
        
        # Log detailed report
        report = self.crossbar_scoreboard.report()
        for line in report.split('\n'):
            self.log.info(line)
        
        # Assert that test passed
        assert result == 1.0, "Transaction verification failed"

    async def main_loop(self):
        """Main test execution loop"""
        self.log.info(f"Starting APB Crossbar Test with {self.M} masters and {self.S} slaves")
        
        # Create components
        await self.create_components()
        
        # Run configured test cases
        if self.test_basic:
            await self.run_test_basic()
        
        if self.test_sequence:
            await self.run_test_sequence()
        
        if self.test_mixed:
            await self.run_test_mixed()
        
        self.log.info("APB Crossbar Test completed successfully")


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def apb_xbar_test(dut):
    """
    APB Crossbar Test

    This test verifies the behavior of an APB crossbar by:
    1. Sending transactions to the input side(s)
    2. Capturing and validating transactions on the output side(s)
    3. Supporting multiple masters and slaves for flexible testing configurations
    """
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    
    # Create and run test
    tb = APBXbarTest(dut)
    await tb.start_clock('pclk', tb.clock_period, 'ns')
    await tb.reset_dut()
    await tb.main_loop()
    await tb.wait_clocks('pclk', 50)
    tb.log.info("Test completed successfully.")


@pytest.mark.parametrize("model_type, m, s, addr_width, data_width, num_transactions, clock_period", 
    [
        (
            "thin",      # model_type
            3,           # m
            6,           # s
            32,          # addr_width
            32,          # data_width
            30,          # num_transactions
            10,          # clock_period
        ),
        # (
        #     "full",      # model_type
        #     2,           # m
        #     4,           # s
        #     32,          # addr_width
        #     32,          # data_width
        #     30,          # num_transactions
        #     10,          # clock_period
        # )
    ])
def test_apb_xbar_wrap(request, model_type, m, s, addr_width, data_width, num_transactions, clock_period):
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_axi': 'rtl/axi',
            'rtl_int_axi': 'rtl/integ_axi/apb_xbar',
        })

    # Determine DUT name based on model type
    # sourcery skip: no-conditionals-in-tests
    if model_type == "thin":
        dut_name = "apb_xbar_thin_wrap_m10_s10"
    else:  # Full model
        dut_name = "apb_xbar_wrap_m10_s10"

    toplevel = dut_name

    # Select appropriate RTL sources based on model type
    common_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_fixed_priority.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_subinst.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted.sv"),
    ]

    model_specific_sources = []
    if model_type == "thin":
        model_specific_sources = [
            os.path.join(rtl_dict['rtl_axi'], "apb_xbar_thin.sv"),
        ]
    else:  # Full model
        model_specific_sources = [
            os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
            os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_sync.sv"),
            os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
            os.path.join(rtl_dict['rtl_axi'], "apb_master_stub.sv"),
            os.path.join(rtl_dict['rtl_axi'], "apb_slave_stub.sv"),
            os.path.join(rtl_dict['rtl_axi'], "apb_xbar.sv"),
        ]

    # Add the top-level wrapper
    toplevel_source = [
        os.path.join(rtl_dict['rtl_int_axi'], f"{dut_name}.sv")
    ]

    verilog_sources = common_sources + model_specific_sources + toplevel_source

    # Create a human readable test identifier
    m_str = TBBase.format_dec(m, 3)
    s_str = TBBase.format_dec(s, 3)
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    test_name_plus_params = f"test_{dut_name}_m{m_str}_s{s_str}_aw{aw_str}_dw{dw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() 
                        if k in ["m", "s", "addr_width", "data_width"]}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x434749),
        'PARAM_M': str(m),
        'PARAM_S': str(s),
        'PARAM_ADDR_WIDTH': str(addr_width),
        'PARAM_DATA_WIDTH': str(data_width),
        'PARAM_NUM_TRANSACTIONS': str(num_transactions),
        'PARAM_CLOCK_PERIOD': str(clock_period),
        'PARAM_MODEL_TYPE': model_type,
        'PARAM_TEST_BASIC': 'True',
        'PARAM_TEST_SEQUENCE': 'True',
        'PARAM_TEST_MIXED': 'True',
    }


    compile_args = [
            "--trace-fst",
            "--trace-structs",
            "--trace-depth", "99",
    ]

    sim_args = [
            "--trace-fst",  # Tell Verilator to use FST
            "--trace-structs",
            "--trace-depth", "99",
    ]

    plusargs = [
            "+trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure