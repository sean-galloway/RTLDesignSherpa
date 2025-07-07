import os
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

from CocoTBFramework.tbclasses.misc.tbbase import TBBase
from CocoTBFramework.tbclasses.misc.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.misc.arbiter_monitor import RoundRobinArbiterMonitor


class ArbiterRoundRobinConfig:
    """Configuration class for arbiter round robin tests"""
    def __init__(self, name, clients, wait_gnt_ack):
        self.name = name
        self.clients = clients
        self.wait_gnt_ack = wait_gnt_ack


class EnhancedArbiterRoundRobinTB(TBBase):
    """
    Enhanced Testbench for the arbiter_round_robin module with integrated monitor
    Features:
    - All original test functionality
    - Integrated arbiter monitor for detailed analysis
    - Enhanced statistics and pattern verification
    - Better error detection and reporting
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters
        self.CLIENTS = int(dut.CLIENTS)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Initialize state trackers (keep original functionality)
        self.active_reqs = 0
        self.granted_reqs = 0

        # Clock and reset signals
        self.clock = self.dut.i_clk
        self.reset_n = self.dut.i_rst_n

        # Initialize the enhanced arbiter monitor
        self.monitor = RoundRobinArbiterMonitor(
            dut=dut,
            title="RR_Monitor",
            clock=self.dut.i_clk,
            reset_n=self.dut.i_rst_n,
            req_signal=self.dut.i_req,
            gnt_valid_signal=self.dut.o_gnt_valid,
            gnt_signal=self.dut.o_gnt,
            gnt_id_signal=self.dut.o_gnt_id,
            gnt_ack_signal=self.dut.i_gnt_ack,
            block_arb_signal=self.dut.i_block_arb,
            clients=self.CLIENTS,
            log=self.log,
            clock_period_ns=10
        )

        # Add monitor callbacks
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)

        # Log configuration
        self.log.info(f"Enhanced Arbiter Round Robin TB initialized with CLIENTS={self.CLIENTS}")
        self.log.info(f"WAIT_GNT_ACK={self.WAIT_GNT_ACK}, SEED={self.SEED}")

    def _on_monitor_transaction(self, transaction):
        """Callback for monitor transactions - can be used for additional validation"""
        pass  # Could add additional checks here if needed

    def _on_monitor_reset(self):
        """Callback for reset events from monitor"""
        self.log.debug("Monitor detected reset event")

    def clear_interface(self):
        """Clear all interface signals"""
        self.dut.i_block_arb.value = 0
        self.dut.i_req.value = 0
        self.dut.i_gnt_ack.value = 0
        self.log.info('Clearing interface done.')

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.reset_n.value = 0
        self.clear_interface()

        # Hold reset for multiple cycles
        await self.wait_clocks('i_clk', 5)

        # Release reset
        self.reset_n.value = 1

        # Start the monitor after reset is released
        self.monitor.start_monitoring()

        # Wait for stabilization
        await self.wait_clocks('i_clk', 5)

        self.log.debug('Ending reset_dut')

    def random_delay(self, min_clocks=1, max_clocks=5):
        """Generate a random delay between min and max clocks"""
        return random.randint(min_clocks, max_clocks)

    async def generate_requests(self, num_cycles=20):
        """Generate random request patterns for specified number of cycles."""
        self.log.info(f"Generating requests for {num_cycles} cycles")

        for _ in range(num_cycles):
            # Add new random requests, but don't remove existing ones
            new_reqs = 0
            for i in range(self.CLIENTS):
                # Only add a new request if this bit is not already set in active_reqs
                if not (self.active_reqs & (1 << i)) and random.random() < 0.5:
                    new_reqs |= (1 << i)

            # Add new requests to active requests
            self.active_reqs |= new_reqs
            self.dut.i_req.value = self.active_reqs

            if new_reqs:
                req_str = bin(self.active_reqs)[2:].zfill(self.CLIENTS)
                msg = f'    New reqs added: {bin(new_reqs)[2:].zfill(self.CLIENTS)}, Active reqs: {req_str}'
                self.log.debug(msg)

            await self.wait_clocks('i_clk', 1)

    async def check_grants(self):
        """Monitor and verify grant signals (original functionality)"""
        while True:
            await self.wait_clocks('i_clk', 1)

            if self.dut.o_gnt_valid.value == 1:
                time_ns = get_sim_time('ns')
                grant_id = int(self.dut.o_gnt_id.value)
                expected_gnt = (1 << grant_id)

                current_req = int(self.dut.i_req.value)
                msg = f'Current req: 0x{current_req:x} @ {time_ns}ns'
                self.log.debug(msg)

                actual_gnt = int(self.dut.o_gnt.value)

                # Verify grant matches expected pattern
                assert actual_gnt == expected_gnt, \
                    f"Expected grant: 0x{expected_gnt:x}, got: 0x{actual_gnt:x} @ {time_ns}ns"

                # Verify grant corresponds to a request
                assert current_req & actual_gnt, \
                    f"Grant 0x{actual_gnt:x} not in response to request 0x{current_req:x} @ {time_ns}ns"

                # Mark this bit as granted so we can remove it from active requests
                self.granted_reqs |= (1 << grant_id)
                msg = f'Request bit {grant_id} granted @ {time_ns}ns'
                self.log.debug(msg)

                # Clear the granted bit from active requests after acknowledge
                if self.WAIT_GNT_ACK == 0:
                    # If no ACK needed, clear immediately
                    self.active_reqs &= ~(1 << grant_id)
                    self.dut.i_req.value = self.active_reqs
                    msg = f'Cleared bit {grant_id} immediately, new req value: 0x{self.active_reqs:x}'
                    self.log.debug(msg)

    async def handle_grant_ack(self):
        """Handle grant acknowledge signals when WAIT_GNT_ACK is enabled"""
        while True:
            await RisingEdge(self.dut.i_clk)

            if self.WAIT_GNT_ACK == 1 and self.dut.o_gnt_valid.value == 1:
                grant_id = int(self.dut.o_gnt_id.value)
                grant_ack_delay = self.random_delay()

                time_ns = get_sim_time('ns')
                self.log.debug(f"Scheduling grant ack for bit {grant_id} after {grant_ack_delay} cycles @ {time_ns}ns")

                # Wait for random delay before acknowledging
                for _ in range(grant_ack_delay):
                    await self.wait_clocks('i_clk', 1)

                # Set acknowledge signal
                ack_mask = (1 << grant_id)
                self.dut.i_gnt_ack.value = ack_mask

                time_ns = get_sim_time('ns')
                self.log.debug(f"Sending grant ack 0x{ack_mask:x} @ {time_ns}ns")

                # Clear the request only after acknowledge
                self.active_reqs &= ~(1 << grant_id)
                self.dut.i_req.value = self.active_reqs

                # Hold for one cycle then clear ack
                await self.wait_clocks('i_clk', 1)
                self.dut.i_gnt_ack.value = 0

    async def test_grant_signals(self):
        """Test that grant signals work correctly (original test)"""
        self.log.info("Starting grant signal test")

        # Test each client one by one to verify correct o_gnt_id to o_gnt mapping
        for client_id in range(self.CLIENTS):
            # Set a request for just this client
            req_pattern = (1 << client_id)
            self.dut.i_req.value = req_pattern
            self.active_reqs = req_pattern

            self.log.info(f"Testing client {client_id}: req = 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}")

            # Wait for a grant
            max_cycles = 20
            cycle = 0
            grant_received = False

            while cycle < max_cycles and not grant_received:
                await RisingEdge(self.dut.i_clk)
                cycle += 1

                if self.dut.o_gnt_valid.value == 1:
                    grant_id = int(self.dut.o_gnt_id.value)
                    grant_bus = int(self.dut.o_gnt.value)

                    self.log.info(f"Grant received on cycle {cycle}")
                    self.log.info(f"Grant ID: {grant_id}")
                    self.log.info(f"Grant bus: 0b{bin(grant_bus)[2:].zfill(self.CLIENTS)}")

                    # Verify the grant signals
                    assert grant_id == client_id, f"Expected grant ID {client_id}, got {grant_id}"
                    expected_grant = (1 << client_id)
                    assert grant_bus == expected_grant, \
                        f"Expected grant bus 0b{bin(expected_grant)[2:].zfill(self.CLIENTS)}, " \
                        f"got 0b{bin(grant_bus)[2:].zfill(self.CLIENTS)}"

                    # Handle acknowledge if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.i_gnt_ack.value = req_pattern
                        await self.wait_clocks('i_clk', 1)
                        self.dut.i_gnt_ack.value = 0

                    grant_received = True

            assert grant_received, f"No grant received for client {client_id}"

            # Clear the request and wait a cycle before the next client
            self.dut.i_req.value = 0
            self.active_reqs = 0
            await self.wait_clocks('i_clk', 5)

        self.log.info("Grant signal test passed - all clients received grants with correct ID and bus values")

    async def run_test(self, run_cycles=500):
        """Run the main test sequence (original functionality)"""
        self.log.info(f"Starting arbiter test with {self.CLIENTS} clients, WAIT_GNT_ACK={self.WAIT_GNT_ACK}")

        # Start concurrent processes
        cocotb.start_soon(self.generate_requests(20 * self.CLIENTS))
        cocotb.start_soon(self.check_grants())
        cocotb.start_soon(self.handle_grant_ack())

        # Run for the specified number of cycles
        self.log.info(f"Running for {run_cycles} clock cycles")
        for _ in range(run_cycles):
            await RisingEdge(self.dut.i_clk)

        self.log.info("Test completed successfully")

    async def run_enhanced_fairness_test(self):
        """Enhanced fairness test using monitor data"""
        self.log.info("Starting enhanced fairness test with monitor analysis")

        # Track grants per client using monitor
        grant_counts = [0] * self.CLIENTS
        total_cycles = 2000

        # Set all requests active
        all_requests = (1 << self.CLIENTS) - 1
        self.dut.i_req.value = all_requests

        self.log.info(f"Initial request pattern: 0b{bin(all_requests)[2:].zfill(self.CLIENTS)}")

        # Monitor grants
        for cycle in range(total_cycles):
            await RisingEdge(self.dut.i_clk)

            if self.dut.o_gnt_valid.value == 1:
                grant_id = int(self.dut.o_gnt_id.value)
                grant_bit = (1 << grant_id)
                req_value = int(self.dut.i_req.value)

                # Increment count for this client
                grant_counts[grant_id] += 1

                # Log detailed information for debugging
                if cycle < 50 or cycle % 100 == 0:
                    self.log.info(f"Cycle {cycle}: Grant to ID {grant_id}, req 0b{bin(req_value)[2:].zfill(self.CLIENTS)}, "
                                  f"grant bit 0b{bin(grant_bit)[2:].zfill(self.CLIENTS)}, counts {grant_counts}")

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    self.dut.i_gnt_ack.value = grant_bit
                    await self.wait_clocks('i_clk', 1)
                    self.dut.i_gnt_ack.value = 0

                # Clear the granted bit but keep all other bits set
                self.dut.i_req.value = (req_value & ~grant_bit) | (all_requests & ~grant_bit)

                # Wait one cycle
                await self.wait_clocks('i_clk', 1)

                # Set all bits again
                self.dut.i_req.value = all_requests

        # Get statistics from monitor
        monitor_stats = self.monitor.get_stats_summary()
        fairness_index = monitor_stats['fairness_index']

        # Calculate statistics
        total_grants = sum(grant_counts)
        expected_per_client = total_grants / self.CLIENTS if self.CLIENTS > 0 else 0

        self.log.info(f"=== Enhanced Fairness Test Results ===")
        self.log.info(f"Total grants: {total_grants}")
        self.log.info(f"Monitor fairness index: {fairness_index:.3f}")
        self.log.info(f"Monitor total transactions: {monitor_stats['total_transactions']}")

        for i, count in enumerate(grant_counts):
            percentage = (count / total_grants) * 100 if total_grants > 0 else 0
            monitor_count = monitor_stats['client_stats'][i]['grants']
            self.log.info(f"Client {i}: {count} grants ({percentage:.1f}%) - Monitor: {monitor_count} grants")

            # Verify reasonable fairness (within 30% of expected)
            if expected_per_client > 0:
                assert count >= expected_per_client * 0.7, \
                    f"Client {i} received too few grants: {count} vs expected {expected_per_client:.1f}"
                assert count <= expected_per_client * 1.3, \
                    f"Client {i} received too many grants: {count} vs expected {expected_per_client:.1f}"

        # Verify monitor fairness
        assert fairness_index > 0.7, f"Monitor fairness index too low: {fairness_index:.3f}"

        # Analyze round-robin pattern using monitor
        rr_analysis = self.monitor.analyze_round_robin_pattern()
        self.log.info(f"Round-robin pattern analysis: {rr_analysis}")

        self.log.info("Enhanced fairness test passed")

    async def test_block_arb(self):
        """Test the block_arb functionality (original test)"""
        self.log.info("Starting block_arb test")

        # First clear all requests
        self.dut.i_req.value = 0
        self.dut.i_block_arb.value = 0
        await self.wait_clocks('i_clk', 5)

        # Set block_arb before setting any requests
        self.dut.i_block_arb.value = 1
        self.log.info("Asserted block_arb")
        await self.wait_clocks('i_clk', 5)

        # Now set some requests - these should not be granted while block_arb is active
        req_pattern = (1 << self.CLIENTS) - 1  # All bits set
        self.dut.i_req.value = req_pattern
        self.log.info(f"Set request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)} with block_arb asserted")

        # Wait several cycles and verify no grants are issued
        for i in range(20):
            await self.wait_clocks('i_clk', 1)
            assert self.dut.o_gnt_valid.value == 0, \
                f"Grant was issued when block_arb was asserted at cycle {i}, time {get_sim_time('ns')}ns"

        self.log.info("No grants issued while block_arb was asserted - good!")

        # De-assert block_arb and ensure requests are still active
        self.dut.i_block_arb.value = 0
        self.log.info("De-asserted block_arb with active requests")

        # Check that grants resume
        grant_issued = False
        grant_count = 0
        max_cycles = 20

        for i in range(max_cycles):
            await self.wait_clocks('i_clk', 1)

            if self.dut.o_gnt_valid.value == 1:
                grant_id = int(self.dut.o_gnt_id.value)
                grant_bit = (1 << grant_id)

                grant_issued = True
                grant_count += 1

                self.log.info(f"Received grant for client {grant_id} after de-asserting block_arb")

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    self.dut.i_gnt_ack.value = grant_bit
                    await self.wait_clocks('i_clk', 1)
                    self.dut.i_gnt_ack.value = 0

                # Clear the granted bit but keep all other bits set
                current_req = int(self.dut.i_req.value)
                self.dut.i_req.value = current_req & ~grant_bit

                # If we've seen at least 3 grants, we can be confident that block_arb is working correctly
                if grant_count >= 3:
                    break

        assert grant_issued, "No grants issued after de-asserting block_arb with active requests"
        self.log.info(f"Received {grant_count} grants after de-asserting block_arb - block_arb test passed")

    async def run_walking_requests_test(self):
        """Test arbiter with walking adjacent requests (original test)"""
        self.log.info("Starting walking adjacent requests test")

        # Initialize
        self.active_reqs = 0
        self.dut.i_req.value = 0

        # Run through all adjacent pairs
        for i in range(self.CLIENTS - 1):
            # Create request pattern with two adjacent bits
            req_pattern = (1 << i) | (1 << (i + 1))
            self.active_reqs = req_pattern
            self.dut.i_req.value = req_pattern

            self.log.info(f"Testing adjacent requests {i}/{i+1}: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}")

            # Wait for both requests to be granted
            granted_bits = 0
            cycles_waited = 0
            max_cycles = 100

            while granted_bits != req_pattern and cycles_waited < max_cycles:
                await RisingEdge(self.dut.i_clk)
                cycles_waited += 1

                if self.dut.o_gnt_valid.value == 1:
                    grant_id = int(self.dut.o_gnt_id.value)
                    grant_bit = (1 << grant_id)

                    self.log.debug(f"Got grant for bit {grant_id}")
                    granted_bits |= grant_bit

                    # Handle ACK if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.i_gnt_ack.value = grant_bit
                        await self.wait_clocks('i_clk', 1)
                        self.dut.i_gnt_ack.value = 0

                    # Clear the granted bit from the active requests
                    self.active_reqs &= ~grant_bit
                    self.dut.i_req.value = self.active_reqs

            assert granted_bits == req_pattern, \
                f"Not all bits in request pattern 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)} were granted"

            # Wait a few cycles before moving to next pattern
            await self.wait_clocks('i_clk', 5)

        self.log.info("Walking adjacent requests test passed")


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def arbiter_round_robin_enhanced_test(dut):
    """Enhanced test for the round-robin arbiter with monitor integration"""
    tb = EnhancedArbiterRoundRobinTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Enhanced round robin test starting with seed {seed}')

    # Start the clock
    await tb.start_clock('i_clk', 10, 'ns')

    # Reset the DUT (this also starts the monitor)
    await tb.reset_dut()

    try:
        # Run the original grant signal test first
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting grant signal test @ {time_ns}ns ===")
        await tb.test_grant_signals()

        # Run the main test with monitoring
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting main arbitration test @ {time_ns}ns ===")
        await tb.run_test(500)

        # Run the walking requests test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting walking requests test @ {time_ns}ns ===")
        await tb.run_walking_requests_test()

        # Test block_arb functionality
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting block_arb test @ {time_ns}ns ===")
        await tb.test_block_arb()

        # Run enhanced fairness test with monitor analysis
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting enhanced fairness test @ {time_ns}ns ===")
        await tb.run_enhanced_fairness_test()

        # Print final monitor statistics
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Final Monitor Statistics @ {time_ns}ns ===")
        final_stats = tb.monitor.get_stats_summary()
        tb.log.info(f"Total transactions: {final_stats['total_transactions']}")
        tb.log.info(f"Total grants: {final_stats['total_grants']}")
        tb.log.info(f"Average wait time: {final_stats['avg_wait_time']:.2f}ns")
        tb.log.info(f"Fairness index: {final_stats['fairness_index']:.3f}")

        # Analyze round-robin compliance
        rr_analysis = tb.monitor.analyze_round_robin_pattern()
        tb.log.info(f"Round-robin compliance: {rr_analysis}")

        tb.log.info("All enhanced tests completed successfully")

    except AssertionError as e:
        tb.log.error(f"Enhanced test failed: {str(e)}")
        raise
    finally:
        # Wait for any pending tasks
        await tb.wait_clocks('i_clk', 10)


@pytest.mark.parametrize("clients, wait_ack", [
    (6, 0),  # No wait for ack
    (4, 1)   # Wait for ack
])
def test_arbiter_round_robin_enhanced(request, clients, wait_ack):
    """Run the enhanced round robin test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "arbiter_round_robin"
    toplevel = dut_name

    # Verilog sources for ROUND ROBIN arbiter
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "find_first_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "find_last_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "leading_one_trailing_one.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    w_str = TBBase.format_dec(wait_ack, 1)
    test_name_plus_params = f"test_{dut_name}_enhanced_c{c_str}_w{w_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters for ROUND ROBIN
    parameters = {'CLIENTS': clients, 'WAIT_GNT_ACK': wait_ack}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
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
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
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
        print(f"Enhanced round robin test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
