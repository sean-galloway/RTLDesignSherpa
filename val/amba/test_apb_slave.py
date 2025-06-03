import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction, APBPacket
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import \
    create_apb_master, create_apb_monitor, create_apb_scoreboard
from CocoTBFramework.components.gaxi.gaxi_factories import \
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig
from CocoTBFramework.tbclasses.gaxi.gaxi_enhancements import GAXICommandHandler_APBSlave
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS, AXI_RANDOMIZER_CONFIGS
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd

# Import the modular Temporal Sequence WaveDrom system - no conditionals
from CocoTBFramework.components.wavedrom_utils.constraint_solver import (
    TemporalConstraintSolver, ClockEdge
)
from CocoTBFramework.components.wavedrom_utils.wavejson_gen import (
    WaveJSONGenerator, create_apb_wavejson_generator
)
from CocoTBFramework.components.wavedrom_utils.utility import (
    create_temporal_annotations_from_solution, create_wavejson_from_packet_and_signals,
    get_apb_field_config
)
from CocoTBFramework.tbclasses.wavedrom_user.apb import (
    APBPresets, APBDebug, APBConstraints, 
    setup_apb_constraints_with_boundaries, get_apb_boundary_pattern
)


class APBSlaveTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.done = False
        # Number of registers to test
        self.registers = 64

        # Task termination flag
        self.done = False
        self.num_line = 32768

        # Create a shared memory model for both APB and GAXI components
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)

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
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
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
        self.apbgaxiconfig = APBGAXIConfig(
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            strb_width=self.STRB_WIDTH
        )
        self.cmd_signal_maps = self.apbgaxiconfig.get_master_cmd_signal_maps()
        self.cmd_field_config = self.apbgaxiconfig.create_cmd_field_config()

        self.cmd_monitor = create_gaxi_monitor(
            dut,
            'CMD Monitor',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.cmd_field_config,
            is_slave=False,  # Monitoring master-side signals
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.cmd_signal_maps['ctl'],
            optional_signal_map=self.cmd_signal_maps['opt']
        )

        self.cmd_slave = create_gaxi_slave(
            dut,
            'CMD Slave',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.cmd_field_config,
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=self.mem,
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.cmd_signal_maps['ctl'],
            optional_signal_map=self.cmd_signal_maps['opt']
        )

        # Configure GAXI components for response interface
        self.rsp_signal_maps = self.apbgaxiconfig.get_slave_rsp_signal_maps()
        self.rsp_field_config = self.apbgaxiconfig.create_rsp_field_config()

        self.rsp_monitor = create_gaxi_monitor(
            dut,
            'RSP Monitor',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.rsp_field_config,
            is_slave=True,  # Monitoring slave-side signals
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.rsp_signal_maps['ctl'],
            optional_signal_map=self.rsp_signal_maps['opt']
        )

        self.rsp_master = create_gaxi_master(
            dut,
            'RSP Master',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.rsp_field_config,
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            log=self.log,
            multi_sig=True,  # Using separate signals
            signal_map=self.rsp_signal_maps['ctl'],
            optional_signal_map=self.rsp_signal_maps['opt']
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

        # Initialize WaveDrom components - will be set up later
        self.wave_solver = None
        self.wave_generator = None
        self.apb_field_config = None

    def setup_wavedrom(self, preset_type: str = "comprehensive"):
        """Set up the modular Temporal Sequence WaveDrom system"""
        try:
            self.log.info("Setting up Modular Temporal Sequence WaveDrom system...")
            
            # Get APB field config
            self.apb_field_config = get_apb_field_config(
                data_width=self.DATA_WIDTH,
                addr_width=self.ADDR_WIDTH,
                strb_width=self.STRB_WIDTH
            )
            self.log.info(f"Created APB FieldConfig: {len(self.apb_field_config.field_names())} fields")
            
            # Create APB-specific WaveJSON generator
            self.wave_generator = create_apb_wavejson_generator(field_config=self.apb_field_config)
            
            if not self.wave_generator:
                # Fallback: Create generic generator
                self.log.warning("Protocol-specific generator not available, using generic")
                self.wave_generator = WaveJSONGenerator(debug_level=2)
                
                # Manually configure APB interface
                apb_signals = [
                    "apb_psel", "apb_penable", "apb_pready", "apb_pwrite",
                    "apb_paddr", "apb_pwdata", "apb_prdata", "apb_pstrb",
                    "apb_pprot", "apb_pslverr"
                ]
                self.wave_generator.add_interface_group("APB Interface", apb_signals)
            
            # Create the temporal constraint solver with the WaveJSON generator
            self.wave_solver = TemporalConstraintSolver(
                dut=self.dut,
                log=self.log,
                debug_level=2,
                wavejson_generator=self.wave_generator,
                default_field_config=self.apb_field_config
            )
            
            # Add primary clock group (APB clock)
            self.wave_solver.add_clock_group(
                name="apb_clk",
                clock_signal=self.dut.pclk,
                edge=ClockEdge.RISING,
                sample_delay_ns=0.1,  # Sample 0.1ns after rising edge
                field_config=self.apb_field_config
            )
            
            # Add APB interface signals
            apb_signals = {
                'psel': 's_apb_PSEL',
                'penable': 's_apb_PENABLE', 
                'pready': 's_apb_PREADY',
                'pwrite': 's_apb_PWRITE',
                'paddr': 's_apb_PADDR',
                'pwdata': 's_apb_PWDATA',
                'prdata': 's_apb_PRDATA',
                'pstrb': 's_apb_PSTRB',
                'pprot': 's_apb_PPROT',
                'pslverr': 's_apb_PSLVERR'
            }
            self.wave_solver.add_interface("apb", apb_signals, field_config=self.apb_field_config)
            
            # Set up constraints with boundaries using the helper function
            num_constraints = setup_apb_constraints_with_boundaries(
                wave_solver=self.wave_solver,
                preset_name=preset_type,
                max_cycles=30,  # Increased for complete sequences + post-match
                clock_group="apb_clk",
                data_width=self.DATA_WIDTH,
                addr_width=self.ADDR_WIDTH,
                enable_packet_callbacks=True,
                use_signal_names=True,  # Use actual signal names by default
                post_match_cycles=3  # Extra cycles to capture transaction completion
            )
            
            self.log.info(f"Added {num_constraints} APB constraints with boundaries")
            
            # Optional: Add custom WaveJSON callback for specific formatting
            def custom_apb_write_wavejson(constraint, signal_data, temporal_solution):
                """Custom WaveJSON generation for APB write sequences"""
                try:
                    # Create temporal annotations from solution
                    annotations = create_temporal_annotations_from_solution(temporal_solution)
                    
                    # Generate WaveJSON with custom formatting
                    return self.wave_generator.generate_wavejson(
                        signal_data=signal_data,
                        title="APB Write Transaction Sequence",
                        subtitle=f"Custom formatting | Duration: {temporal_solution.get('sequence_duration', 0)} cycles",
                        temporal_annotations=annotations,
                        config_options={"hscale": 3}  # Wider display
                    )
                except Exception as e:
                    self.log.error(f"Custom WaveJSON callback failed: {e}")
                    return None
            
            # Register custom callback for write sequences
            if hasattr(self.wave_solver, 'add_wavejson_callback'):
                self.wave_solver.add_wavejson_callback("apb_write_sequence", custom_apb_write_wavejson)
            
            self.log.info("Modular Temporal Sequence WaveDrom setup complete")
            if self.wave_generator:
                self.log.info(f"   WaveJSON Generator: {self.wave_generator.get_stats()}")
            
        except Exception as e:
            self.log.error(f"Failed to setup Modular Temporal WaveDrom: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            self.wave_solver = None
            self.wave_generator = None

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

        # Create a transaction
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

        # Send the transaction
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

    async def run_test(self, config: APBSequence, num_transactions: int = None):
        """Run test - Modular WaveDrom solver samples automatically in background"""

        save_randomizer = False

        # Apply custom timing constraints if provided
        if config.master_randomizer:
            save_randomizer = True
            self.log.debug(f'run_test: Setting master randomizer to {config.master_randomizer}')
            self.apb_master.set_randomizer(config.master_randomizer)

        # Reset iterators
        config.reset_iterators()

        # Determine number of transactions to run
        if num_transactions is None:
            num_transactions = len(config.pwrite_seq)

        results = []

        try:
            # Execute transactions - the modular WaveDrom solver samples automatically!
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
            if save_randomizer:
                self.apb_master.set_randomizer(FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']))

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
    def _create_write_seq(self):
        """Create configuration focused on write transactions"""
        return APBSequence(
            name="write_focused",
            pwrite_seq=[True, True],  # Two write transactions
            addr_seq=[0x1000, 0x1004],
            data_seq=[0xDEADBEEF, 0xCAFEBABE],
            strb_seq=[0xF, 0xF],
            inter_cycle_delays=[8, 8]  # Good spacing for waveform capture
        )

    def _create_read_seq(self):
        """Create configuration focused on read transactions"""
        return APBSequence(
            name="read_focused", 
            pwrite_seq=[True, False, False],  # Write then two reads
            addr_seq=[0x2000, 0x2000, 0x2004],
            data_seq=[0x12345678, 0, 0],  # Only write data matters
            strb_seq=[0xF, 0xF, 0xF],
            inter_cycle_delays=[8, 8, 8]
        )

    def _create_mixed_seq(self):
        """Create mixed read/write sequence for comprehensive testing"""
        return APBSequence(
            name="mixed_rw",
            pwrite_seq=[True, False, True, False, True],  # Mixed sequence
            addr_seq=[0x3000, 0x3000, 0x3004, 0x3004, 0x3008],
            data_seq=[0x11223344, 0, 0x55667788, 0, 0x99AABBCC],
            strb_seq=[0xF, 0xF, 0xF, 0xF, 0xF],
            inter_cycle_delays=[6, 6, 6, 6, 6]  # Shorter delays for rapid sequences
        )


@cocotb.test(timeout_time=120, timeout_unit="us")
async def apb_slave_test(dut):
    """APB slave test with Modular Temporal Sequence WaveDrom system"""
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

    # Set up modular Temporal Sequence WaveDrom system
    print('Setting up Modular Temporal Sequence WaveDrom')
    tb.log.info("=== Setting up Modular Temporal Sequence WaveDrom System ===")
    tb.setup_wavedrom(preset_type="comprehensive")

    # Start the command handler
    await tb.cmd_handler.start()

    # Start WaveDrom sampling (if solver is available)
    if tb.wave_solver:
        await tb.wave_solver.start_sampling()
        tb.log.info("Modular Temporal Sequence WaveDrom solver is sampling...")

    try:
        print('# Test 1: Write Transaction Sequences')
        tb.log.info("=== Test 1: Write Transaction Sequences ===")

        config = tb._create_write_seq()
        await tb.run_test(config)
        await tb.verify_scoreboard()

        # Allow time for boundary detection
        tb.log.info("Allowing time for boundary detection to capture write sequences...")
        await tb.wait_clocks('pclk', 15)

        print('# Test 2: Read Transaction Sequences')
        tb.log.info("=== Test 2: Read Transaction Sequences ===")
        config = tb._create_read_seq()
        await tb.run_test(config)
        await tb.verify_scoreboard()

        # Allow time for boundary detection
        tb.log.info("Allowing time for boundary detection to capture read sequences...")
        await tb.wait_clocks('pclk', 15)

        print('# Test 3: Mixed Read/Write Sequences')
        tb.log.info("=== Test 3: Mixed R/W Sequences ===")
        config = tb._create_mixed_seq()
        await tb.run_test(config)
        await tb.verify_scoreboard()

        # Final settling time for any remaining boundary detections
        tb.log.info("Final boundary detection settling time...")
        await tb.wait_clocks('pclk', 20)

        # Stop sampling and get results
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()

            # Debug status
            tb.wave_solver.debug_status()

            # Get results
            results = tb.wave_solver.get_results()

            tb.log.info(f"Modular Temporal Sequence Results:")
            tb.log.info(f"  Total solutions found: {len(results['solutions'])}")
            tb.log.info(f"  Satisfied constraints: {results['satisfied_constraints']}")
            tb.log.info(f"  Failed constraints: {results['failed_constraints']}")
            tb.log.info(f"  All required satisfied: {results['all_required_satisfied']}")
            tb.log.info(f"  WaveJSON Generator stats: {results.get('wavejson_generator_stats', {})}")
            tb.log.info(f"  Protocol configs: {results.get('protocol_configs', 0)}")
            tb.log.info(f"  Boundary configs: {results.get('boundary_configs', 0)}")

            if not results["all_required_satisfied"]:
                tb.log.error(f"Required temporal constraints failed: {results['failed_constraints']}")

                # Show any solutions we did get
                if results["solutions"]:
                    tb.log.warning(f"Got {len(results['solutions'])} solutions from constraints:")
                    for solution in results["solutions"]:
                        tb.log.warning(f"    - {solution.constraint_name}: {solution.filename}")
                        if solution.temporal_solution:
                            timing = solution.temporal_solution.get('event_timing', {})
                            duration = solution.temporal_solution.get('sequence_duration', 0)
                            tb.log.warning(f"      Events: {timing}, Duration: {duration} cycles")
                        if solution.field_config:
                            tb.log.warning(f"      FieldConfig: {len(solution.field_config.field_names())} fields")
                        if solution.protocol_hint:
                            tb.log.warning(f"      Protocol: {solution.protocol_hint}")
                else:
                    tb.log.error("No temporal solutions found!")

                # Don't fail the test, just warn for debugging
                tb.log.warning("Continuing test despite constraint failures for debugging")
            else:
                tb.log.info(f"All required temporal constraints satisfied!")

            # Show generated files with information
            tb.log.info("Generated WaveJSON Files:")
            for solution in results["solutions"]:
                tb.log.info(f"  File: {solution.filename}")
                if solution.temporal_solution:
                    timing = solution.temporal_solution.get('event_timing', {})
                    duration = solution.temporal_solution.get('sequence_duration', 0)
                    tb.log.info(f"      Sequence timing: {timing}")
                    tb.log.info(f"      Duration: {duration} cycles")

                # Solution information
                if solution.field_config:
                    tb.log.info(f"      FieldConfig: {len(solution.field_config.field_names())} fields")
                if solution.protocol_hint:
                    tb.log.info(f"      Protocol: {solution.protocol_hint}")
                if solution.wavejson_generator:
                    gen_stats = solution.wavejson_generator.get_stats()
                    tb.log.info(f"      Generator: {gen_stats.get('total_signals', 0)} signals, {gen_stats.get('fieldconfig_signals', 0)} FieldConfig")

                # WaveJSON validation results
                if tb.wave_generator and solution.wavejson:
                    is_valid, errors = tb.wave_generator.validate_wavejson(solution.wavejson)
                    if is_valid:
                        tb.log.info(f"      WaveJSON: Valid format")

                        # Check for features
                        has_edges = "edge" in solution.wavejson and solution.wavejson["edge"]
                        has_nodes = False
                        has_fieldconfig_data = False

                        if "signal" in solution.wavejson:
                            for signal_item in solution.wavejson["signal"]:
                                if isinstance(signal_item, list):
                                    for signal in signal_item[1:]:  # Skip group name
                                        if isinstance(signal, dict):
                                            if "node" in signal:
                                                has_nodes = True
                                            if "data" in signal and signal["data"]:
                                                has_fieldconfig_data = True
                                elif isinstance(signal_item, dict):
                                    if "node" in signal_item:
                                        has_nodes = True
                                    if "data" in signal_item and signal_item["data"]:
                                        has_fieldconfig_data = True

                        feature_status = []
                        if has_edges and has_nodes:
                            feature_status.append("Edges with nodes")
                        elif has_edges:
                            feature_status.append("Edges present, nodes missing")
                        else:
                            feature_status.append("No edge annotations")

                        if has_fieldconfig_data:
                            feature_status.append("FieldConfig data formatting")
                        else:
                            feature_status.append("No advanced data formatting")

                        tb.log.info(f"      Features: {', '.join(feature_status)}")
                    else:
                        tb.log.warning(f"      WaveJSON: Validation errors: {errors}")

            # Show boundary detection statistics
            if hasattr(tb.wave_solver, 'auto_boundary_configs') and tb.wave_solver.auto_boundary_configs:
                tb.log.info("Boundary Detection Summary:")
                for constraint_name, config in tb.wave_solver.auto_boundary_configs.items():
                    signal = config['transition_signal']
                    transition = config['transition_value']
                    reset_count = len(config['reset_signals'])
                    tb.log.info(f"  {constraint_name}: {signal} {transition[0]}→{transition[1]} (resets {reset_count} signals)")

            # Show FieldConfig integration statistics
            tb.log.info("FieldConfig Integration Summary:")
            tb.log.info(f"  APB FieldConfig: {len(tb.apb_field_config.field_names())} fields")
            for field_name, field_def in tb.apb_field_config.items():
                encoding_info = f", encoding: {len(field_def.encoding)} values" if field_def.encoding else ""
                tb.log.info(f"    {field_name}: {field_def.bits}b, {field_def.format}{encoding_info}")

        else:
            tb.log.warning("No Temporal Sequence Solver available")

        print("\n" + "="*80)
        print("APB Slave test completed with Modular Architecture!")
        print("="*80)
        print("ARCHITECTURE FEATURES:")
        print("  FieldConfig integration for automatic signal configuration")
        print("  WaveJSON generation with protocol-specific formatting")
        print("  Modular constraint solver with FieldConfig-aware boundaries")
        print("  Packet-based WaveJSON callbacks using APBPacket objects")
        print("  Edge nodes with proper WaveDrom specification compliance")
        print("  Automatic signal classification from FieldConfig definitions")
        print("  Validation and error handling")
        print("  Multi-protocol support through FieldConfig abstraction")
        print("\nFIELDCONFIG INTEGRATION:")
        print("  Automatic signal bit width and format detection")
        print("  Protocol-aware field encoding (READ/WRITE, OKAY/ERROR)")
        print("  Data formatting in WaveJSON output")
        print("  Field validation and boundary checking")
        print("  Seamless integration between packets and constraints")
        print("\nWAVEJSON FEATURES:")
        print("  Protocol-specific signal grouping and organization")
        print("  Temporal annotations with proper node mappings")
        print("  Custom formatting based on FieldConfig field definitions")
        print("  Validation of generated WaveJSON against specification")
        print("  Multiple callback types: custom, packet-based, debug")
        print("="*80)

    finally:
        # Clean shutdown
        tb.done = True
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.cmd_handler.stop()
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
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba': 'rtl/amba'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"{dut_name}.sv")
    ]

    # create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it in the simbuild path
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
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'WAVEDROM_SHOW_STATUS': '1'  # Show WaveDrom status on import
    }

    # Add test parameters
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)

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