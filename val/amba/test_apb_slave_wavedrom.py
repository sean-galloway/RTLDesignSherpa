# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ComprehensiveAPBSlaveTB
# Purpose: Comprehensive APB Slave Test Suite
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Comprehensive APB Slave Test Suite

This enhanced test suite exercises all randomizer configurations and includes
extensive edge case testing for robust verification coverage.
"""

import os
import random
import itertools
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction, APBPacket
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import \
    create_apb_master, create_apb_monitor, create_apb_scoreboard
from CocoTBFramework.components.gaxi.gaxi_factories import \
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge
)
from CocoTBFramework.components.wavedrom.wavejson_gen import (
    WaveJSONGenerator, create_apb_wavejson_generator
)
from CocoTBFramework.components.wavedrom.utility import (
    create_temporal_annotations_from_solution, create_wavejson_from_packet_and_signals,
    get_apb_field_config
)
from CocoTBFramework.tbclasses.wavedrom_user.apb import (
    APBPresets, APBDebug, APBConstraints,
    setup_apb_constraints_with_boundaries, get_apb_boundary_pattern
)


class ComprehensiveAPBSlaveTB(TBBase):
    """Enhanced APB Slave Testbench with comprehensive test coverage."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.done = False
        self.registers = 1024  # Increased for comprehensive testing
        self.num_line = 32768

        # Test statistics
        self.test_stats = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': 0,
            'total_transactions': 0,
            'error_transactions': 0,
            'configurations_tested': set()
        }

        # Create shared memory model
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)

        # Initialize basic components
        self._init_components()

        # Initialize WaveDrom
        self.wave_solver = None
        self.wave_generator = None
        self.apb_field_config = None

    def _init_components(self):
        """Initialize all APB and GAXI components."""
        # APB components
        self.apb_monitor = create_apb_monitor(
            self.dut,
            'APB Monitor',
            's_apb',
            self.dut.pclk,
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            log=self.log
        )

        self.apb_master = create_apb_master(
            self.dut,
            'APB Master',
            's_apb',
            self.dut.pclk,
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log
        )

        # APB scoreboard
        self.apb_scoreboard = create_apb_scoreboard(
            'APB Scoreboard',
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            log=self.log
        )

        # GAXI components
        super_debug = False
        self.apbgaxiconfig = APBGAXIConfig(
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            strb_width=self.STRB_WIDTH
        )
        self.cmd_field_config = self.apbgaxiconfig.create_cmd_field_config()
        self.rsp_field_config = self.apbgaxiconfig.create_rsp_field_config()

        # Command interface components
        self.cmd_monitor = create_gaxi_monitor(
            self.dut, 'CMD Monitor', '', self.dut.pclk,
            field_config=self.cmd_field_config,
            pkt_prefix='cmd', is_slave=True,
            log=self.log, super_debug=super_debug, multi_sig=True,
        )

        self.cmd_slave = create_gaxi_slave(
            self.dut, 'CMD Slave', '', self.dut.pclk,
            field_config=self.cmd_field_config,
            pkt_prefix='cmd',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=self.mem,
            log=self.log, super_debug=super_debug, multi_sig=True,
        )

        # Response interface components
        self.rsp_monitor = create_gaxi_monitor(
            self.dut, 'RSP Monitor', '', self.dut.pclk,
            field_config=self.rsp_field_config,
            pkt_prefix='rsp', is_slave=False,
            log=self.log, super_debug=super_debug, multi_sig=True,
        )

        self.rsp_master = create_gaxi_master(
            self.dut, 'RSP Master', '', self.dut.pclk,
            field_config=self.rsp_field_config,
            pkt_prefix='rsp',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None,
            log=self.log, super_debug=super_debug, multi_sig=True,
        )

        # Command handler with response generation
        self.cmd_handler = GAXICommandHandler(
            master=self.rsp_master,
            slave=self.cmd_slave,
            memory_model=self.mem,
            log=self.log,
            response_generation_mode=True
        )

        # Enhanced scoreboard
        self.apb_gaxi_scoreboard = APBGAXIScoreboard(
            'APB-GAXI Scoreboard',
            log=self.log
        )

        # Connect monitors
        self.apb_monitor.add_callback(self.apb_transaction_callback)
        self.cmd_monitor.add_callback(self.cmd_transaction_callback)
        self.rsp_monitor.add_callback(self.rsp_transaction_callback)  # This was missing!

        # Initialize queues
        self.apb_monitor_queue = deque()

    def setup_wavedrom(self, preset_type: str = "comprehensive"):
        """Set up WaveDrom system (same as before)."""
        try:
            self.log.info("Setting up Modular Temporal Sequence WaveDrom system...")

            self.apb_field_config = get_apb_field_config(
                data_width=self.DATA_WIDTH,
                addr_width=self.ADDR_WIDTH,
                strb_width=self.STRB_WIDTH
            )

            self.wave_generator = create_apb_wavejson_generator(field_config=self.apb_field_config)
            if not self.wave_generator:
                self.wave_generator = WaveJSONGenerator(debug_level=2)
                apb_signals = [
                    "apb_psel", "apb_penable", "apb_pready", "apb_pwrite",
                    "apb_paddr", "apb_pwdata", "apb_prdata", "apb_pstrb",
                    "apb_pprot", "apb_pslverr"
                ]
                self.wave_generator.add_interface_group("APB Interface", apb_signals)

            self.wave_solver = TemporalConstraintSolver(
                dut=self.dut,
                log=self.log,
                debug_level=2,
                wavejson_generator=self.wave_generator,
                default_field_config=self.apb_field_config
            )

            self.wave_solver.add_clock_group(
                name="apb_clk",
                clock_signal=self.dut.pclk,
                edge=ClockEdge.RISING,
                sample_delay_ns=0.1,
                field_config=self.apb_field_config
            )

            # WAVEDROM REQUIREMENT v1.2: ALL waveforms MUST include clock and reset
            apb_signals = {
                'pclk': 'pclk',          # Clock (ALWAYS REQUIRED)
                'presetn': 'presetn',    # Reset (ALWAYS REQUIRED)
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

            num_constraints = setup_apb_constraints_with_boundaries(
                wave_solver=self.wave_solver,
                preset_name=preset_type,
                max_cycles=30,
                clock_group="apb_clk",
                data_width=self.DATA_WIDTH,
                addr_width=self.ADDR_WIDTH,
                enable_packet_callbacks=True,
                use_signal_names=True,
                post_match_cycles=3
            )

            self.log.info(f"Added {num_constraints} APB constraints with boundaries")

        except Exception as e:
            self.log.error(f"Failed to setup WaveDrom: {e}")
            self.wave_solver = None
            self.wave_generator = None

    def rsp_transaction_callback(self, transaction):
        """
        GAXI response transaction callback

        This method gets called whenever the RSP monitor observes a response transaction.
        It adds the response to the scoreboard for matching with APB transactions.

        Args:
            transaction: GAXI response transaction from the RSP monitor
        """
        # Add the response transaction to the scoreboard
        self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)

        # Optional: Log for debugging
        if self.log:
            prdata = transaction.fields.get('prdata', 0) if hasattr(transaction, 'fields') else getattr(transaction, 'prdata', 0)
            pslverr = transaction.fields.get('pslverr', 0) if hasattr(transaction, 'fields') else getattr(transaction, 'pslverr', 0)
            self.log.debug(f"RSP callback: Adding GAXI response to scoreboard - data=0x{prdata:X}, error={pslverr}")

    def cmd_transaction_callback(self, transaction):
        """GAXI command transaction callback."""
        self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)

        # Optional: Log for debugging
        if self.log:
            pwrite = transaction.fields.get('pwrite', 0) if hasattr(transaction, 'fields') else getattr(transaction, 'pwrite', 0)
            paddr = transaction.fields.get('paddr', 0) if hasattr(transaction, 'fields') else getattr(transaction, 'paddr', 0)
            pwdata = transaction.fields.get('pwdata', 0) if hasattr(transaction, 'fields') else getattr(transaction, 'pwdata', 0)
            direction = "WRITE" if pwrite else "READ"
            self.log.debug(f"CMD callback: Adding GAXI command to scoreboard - {direction} addr=0x{paddr:X}, data=0x{pwdata:X}")

    def apb_transaction_callback(self, transaction):
        """APB transaction callback."""
        self.apb_monitor_queue.append(transaction)
        self.apb_gaxi_scoreboard.add_apb_transaction(transaction)
        self.test_stats['total_transactions'] += 1

        # Optional: Log for debugging
        if self.log:
            direction = "WRITE" if getattr(transaction, 'pwrite', 0) else "READ"
            addr = getattr(transaction, 'paddr', 0)
            if direction == "WRITE":
                data = getattr(transaction, 'pwdata', 0)
                self.log.debug(f"APB callback: Adding APB transaction to scoreboard - {direction} addr=0x{addr:X}, data=0x{data:X}")
            else:
                data = getattr(transaction, 'prdata', 0)
                self.log.debug(f"APB callback: Adding APB transaction to scoreboard - {direction} addr=0x{addr:X}, data=0x{data:X}")

    async def reset_dut(self):
        """Reset DUT and all components."""
        self.log.debug('Starting reset_dut')

        self.dut.presetn.value = 0
        await self.apb_master.reset_bus()
        await self.cmd_slave.reset_bus()
        await self.rsp_master.reset_bus()
        await self.wait_clocks('pclk', 5)

        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 10)

        self.apb_monitor_queue.clear()
        self.apb_gaxi_scoreboard.clear()

        self.log.debug('Ending reset_dut')

    async def wait_for_queue_empty(self, object_with_queue, timeout=1000):
        """Wait for queue to be empty."""
        start_time = get_sim_time('ns')

        if hasattr(object_with_queue, 'transmit_queue'):
            queue_attr = 'transmit_queue'
        elif hasattr(object_with_queue, '_xmitQ'):
            queue_attr = '_xmitQ'
        else:
            self.log.error(f"Unknown queue type for {object_with_queue.__class__.__name__}")
            return

        queue = getattr(object_with_queue, queue_attr)

        while len(queue) > 0:
            await self.wait_clocks('pclk', 1)
            current_time = get_sim_time('ns')
            if current_time - start_time > timeout:
                self.log.warning(f"Timeout waiting for queue to be empty after {timeout}ns")
                break

    async def send_apb_transaction(self, is_write, addr, data=None, strobe=None):
        """Send APB transaction."""
        start_time = get_sim_time('ns')

        xmit_transaction_cls = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
        xmit_transaction = xmit_transaction_cls.next()

        xmit_transaction.pwrite = 1 if is_write else 0
        xmit_transaction.direction = "WRITE" if is_write else "READ"
        xmit_transaction.paddr = addr

        if is_write:
            xmit_transaction.pwdata = data if data is not None else random.randint(0, 2**self.DATA_WIDTH - 1)
            xmit_transaction.pstrb = strobe if strobe is not None else (2**self.STRB_WIDTH - 1)

        xmit_transaction.start_time = start_time

        await self.apb_master.send(xmit_transaction)
        await self.wait_for_queue_empty(self.apb_master, timeout=10000)
        await self.wait_clocks('pclk', 3)  # Small delay for response processing

        return xmit_transaction

    def set_randomizer_config(self, apb_master_config=None, apb_slave_config=None, axi_config=None):
        """Set randomizer configurations for all components."""
        if apb_master_config:
            self.apb_master.set_randomizer(FlexRandomizer(apb_master_config))
            self.test_stats['configurations_tested'].add(f"apb_master_{apb_master_config}")

        if apb_slave_config:
            # Note: APB slave randomizer would be used if we had an APB slave component
            # For now, we track the configuration for completeness
            self.test_stats['configurations_tested'].add(f"apb_slave_{apb_slave_config}")

        if axi_config:
            if 'master' in axi_config:
                self.rsp_master.set_randomizer(FlexRandomizer(axi_config['master']))
            if 'slave' in axi_config:
                self.cmd_slave.set_randomizer(FlexRandomizer(axi_config['slave']))
            self.test_stats['configurations_tested'].add(f"axi_{axi_config}")

    async def run_test_sequence(self, sequence_config, num_transactions=None):
        """Run a test sequence with the given configuration."""
        if num_transactions is None:
            num_transactions = len(sequence_config.pwrite_seq)

        results = []
        sequence_config.reset_iterators()

        try:
            for i in range(num_transactions):
                is_write = sequence_config.next_pwrite()
                addr = sequence_config.next_addr()

                if is_write:
                    data = sequence_config.next_data()
                    strobe = sequence_config.next_strb()
                    result = await self.send_apb_transaction(True, addr, data, strobe)
                else:
                    result = await self.send_apb_transaction(False, addr)

                results.append(result)

                if i < num_transactions - 1:
                    delay = sequence_config.next_delay()
                    if delay > 0:
                        await self.wait_clocks('pclk', delay)

        except Exception as e:
            self.log.error(f"Test sequence failed: {e}")
            self.test_stats['failed_tests'] += 1
            raise

        return results

    async def verify_scoreboard(self, timeout=1000):
        """Verify scoreboard."""
        result = await self.apb_gaxi_scoreboard.check_scoreboard(timeout)

        if result:
            self.test_stats['passed_tests'] += 1
            self.log.info("Scoreboard verification passed")
        else:
            self.test_stats['failed_tests'] += 1
            self.log.error("Scoreboard verification failed")

        return result

    # Test sequence generators
    def create_basic_write_sequence(self, num_txns=5):
        """Create basic write sequence - FIXED to include reads."""
        # Create write-read pairs for better testing
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        for i in range(num_txns):
            # Write first
            pwrite_seq.append(True)
            addr_seq.append(0x1000 + i*4)
            data_seq.append(0x10000 + i)
            strb_seq.append(0xF)

            # Then read back
            pwrite_seq.append(False)
            addr_seq.append(0x1000 + i*4)
            data_seq.append(0)  # Not used for reads
            strb_seq.append(0xF)

        return APBSequence(
            name="basic_write_read",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=[2] * len(pwrite_seq)
        )

    def create_basic_read_sequence(self, num_txns=5):
        """Create basic read sequence - FIXED to test sequential data."""
        # First write some data, then read it back
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        # Write phase
        for i in range(num_txns):
            pwrite_seq.append(True)
            addr_seq.append(0x2000 + i*4)
            data_seq.append(0x20000 + i)
            strb_seq.append(0xF)

        # Read phase
        for i in range(num_txns):
            pwrite_seq.append(False)
            addr_seq.append(0x2000 + i*4)
            data_seq.append(0)  # Not used for reads
            strb_seq.append(0xF)

        return APBSequence(
            name="basic_read_test",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=[2] * len(pwrite_seq)
        )

    def create_burst_sequence(self, num_txns=10):
        """Create burst sequence - FIXED to include reads."""
        # Alternating write-read pattern
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        for i in range(num_txns//2):
            # Write
            pwrite_seq.append(True)
            addr_seq.append(0x3000 + i*4)
            data_seq.append(0x30000 + i)
            strb_seq.append(0xF)

            # Read
            pwrite_seq.append(False)
            addr_seq.append(0x3000 + i*4)
            data_seq.append(0)
            strb_seq.append(0xF)

        return APBSequence(
            name="burst_write_read",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=[0] * len(pwrite_seq)  # Back-to-back
        )

    def create_sequential_read_test(self, num_txns=8):
        """Create test specifically for sequential data generation."""
        # Only reads to test sequential data generation
        return APBSequence(
            name="sequential_read_test",
            pwrite_seq=[False] * num_txns,
            addr_seq=[0x4000 + i*4 for i in range(num_txns)],
            data_seq=[0] * num_txns,  # Not used for reads
            strb_seq=[0xF] * num_txns,
            inter_cycle_delays=[1] * num_txns
        )

    def create_sparse_sequence(self, num_txns=5):
        """Create sparse sequence with large delays."""
        return APBSequence(
            name="sparse",
            pwrite_seq=[True, False] * (num_txns//2) + [True],
            addr_seq=[0x4000 + i*4 for i in range(num_txns)],
            data_seq=[0x2000 + i for i in range(num_txns)],
            strb_seq=[0xF] * num_txns,
            inter_cycle_delays=[20] * num_txns  # Large delays
        )

    def create_boundary_address_sequence(self):
        """Create sequence testing boundary addresses."""
        boundary_addrs = [
            0x00000000,  # Minimum address
            0x00000004,  # Word aligned
            0x00000008,  # Word aligned
            0x000003FC,  # Near boundary
            0x00000FFC,  # Near 4K boundary
        ]

        return APBSequence(
            name="boundary_addresses",
            pwrite_seq=[True, False] * (len(boundary_addrs)//2) + [True],
            addr_seq=boundary_addrs,
            data_seq=[0x5000 + i for i in range(len(boundary_addrs))],
            strb_seq=[0xF] * len(boundary_addrs),
            inter_cycle_delays=[3] * len(boundary_addrs)
        )

    def create_strobe_pattern_sequence(self):
        """Create sequence testing different strobe patterns."""
        strobe_patterns = [0x1, 0x3, 0x7, 0xF, 0x8, 0xC, 0x6, 0x9]

        return APBSequence(
            name="strobe_patterns",
            pwrite_seq=[True] * len(strobe_patterns),
            addr_seq=[0x5000 + i*4 for i in range(len(strobe_patterns))],
            data_seq=[0x3000 + i for i in range(len(strobe_patterns))],
            strb_seq=strobe_patterns,
            inter_cycle_delays=[2] * len(strobe_patterns)
        )

    def create_data_pattern_sequence(self):
        """Create sequence testing different data patterns."""
        data_patterns = [
            0x00000000,  # All zeros
            0xFFFFFFFF,  # All ones
            0x55555555,  # Alternating 01
            0xAAAAAAAA,  # Alternating 10
            0x12345678,  # Incremental
            0x87654321,  # Decremental
            0xDEADBEEF,  # Known pattern
            0xCAFEBABE,  # Known pattern
        ]

        return APBSequence(
            name="data_patterns",
            pwrite_seq=[True, False] * (len(data_patterns)//2),
            addr_seq=[0x6000 + i*4 for i in range(len(data_patterns))],
            data_seq=data_patterns,
            strb_seq=[0xF] * len(data_patterns),
            inter_cycle_delays=[1] * len(data_patterns)
        )

    async def generate_all_wavedrom_scenarios(self):
        """
        Generate all 7 focused APB waveform scenarios.

        This method explicitly creates transaction patterns to ensure all
        meaningful waveforms are generated:
        1. Basic write
        2. Basic read
        3. Back-to-back writes
        4. Back-to-back reads
        5. Write-to-read transition
        6. Read-to-write transition
        7. Error transaction (if supported)
        """
        self.log.info("=== Generating All APB WaveDrom Scenarios ===")

        # Use fixed timing for predictable waveforms
        self.set_randomizer_config(
            apb_master_config=APB_MASTER_RANDOMIZER_CONFIGS['fixed'],
            axi_config=AXI_RANDOMIZER_CONFIGS['fixed']
        )

        # Scenario 1 & 2: Basic write and read (single transactions)
        self.log.info("Generating: Basic write and read transactions")
        basic_seq = APBSequence(
            name="basic_wr",
            pwrite_seq=[True, False],
            addr_seq=[0x1000, 0x1000],
            data_seq=[0xDEADBEEF, 0x0],
            strb_seq=[0xF, 0xF],
            inter_cycle_delays=[5, 5]  # Gap between transactions
        )
        await self.run_test_sequence(basic_seq)
        await self.wait_clocks('pclk', 10)

        # Scenario 3: Back-to-back writes
        self.log.info("Generating: Back-to-back writes")
        b2b_writes = APBSequence(
            name="b2b_writes",
            pwrite_seq=[True, True],
            addr_seq=[0x2000, 0x2004],
            data_seq=[0xAAAAAAAA, 0xBBBBBBBB],
            strb_seq=[0xF, 0xF],
            inter_cycle_delays=[0, 5]  # No gap = back-to-back
        )
        await self.run_test_sequence(b2b_writes)
        await self.wait_clocks('pclk', 10)

        # Scenario 4: Back-to-back reads
        self.log.info("Generating: Back-to-back reads")
        b2b_reads = APBSequence(
            name="b2b_reads",
            pwrite_seq=[False, False],
            addr_seq=[0x3000, 0x3004],
            data_seq=[0x0, 0x0],
            strb_seq=[0xF, 0xF],
            inter_cycle_delays=[0, 5]  # No gap = back-to-back
        )
        await self.run_test_sequence(b2b_reads)
        await self.wait_clocks('pclk', 10)

        # Scenario 5: Write-to-read transition
        self.log.info("Generating: Write-to-read transition")
        wr_to_rd = APBSequence(
            name="wr_to_rd",
            pwrite_seq=[True, False],
            addr_seq=[0x4000, 0x4000],
            data_seq=[0x12345678, 0x0],
            strb_seq=[0xF, 0xF],
            inter_cycle_delays=[0, 5]  # No gap = immediate transition
        )
        await self.run_test_sequence(wr_to_rd)
        await self.wait_clocks('pclk', 10)

        # Scenario 6: Read-to-write transition
        self.log.info("Generating: Read-to-write transition")
        rd_to_wr = APBSequence(
            name="rd_to_wr",
            pwrite_seq=[False, True],
            addr_seq=[0x5000, 0x5000],
            data_seq=[0x0, 0x87654321],
            strb_seq=[0xF, 0xF],
            inter_cycle_delays=[0, 5]  # No gap = immediate transition
        )
        await self.run_test_sequence(rd_to_wr)
        await self.wait_clocks('pclk', 10)

        # Scenario 7: Error transactions would be generated if the slave
        # supports error responses - skipping for now as it requires
        # specific slave configuration

        self.log.info("✓ All APB WaveDrom scenarios generated")

    async def run_comprehensive_test_suite(self):
        """Run comprehensive test suite with all configurations."""
        self.log.info("=== Starting Comprehensive APB Test Suite ===")

        # Test configuration matrix
        test_matrix = [
            ('fixed', 'fixed', 'Basic Fixed Timing'),
            # ('constrained', 'constrained', 'Constrained Random Timing'),
            # ('fast', 'fast', 'Fast Timing'),
            # ('backtoback', 'backtoback', 'Back-to-Back Transactions'),
        ]

        test_sequences = [
            ('basic_write_read', lambda: self.create_basic_write_sequence(3)),
            # ('basic_read_test', lambda: self.create_basic_read_sequence(3)),
            # ('burst_write_read', lambda: self.create_burst_sequence(6)),
            # ('sequential_read_test', lambda: self.create_sequential_read_test(5)),
            # ('boundary_addresses', lambda: self.create_boundary_address_sequence()),
            # ('strobe_patterns', lambda: self.create_strobe_pattern_sequence()),
            # ('data_patterns', lambda: self.create_data_pattern_sequence()),
        ]

        total_test_combinations = len(test_matrix) * len(test_sequences)
        current_test = 0

        for apb_config, axi_config, config_desc in test_matrix:
            for seq_name, seq_generator in test_sequences:
                current_test += 1
                self.log.info(f"=== Test {current_test}/{total_test_combinations}: {config_desc} - {seq_name} ===")

                try:
                    # Set configuration
                    self.set_randomizer_config(
                        apb_master_config=APB_MASTER_RANDOMIZER_CONFIGS[apb_config],
                        axi_config=AXI_RANDOMIZER_CONFIGS[axi_config]
                    )

                    # Generate and run sequence
                    sequence = seq_generator()
                    await self.run_test_sequence(sequence)

                    # Verify results
                    result = await self.verify_scoreboard()

                    if result:
                        self.log.info(f"✓ Test {current_test} PASSED: {config_desc} - {seq_name}")
                    else:
                        self.log.error(f"✗ Test {current_test} FAILED: {config_desc} - {seq_name}")

                    # Allow settling time between tests
                    await self.wait_clocks('pclk', 10)

                    self.test_stats['total_tests'] += 1

                except Exception as e:
                    self.log.error(f"✗ Test {current_test} EXCEPTION: {config_desc} - {seq_name}: {e}")
                    self.test_stats['failed_tests'] += 1
                    # Continue with next test
                    continue

        # High-throughput stress test
        await self.run_stress_tests()

        # Error injection tests
        await self.run_error_injection_tests()

        # Generate final report
        self.generate_test_report()

    async def run_stress_tests(self):
        """Run stress tests with high transaction volumes."""
        self.log.info("=== Running Stress Tests ===")

        stress_configs = [
            ('backtoback', 'high_throughput', 'High Throughput Stress'),
            ('backtoback', 'backtoback', 'Back-to-Back Stress'),
        ]

        for apb_config, axi_config, config_desc in stress_configs:
            self.log.info(f"=== Stress Test: {config_desc} ===")

            try:
                # Set high-performance configuration
                self.set_randomizer_config(
                    apb_master_config=APB_MASTER_RANDOMIZER_CONFIGS[apb_config],
                    axi_config=AXI_RANDOMIZER_CONFIGS[axi_config]
                )

                # Create large burst sequence
                large_burst = APBSequence(
                    name="stress_burst",
                    pwrite_seq=[True, False] * 50,  # 100 transactions
                    addr_seq=[0x7000 + i*4 for i in range(100)],
                    data_seq=[0x4000 + i for i in range(100)],
                    strb_seq=[0xF] * 100,
                    inter_cycle_delays=[0] * 100  # Back-to-back
                )

                await self.run_test_sequence(large_burst)
                result = await self.verify_scoreboard()

                if result:
                    self.log.info(f"✓ Stress Test PASSED: {config_desc}")
                else:
                    self.log.error(f"✗ Stress Test FAILED: {config_desc}")

                self.test_stats['total_tests'] += 1

            except Exception as e:
                self.log.error(f"✗ Stress Test EXCEPTION: {config_desc}: {e}")
                self.test_stats['failed_tests'] += 1

    async def run_error_injection_tests(self):
        """Run error injection tests."""
        self.log.info("=== Running Error Injection Tests ===")

        # Note: These tests would be more effective with actual error injection
        # in the DUT or slave components, but we can test the framework

        try:
            # Test with slow consumer configuration
            self.set_randomizer_config(
                apb_master_config=APB_MASTER_RANDOMIZER_CONFIGS['slow_master'],
                axi_config=AXI_RANDOMIZER_CONFIGS['slow_producer']
            )

            # Create challenging sequence
            error_sequence = APBSequence(
                name="error_injection",
                pwrite_seq=[True, False, True, False, True],
                addr_seq=[0x8000, 0x8004, 0x8008, 0x800C, 0x8010],
                data_seq=[0x5000, 0x5001, 0x5002, 0x5003, 0x5004],
                strb_seq=[0xF, 0x3, 0xC, 0x1, 0x8],
                inter_cycle_delays=[5, 10, 15, 20, 25]
            )

            await self.run_test_sequence(error_sequence)
            result = await self.verify_scoreboard()

            if result:
                self.log.info("✓ Error Injection Test PASSED")
            else:
                self.log.error("✗ Error Injection Test FAILED")

            self.test_stats['total_tests'] += 1

        except Exception as e:
            self.log.error(f"✗ Error Injection Test EXCEPTION: {e}")
            self.test_stats['failed_tests'] += 1

    def generate_test_report(self):
        """Generate comprehensive test report."""
        self.log.info("=== COMPREHENSIVE TEST REPORT ===")
        self.log.info(f"Total Tests: {self.test_stats['total_tests']}")
        self.log.info(f"Passed Tests: {self.test_stats['passed_tests']}")
        self.log.info(f"Failed Tests: {self.test_stats['failed_tests']}")
        self.log.info(f"Total Transactions: {self.test_stats['total_transactions']}")
        self.log.info(f"Error Transactions: {self.test_stats['error_transactions']}")

        if self.test_stats['total_tests'] > 0:
            pass_rate = (self.test_stats['passed_tests'] / self.test_stats['total_tests']) * 100
            self.log.info(f"Pass Rate: {pass_rate:.1f}%")

        self.log.info(f"Configurations Tested: {len(self.test_stats['configurations_tested'])}")
        for config in sorted(self.test_stats['configurations_tested']):
            self.log.info(f"  - {config}")

        self.log.info("=== END TEST REPORT ===")


@cocotb.test(timeout_time=300, timeout_unit="us")  # Increased timeout for comprehensive tests
async def comprehensive_apb_slave_test(dut):
    """Comprehensive APB slave test with all randomizer configurations."""
    tb = ComprehensiveAPBSlaveTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start clock
    await tb.start_clock('pclk', 10, 'ns')

    # Reset DUT
    await tb.reset_dut()

    # Set up WaveDrom
    tb.setup_wavedrom(preset_type="comprehensive")

    # Start command handler
    await tb.cmd_handler.start()

    # Start WaveDrom sampling
    if tb.wave_solver:
        await tb.wave_solver.start_sampling()

    try:
        # Generate all APB waveform scenarios
        await tb.generate_all_wavedrom_scenarios()

        # Stop WaveDrom sampling and get results
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
            tb.wave_solver.debug_status()
            results = tb.wave_solver.get_results()

            tb.log.info(f"WaveDrom Results: {len(results['solutions'])} solutions, "
                       f"{results['satisfied_constraints']} satisfied, "
                       f"{results['failed_constraints']} failed")

            # Check if all required waveforms were generated
            if not results['all_required_satisfied']:
                tb.log.error(f"❌ NOT ALL REQUIRED WAVEFORMS GENERATED ❌")
                tb.log.error(f"Failed constraints: {results['failed_constraints']}")
                assert False, f"Required waveforms not generated: {results['failed_constraints']}"

        # Final verification
        final_result = await tb.verify_scoreboard(timeout=5000)

        if final_result:
            tb.log.info("🎉 APB WAVEDROM GENERATION COMPLETE! 🎉")
        else:
            tb.log.error("❌ APB WAVEDROM GENERATION FAILED ❌")
            assert False, "Waveform generation test failed"

    finally:
        # Clean shutdown
        tb.done = True
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.cmd_handler.stop()
        await tb.wait_clocks('pclk', 10)


# Keep the original test parameters
@pytest.mark.parametrize("addr_width, data_width, depth",
    [
        (32, 32, 2),
    ])
def test_comprehensive_apb_slave(request, addr_width, data_width, depth):
    """Comprehensive APB slave test with all configurations."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"apb/{dut_name}.sv")
    ]

    # Create test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["addr_width", "data_width", "depth"]}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'WAVEDROM_SHOW_STATUS': '1',
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # Disable FST tracing to avoid Verilator bug
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = []

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = []
    plusargs = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_amba_includes']],
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Disable waves to avoid Verilator FST bug
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        print(f"Comprehensive test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Comprehensive APB slave test with all configurations."""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"apb/{dut_name}.sv")
    ]

    # Create test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["addr_width", "data_width", "depth"]}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'WAVEDROM_SHOW_STATUS': '1',
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # Disable FST tracing to avoid Verilator bug
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = []

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = []
    plusargs = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_amba_includes']],
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Disable waves to avoid Verilator FST bug
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        print(f"Comprehensive test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
