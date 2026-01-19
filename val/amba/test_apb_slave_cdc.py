# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBSlaveCDCTB
# Purpose: Enhanced APB-GAXI CDC testbench with comprehensive testing and debug capabilitie
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction, APBPacket
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import create_apb_master, create_apb_monitor
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
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

# WaveDrom support
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver,
    TemporalConstraint,
    TemporalEvent,
    SignalTransition,
    TemporalRelation
)
from CocoTBFramework.tbclasses.wavedrom_user.apb import (
    get_apb_field_config,
    create_apb_wavejson_generator,
    setup_apb_constraints_with_boundaries
)
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import (
    get_gaxi_field_config,
    create_gaxi_wavejson_generator
)


class APBSlaveCDCTB(TBBase):
    """Enhanced APB-GAXI CDC testbench with comprehensive testing and debug capabilities."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.done = False
        self.num_line = 32768  # Large memory for comprehensive testing

        # Enhanced debug tracking
        self.debug_stats = {
            'apb_writes': 0,
            'apb_reads': 0,
            'gaxi_commands': 0,
            'gaxi_responses': 0,
            'cmd_handler_responses': 0,
            'signal_checks': {},
            'clock_domain_crossings': 0,
            'aclk_cycles': 0,
            'pclk_cycles': 0
        }

        # Test statistics for comprehensive suite
        self.test_stats = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': 0,
            'total_transactions': 0,
            'error_transactions': 0,
            'configurations_tested': set(),
            'cdc_violations': 0
        }

        # Initialize components with CDC-specific setup
        self._init_cdc_components_with_debug()

    def _init_cdc_components_with_debug(self):
        """Initialize CDC components with enhanced debugging for cross-domain issues."""
        self.log.info("=== APB-GAXI CDC: Component initialization ===")

        # Memory model - larger for comprehensive testing
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)
        self.log.info(f"✓ Memory model created: {self.num_line} lines x {self.STRB_WIDTH} bytes")

        # APB components - these should be unchanged by GAXI refactor
        self.apb_master = create_apb_master(
            self.dut, 'APB Master', 's_apb', self.dut.pclk,
            addr_width=self.ADDR_WIDTH, data_width=self.DATA_WIDTH,
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log
        )
        self.log.info("✓ APB Master created (pclk domain)")

        self.apb_monitor = create_apb_monitor(
            self.dut, 'APB Monitor', 's_apb', self.dut.pclk,
            addr_width=self.ADDR_WIDTH, data_width=self.DATA_WIDTH,
            log=self.log
        )
        self.log.info("✓ APB Monitor created (pclk domain)")

        # GAXI field configurations
        self.apbgaxiconfig = APBGAXIConfig(
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            strb_width=self.STRB_WIDTH
        )
        self.cmd_field_config = self.apbgaxiconfig.create_cmd_field_config()
        self.rsp_field_config = self.apbgaxiconfig.create_rsp_field_config()

        self.log.info(f"✓ Field configs created for CDC operation")

        # CDC-specific GAXI components with separate clock domains
        super_debug = True  # Enable debug for CDC testing

        # Command interface (slave side - receives commands from APB slave)
        # CDC: Uses aclk (fast clock) for command processing
        try:
            self.cmd_monitor = create_gaxi_monitor(
                self.dut, 'CMD Monitor', '', self.dut.aclk,  # CDC: aclk domain
                field_config=self.cmd_field_config,
                pkt_prefix='cmd', is_slave=True,
                log=self.log, super_debug=super_debug, multi_sig=True
            )
            self.log.info("✓ CMD Monitor created (aclk domain)")

        except Exception as e:
            self.log.error(f"✗ CMD Monitor creation failed: {e}")
            raise

        try:
            self.cmd_slave = create_gaxi_slave(
                self.dut, 'CMD Slave', '', self.dut.aclk,  # CDC: aclk domain
                field_config=self.cmd_field_config,
                pkt_prefix='cmd',
                randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
                memory_model=None,  # Don't use memory in slave for CDC
                log=self.log, super_debug=super_debug, multi_sig=True
            )
            self.log.info("✓ CMD Slave created (aclk domain)")

        except Exception as e:
            self.log.error(f"✗ CMD Slave creation failed: {e}")
            raise

        # Response interface (master side - sends responses back to APB slave)
        # CDC: Uses pclk (slower clock) for response generation
        try:
            self.rsp_monitor = create_gaxi_monitor(
                self.dut, 'RSP Monitor', '', self.dut.aclk,  # CDC: aclk domain
                field_config=self.rsp_field_config,
                pkt_prefix='rsp', is_slave=False,
                log=self.log, super_debug=super_debug, multi_sig=True
            )
            self.log.info("✓ RSP Monitor created (pclk domain)")

        except Exception as e:
            self.log.error(f"✗ RSP Monitor creation failed: {e}")
            raise

        try:
            self.rsp_master = create_gaxi_master(
                self.dut, 'RSP Master', '', self.dut.aclk,  # CDC: aclk domain
                field_config=self.rsp_field_config,
                pkt_prefix='rsp',
                randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
                memory_model=None,
                log=self.log, super_debug=super_debug, multi_sig=True
            )
            self.log.info("✓ RSP Master created (pclk domain)")

        except Exception as e:
            self.log.error(f"✗ RSP Master creation failed: {e}")
            raise

        # Command handler - orchestrates the command/response flow across clock domains
        try:
            self.cmd_handler = GAXICommandHandler(
                master=self.rsp_master,
                slave=self.cmd_slave,
                memory_model=self.mem,
                log=self.log,
                response_generation_mode=True
            )
            self.log.info("✓ Command Handler created in response generation mode (CDC)")

        except Exception as e:
            self.log.error(f"✗ Command Handler creation failed: {e}")
            raise

        # Enhanced scoreboard for CDC testing
        self.apb_gaxi_scoreboard = APBGAXIScoreboard('CDC Scoreboard', log=self.log)
        self.log.info("✓ Enhanced Scoreboard created")

        # Connect callbacks with CDC-aware debugging
        self.log.info("Connecting CDC-aware callbacks...")

        try:
            self.apb_monitor.add_callback(self.debug_apb_callback)
            self.log.info("✓ APB Monitor callback connected (pclk domain)")
        except Exception as e:
            self.log.error(f"✗ APB Monitor callback failed: {e}")

        try:
            self.cmd_monitor.add_callback(self.debug_cmd_callback)
            self.log.info("✓ CMD Monitor callback connected (aclk domain)")
        except Exception as e:
            self.log.error(f"✗ CMD Monitor callback failed: {e}")

        try:
            self.rsp_monitor.add_callback(self.debug_rsp_callback)
            self.log.info("✓ RSP Monitor callback connected (pclk domain)")
        except Exception as e:
            self.log.error(f"✗ RSP Monitor callback failed: {e}")

        self.log.info("=== APB-GAXI CDC: Component initialization complete ===")

    def debug_apb_callback(self, transaction):
        """CDC-aware APB transaction callback with cross-domain tracking."""
        try:
            pwrite = getattr(transaction, 'pwrite', None)
            paddr = getattr(transaction, 'paddr', None)

            # Track clock domain crossing
            self.debug_stats['clock_domain_crossings'] += 1

            if pwrite == 1:
                self.debug_stats['apb_writes'] += 1
                pwdata = getattr(transaction, 'pwdata', None)
                pstrb = getattr(transaction, 'pstrb', None)
                self.log.info(f"🔵 APB WRITE #{self.debug_stats['apb_writes']} (pclk→aclk): "
                                f"addr=0x{paddr:X}, data=0x{pwdata:X}, strb=0x{pstrb:X}")
            elif pwrite == 0:
                self.debug_stats['apb_reads'] += 1
                prdata = getattr(transaction, 'prdata', None)
                pslverr = getattr(transaction, 'pslverr', None)
                self.log.info(f"🔵 APB READ #{self.debug_stats['apb_reads']} (pclk→aclk): "
                                f"addr=0x{paddr:X}, data=0x{prdata:X}, err={pslverr}")
            else:
                self.log.error(f"🔴 APB UNKNOWN: pwrite={pwrite}")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_apb_transaction(transaction)
            self.log.debug("✓ APB transaction added to CDC scoreboard")

        except Exception as e:
            self.log.error(f"🔴 APB CDC callback error: {e}")

    def debug_cmd_callback(self, transaction):
        """CDC-aware GAXI command callback with aclk domain tracking."""
        try:
            self.debug_stats['gaxi_commands'] += 1
            self.debug_stats['aclk_cycles'] += 1

            # Handle both field storage methods
            if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
                fields = transaction.fields
                pwrite = fields.get('pwrite', 'N/A')
                paddr = fields.get('paddr', 'N/A')
                pwdata = fields.get('pwdata', 'N/A')
                self.log.info(f"🟢 GAXI CMD #{self.debug_stats['gaxi_commands']} (aclk): "
                                f"pwrite={pwrite}, addr=0x{paddr:X}, data=0x{pwdata:X}")
            else:
                pwrite = getattr(transaction, 'pwrite', 'N/A')
                paddr = getattr(transaction, 'paddr', 'N/A')
                pwdata = getattr(transaction, 'pwdata', 'N/A')
                self.log.info(f"🟢 GAXI CMD #{self.debug_stats['gaxi_commands']} (aclk): "
                                f"pwrite={pwrite}, addr=0x{paddr:X}, data=0x{pwdata:X}")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)
            self.log.debug("✓ GAXI CMD transaction added to CDC scoreboard")

        except Exception as e:
            self.log.error(f"🔴 GAXI CMD CDC callback error: {e}")

    def debug_rsp_callback(self, transaction):
        """CDC-aware GAXI response callback with pclk domain tracking."""
        try:
            self.debug_stats['gaxi_responses'] += 1
            self.debug_stats['pclk_cycles'] += 1

            # Handle both field storage methods
            if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
                fields = transaction.fields
                prdata = fields.get('prdata', 'N/A')
                pslverr = fields.get('pslverr', 'N/A')
                self.log.info(f"🟡 GAXI RSP #{self.debug_stats['gaxi_responses']} (aclk→pclk): "
                                f"data=0x{prdata:X}, err={pslverr}")
            else:
                prdata = getattr(transaction, 'prdata', 'N/A')
                pslverr = getattr(transaction, 'pslverr', 'N/A')
                self.log.info(f"🟡 GAXI RSP #{self.debug_stats['gaxi_responses']} (aclk→pclk): "
                                f"data=0x{prdata:X}, err={pslverr}")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)
            self.log.debug("✓ GAXI RSP transaction added to CDC scoreboard")

        except Exception as e:
            self.log.error(f"🔴 GAXI RSP CDC callback error: {e}")

    async def reset_dut(self):
        """Enhanced CDC reset with separate clock domain handling."""
        self.log.info('=== APB-GAXI CDC: Starting reset ===')

        # CDC Reset: Both clock domains need reset
        self.dut.aresetn.value = 0  # AXI clock domain (aclk)
        self.dut.presetn.value = 0  # APB clock domain (pclk)

        # Wait for both clock domains
        await self.wait_clocks('aclk', 5)
        await self.wait_clocks('pclk', 5)

        # Reset all components
        await self.apb_master.reset_bus()
        await self.cmd_slave.reset_bus()
        await self.rsp_master.reset_bus()

        # Hold reset longer for CDC stability
        await self.wait_clocks('aclk', 10)
        await self.wait_clocks('pclk', 10)

        # Release reset for both domains
        self.dut.aresetn.value = 1  # AXI clock domain
        self.dut.presetn.value = 1  # APB clock domain

        # Wait for CDC synchronization
        await self.wait_clocks('aclk', 15)
        await self.wait_clocks('pclk', 15)

        # Clear tracking
        self.debug_stats = {k: 0 if isinstance(v, int) else {} for k, v in self.debug_stats.items()}
        self.apb_gaxi_scoreboard.clear()

        self.log.info('=== APB-GAXI CDC: Reset complete ===')

    async def check_cdc_signal_connectivity(self):
        """Check signal connectivity for CDC-specific signals."""
        self.log.info("=== CHECKING CDC SIGNAL CONNECTIVITY ===")

        signal_checks = {}

        # Check APB signals (pclk domain)
        apb_signals = ['PSEL', 'PENABLE', 'PWRITE', 'PADDR', 'PWDATA', 'PRDATA', 'PREADY', 'PSTRB', 'PPROT', 'PSLVERR']
        for sig in apb_signals:
            try:
                signal_name = f's_apb_{sig}'
                signal_obj = getattr(self.dut, signal_name)
                signal_checks[f"{signal_name} (pclk)"] = '✓ accessible'
                self.log.debug(f"✓ {signal_name} accessible in pclk domain")
            except AttributeError:
                signal_checks[f"{signal_name} (pclk)"] = '✗ missing'
                self.log.warning(f"✗ {signal_name} not found in pclk domain")

        # Check GAXI command signals (aclk domain)
        cmd_signals = ['cmd_valid', 'cmd_ready', 'cmd_pwrite', 'cmd_paddr', 'cmd_pwdata', 'cmd_pstrb', 'cmd_pprot']
        for sig in cmd_signals:
            for direction in ['', '']:
                try:
                    signal_name = f'{direction}{sig}'
                    signal_obj = getattr(self.dut, signal_name)
                    signal_checks[f"{signal_name} (aclk)"] = '✓ accessible'
                    self.log.debug(f"✓ {signal_name} accessible in aclk domain")
                except AttributeError:
                    signal_checks[f"{signal_name} (aclk)"] = '✗ missing'
                    self.log.debug(f"✗ {signal_name} not found in aclk domain")

        # Check GAXI response signals (pclk domain)
        rsp_signals = ['rsp_valid', 'rsp_ready', 'rsp_prdata', 'rsp_pslverr']
        for sig in rsp_signals:
            for direction in ['', '']:
                try:
                    signal_name = f'{direction}{sig}'
                    signal_obj = getattr(self.dut, signal_name)
                    signal_checks[f"{signal_name} (pclk)"] = '✓ accessible'
                    self.log.debug(f"✓ {signal_name} accessible in pclk domain")
                except AttributeError:
                    signal_checks[f"{signal_name} (pclk)"] = '✗ missing'
                    self.log.debug(f"✗ {signal_name} not found in pclk domain")

        # Check CDC-specific clocks and resets
        cdc_signals = ['aclk', 'pclk', 'aresetn', 'presetn']
        for sig in cdc_signals:
            try:
                signal_obj = getattr(self.dut, sig)
                signal_checks[f"{sig} (CDC)"] = '✓ accessible'
                self.log.debug(f"✓ {sig} CDC signal accessible")
            except AttributeError:
                signal_checks[f"{sig} (CDC)"] = '✗ missing'
                self.log.warning(f"✗ {sig} CDC signal not found")

        self.debug_stats['signal_checks'] = signal_checks

        # Summary
        accessible_count = sum(1 for status in signal_checks.values() if '✓' in status)
        total_count = len(signal_checks)
        self.log.info(f"CDC Signal connectivity: {accessible_count}/{total_count} signals accessible")

        if accessible_count < total_count:
            self.log.warning("Some CDC signals missing - check clock domain assignments")
            for sig, status in signal_checks.items():
                if '✗' in status:
                    self.log.warning(f"  Missing: {sig}")

        return accessible_count >= len(apb_signals) + len(cdc_signals)  # At least core signals should work

    async def wait_for_queue_empty(self, obj, timeout=5000):
        """Enhanced queue empty waiting with CDC awareness."""
        start_time = get_sim_time('ns')

        queue = getattr(obj, 'transmit_queue', None)
        if queue is None:
            self.log.debug(f"No transmit_queue found on {obj.__class__.__name__}")
            return

        initial_length = len(queue)
        if initial_length > 0:
            self.log.debug(f"Waiting for {obj.__class__.__name__} queue to empty (initial: {initial_length})")

        cycle_count = 0
        while len(queue) > 0:
            # For CDC, wait on the appropriate clock domain
            if 'RSP' in obj.title:
                await self.wait_clocks('pclk', 1)  # Response components use pclk
            else:
                await self.wait_clocks('aclk', 1)  # Command components use aclk
            cycle_count += 1

            if cycle_count % 20 == 0:
                self.log.debug(f"{obj.__class__.__name__} queue: {len(queue)} items after {cycle_count} cycles")

            if get_sim_time('ns') - start_time > timeout:
                self.log.error(f"TIMEOUT: {obj.__class__.__name__} queue still has {len(queue)} items")
                break

    async def send_apb_write_read_pair(self, addr, data):
        """Enhanced write-read pair with CDC timing considerations."""
        self.log.info(f"=== CDC TESTING WRITE-READ PAIR: addr=0x{addr:X}, data=0x{data:X} ===")

        # Send write
        self.log.info("Sending WRITE (pclk domain)...")
        write_transaction = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
        write_packet = write_transaction.next()
        write_packet.pwrite = 1
        write_packet.paddr = addr
        write_packet.pwdata = data
        write_packet.pstrb = 0xF
        write_packet.direction = "WRITE"

        await self.apb_master.send(write_packet)
        await self.wait_for_queue_empty(self.apb_master)

        # CDC: Extra wait for cross-domain synchronization
        await self.wait_clocks('aclk', 10)  # Allow command processing
        await self.wait_clocks('pclk', 10)  # Allow response generation

        # Send read
        self.log.info("Sending READ (pclk domain)...")
        read_transaction = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
        read_packet = read_transaction.next()
        read_packet.pwrite = 0
        read_packet.paddr = addr
        read_packet.direction = "READ"

        await self.apb_master.send(read_packet)
        await self.wait_for_queue_empty(self.apb_master)

        # CDC: Extra wait for cross-domain synchronization
        await self.wait_clocks('aclk', 10)  # Allow command processing
        await self.wait_clocks('pclk', 10)  # Allow response generation

        self.log.info("=== CDC WRITE-READ PAIR COMPLETE ===")

    async def run_cdc_comprehensive_test(self):
        """Run comprehensive CDC test with cross-domain validation."""
        self.log.info("=== STARTING APB-GAXI CDC COMPREHENSIVE TEST ===")

        # Step 1: Check CDC signal connectivity
        signals_ok = await self.check_cdc_signal_connectivity()

        # Step 2: Start command handler (critical for response generation)
        self.log.info("Starting CDC command handler...")
        try:
            await self.cmd_handler.start()
            handler_stats = self.cmd_handler.get_stats()
            self.log.info(f"✓ CDC Command handler started: {handler_stats}")
        except Exception as e:
            self.log.error(f"✗ CDC Command handler start failed: {e}")
            return False

        # Step 3: Wait for CDC stabilization
        await self.wait_clocks('aclk', 15)
        await self.wait_clocks('pclk', 15)

        # Step 4: Test the full APB->GAXI->APB flow across clock domains
        test_addr = 0x1000
        test_data = 0x12345678

        initial_stats = self.debug_stats.copy()
        await self.send_apb_write_read_pair(test_addr, test_data)

        # Step 5: Check what happened across clock domains
        self.log.info("=== CDC FLOW ANALYSIS ===")
        self.log.info(f"APB Writes: {initial_stats['apb_writes']} → {self.debug_stats['apb_writes']}")
        self.log.info(f"APB Reads: {initial_stats['apb_reads']} → {self.debug_stats['apb_reads']}")
        self.log.info(f"GAXI Commands (aclk): {initial_stats['gaxi_commands']} → {self.debug_stats['gaxi_commands']}")
        self.log.info(f"GAXI Responses (pclk): {initial_stats['gaxi_responses']} → {self.debug_stats['gaxi_responses']}")
        self.log.info(f"Clock Domain Crossings: {self.debug_stats['clock_domain_crossings']}")

        # Step 6: Command handler analysis
        handler_stats = self.cmd_handler.get_stats()
        self.log.info(f"CDC Command Handler Stats: {handler_stats}")

        # Step 7: Scoreboard analysis with CDC timing
        await self.wait_clocks('aclk', 25)  # Allow final aclk processing
        await self.wait_clocks('pclk', 25)  # Allow final pclk processing
        scoreboard_stats = self.apb_gaxi_scoreboard.get_stats()
        self.log.info(f"CDC Scoreboard Stats: {scoreboard_stats}")

        # Step 8: Determine what's broken in CDC context
        apb_flow_working = (self.debug_stats['apb_writes'] > 0 and self.debug_stats['apb_reads'] > 0)
        gaxi_cmd_working = (self.debug_stats['gaxi_commands'] > 0)
        gaxi_rsp_working = (self.debug_stats['gaxi_responses'] > 0)
        scoreboard_working = (scoreboard_stats['matched_pairs'] > 0)
        cdc_working = (self.debug_stats['clock_domain_crossings'] > 0)

        self.log.info("=== CDC COMPREHENSIVE ANALYSIS ===")
        self.log.info(f"Signal connectivity: {'✓' if signals_ok else '✗'}")
        self.log.info(f"APB transaction flow (pclk): {'✓' if apb_flow_working else '✗'}")
        self.log.info(f"GAXI command generation (aclk): {'✓' if gaxi_cmd_working else '✗'}")
        self.log.info(f"GAXI response generation (pclk): {'✓' if gaxi_rsp_working else '✗'}")
        self.log.info(f"CDC clock domain crossing: {'✓' if cdc_working else '✗'}")
        self.log.info(f"Scoreboard matching: {'✓' if scoreboard_working else '✗'}")

        # CDC-specific issue identification
        if not gaxi_cmd_working:
            self.log.error("🔥 CDC ISSUE: GAXI commands not crossing pclk→aclk - check CDC handshake")
        if not gaxi_rsp_working:
            self.log.error("🔥 CDC ISSUE: GAXI responses not crossing aclk→pclk - check CDC response path")
        if not cdc_working:
            self.log.error("🔥 CDC ISSUE: No clock domain crossings detected - check CDC implementation")

        success = apb_flow_working and gaxi_cmd_working and gaxi_rsp_working and scoreboard_working and cdc_working

        if success:
            self.log.info("✓ APB-GAXI CDC COMPREHENSIVE TEST PASSED")
        else:
            self.log.error("✗ APB-GAXI CDC COMPREHENSIVE TEST FAILED - CDC issues identified above")

        return success

    def set_randomizer_config(self, apb_master_config=None, apb_slave_config=None, axi_config=None):
        """Set randomizer configurations for all components with CDC awareness."""
        if apb_master_config:
            self.apb_master.set_randomizer(FlexRandomizer(apb_master_config))
            self.test_stats['configurations_tested'].add(f"apb_master_{apb_master_config}")

        if apb_slave_config:
            # For CDC, slave config would apply to cmd_slave
            self.test_stats['configurations_tested'].add(f"apb_slave_{apb_slave_config}")

        if axi_config:
            if 'master' in axi_config:
                self.rsp_master.set_randomizer(FlexRandomizer(axi_config['master']))
            if 'slave' in axi_config:
                self.cmd_slave.set_randomizer(FlexRandomizer(axi_config['slave']))
            self.test_stats['configurations_tested'].add(f"axi_{axi_config}")

    async def run_test_sequence(self, sequence_config, num_transactions=None):
        """Run a test sequence with CDC-aware timing."""
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

                # CDC: Add extra delays for cross-domain synchronization
                if i < num_transactions - 1:
                    delay = sequence_config.next_delay()
                    if delay > 0:
                        await self.wait_clocks('pclk', delay)
                        await self.wait_clocks('aclk', delay // 2)  # Some aclk cycles too

        except Exception as e:
            self.log.error(f"CDC test sequence failed: {e}")
            self.test_stats['failed_tests'] += 1
            raise

        return results

    async def send_apb_transaction(self, is_write, addr, data=None, strobe=None):
        """Send APB transaction with CDC-aware timing."""
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

        # CDC: Wait for cross-domain processing
        await self.wait_clocks('aclk', 5)  # Command processing
        await self.wait_clocks('pclk', 5)  # Response processing

        return xmit_transaction

    async def verify_scoreboard(self, timeout=2000):
        """Verify scoreboard with CDC-aware timing."""
        # CDC: Longer timeout for cross-domain synchronization
        result = await self.apb_gaxi_scoreboard.check_scoreboard(timeout)

        if result:
            self.test_stats['passed_tests'] += 1
            self.log.info("CDC Scoreboard verification passed")
        else:
            self.test_stats['failed_tests'] += 1
            self.log.error("CDC Scoreboard verification failed")

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

    # Enhanced test sequence generators for CDC
    def create_cdc_basic_sequence(self, num_txns=5):
        """Create basic CDC test sequence with cross-domain considerations."""
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
            data_seq.append(0)
            strb_seq.append(0xF)

        return APBSequence(
            name="cdc_basic",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=[5] * len(pwrite_seq)  # Longer delays for CDC
        )

    def create_cdc_burst_sequence(self, num_txns=10):
        """Create burst sequence optimized for CDC testing."""
        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        for i in range(num_txns//2):
            # Write
            pwrite_seq.append(True)
            addr_seq.append(0x2000 + i*4)
            data_seq.append(0x20000 + i)
            strb_seq.append(0xF)

            # Read
            pwrite_seq.append(False)
            addr_seq.append(0x2000 + i*4)
            data_seq.append(0)
            strb_seq.append(0xF)

        return APBSequence(
            name="cdc_burst",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=[2] * len(pwrite_seq)  # Faster for CDC stress
        )

    def create_cdc_stress_sequence(self, num_txns=20):
        """Create stress sequence for CDC validation."""
        pwrite_seq = [True, False] * (num_txns//2)
        addr_seq = [0x3000 + i*4 for i in range(num_txns)]
        data_seq = [0x30000 + i for i in range(num_txns)]
        strb_seq = [0xF] * num_txns

        return APBSequence(
            name="cdc_stress",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=[1] * num_txns,  # Minimal delays for stress
            master_randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fast'])
        )

    async def run_comprehensive_cdc_test_suite(self):
        """Run comprehensive CDC test suite with all configurations."""
        self.log.info("=== Starting Comprehensive CDC APB Test Suite ===")

        # CDC-specific test configuration matrix
        test_matrix = [
            ('fixed', 'fixed', 'CDC Basic Fixed Timing'),
            ('constrained', 'constrained', 'CDC Constrained Random Timing'),
            ('fast', 'fast', 'CDC Fast Timing'),
            ('backtoback', 'backtoback', 'Back-to-Back Transactions'),
        ]

        test_sequences = [
            ('basic_write_read', lambda: self.create_basic_write_sequence(3)),
            ('basic_read_test', lambda: self.create_basic_read_sequence(3)),
            ('burst_write_read', lambda: self.create_burst_sequence(6)),
            ('sequential_read_test', lambda: self.create_sequential_read_test(5)),
            ('boundary_addresses', lambda: self.create_boundary_address_sequence()),
            ('strobe_patterns', lambda: self.create_strobe_pattern_sequence()),
            ('data_patterns', lambda: self.create_data_pattern_sequence()),
            ('cdc_basic', lambda: self.create_cdc_basic_sequence(3)),
            ('cdc_burst', lambda: self.create_cdc_burst_sequence(6)),
            ('cdc_stress', lambda: self.create_cdc_stress_sequence(10)),
        ]

        total_test_combinations = len(test_matrix) * len(test_sequences)
        current_test = 0

        for apb_config, axi_config, config_desc in test_matrix:
            for seq_name, seq_generator in test_sequences:
                current_test += 1
                self.log.info(f"=== CDC Test {current_test}/{total_test_combinations}: {config_desc} - {seq_name} ===")

                try:
                    # Set configuration
                    self.set_randomizer_config(
                        apb_master_config=APB_MASTER_RANDOMIZER_CONFIGS[apb_config],
                        axi_config=AXI_RANDOMIZER_CONFIGS[axi_config]
                    )

                    # Generate and run sequence
                    sequence = seq_generator()
                    await self.run_test_sequence(sequence)

                    # Verify results with CDC timing
                    result = await self.verify_scoreboard(timeout=3000)

                    if result:
                        self.log.info(f"✓ CDC Test {current_test} PASSED: {config_desc} - {seq_name}")
                    else:
                        self.log.error(f"✗ CDC Test {current_test} FAILED: {config_desc} - {seq_name}")

                    # Allow CDC settling time between tests
                    await self.wait_clocks('aclk', 20)
                    await self.wait_clocks('pclk', 20)

                    self.test_stats['total_tests'] += 1

                except Exception as e:
                    self.log.error(f"✗ CDC Test {current_test} EXCEPTION: {config_desc} - {seq_name}: {e}")
                    self.test_stats['failed_tests'] += 1
                    continue

        # Generate final report
        self.generate_cdc_test_report()

    def generate_cdc_test_report(self):
        """Generate comprehensive CDC test report."""
        self.log.info("=== COMPREHENSIVE CDC TEST REPORT ===")
        self.log.info(f"Total Tests: {self.test_stats['total_tests']}")
        self.log.info(f"Passed Tests: {self.test_stats['passed_tests']}")
        self.log.info(f"Failed Tests: {self.test_stats['failed_tests']}")
        self.log.info(f"Total Transactions: {self.test_stats['total_transactions']}")
        self.log.info(f"Error Transactions: {self.test_stats['error_transactions']}")
        self.log.info(f"CDC Violations: {self.test_stats['cdc_violations']}")
        self.log.info(f"Clock Domain Crossings: {self.debug_stats['clock_domain_crossings']}")

        if self.test_stats['total_tests'] > 0:
            pass_rate = (self.test_stats['passed_tests'] / self.test_stats['total_tests']) * 100
            self.log.info(f"CDC Pass Rate: {pass_rate:.1f}%")

        self.log.info(f"Configurations Tested: {len(self.test_stats['configurations_tested'])}")
        for config in sorted(self.test_stats['configurations_tested']):
            self.log.info(f"  - {config}")

        self.log.info("=== END CDC TEST REPORT ===")


@cocotb.test(timeout_time=10, timeout_unit="sec")
async def apb_slave_cdc_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for APB slave CDC.

    When enabled, would generate 7 comprehensive APB scenarios plus 3 CDC-specific scenarios:

    APB scenarios (using comprehensive preset):
    1. Basic write transaction
    2. Basic read transaction
    3. Back-to-back writes
    4. Back-to-back reads
    5. Write-to-read transition
    6. Read-to-write transition
    7. Error response (if supported)

    CDC-specific scenarios (custom constraints):
    8. Write CDC timing (APB domain → GAXI domain)
    9. Read CDC timing (GAXI domain → APB domain)
    10. Back-to-back CDC (showing async operation)

    All waveforms would include clock (both pclk and aclk) and reset signals.

    Enable with ENABLE_WAVEDROM=1 environment variable.

    NOTE: Multi-clock domain support is enabled in WaveDrom framework.
    This test generates waveforms showing both APB and GAXI domains with CDC timing.
    """
    # Setup testbench
    tb = APBSlaveCDCTB(dut)

    # Start both clocks for CDC (5:1 ratio for actual timing)
    await tb.start_clock('pclk', 10, 'ns')  # APB clock - 100MHz
    await tb.start_clock('aclk',  2, 'ns')  # AXI clock - 500MHz (5x faster, but will display as 2x with period=0.4)

    await tb.reset_dut()

    # Setup WaveDrom solver with BOTH APB and GAXI signals
    apb_field_config = get_apb_field_config(tb.ADDR_WIDTH, tb.DATA_WIDTH)
    gaxi_field_config = get_gaxi_field_config(tb.DATA_WIDTH)

    # Create generator that can handle both protocols
    wave_generator = create_apb_wavejson_generator(apb_field_config)

    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=apb_field_config
    )

    # Add both clock groups (APB and AXI domains)
    # Use 'default' for APB domain as expected by comprehensive preset
    wave_solver.add_clock_group('default', dut.pclk)
    wave_solver.add_clock_group('axi_domain', dut.aclk)

    # WAVEDROM REQUIREMENT v1.2: ALL waveforms MUST include clock and reset
    # Bind APB slave signals (s_apb_* prefix) with clock and reset
    apb_signals = {
        'pclk': 'pclk',
        'presetn': 'presetn',
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
    wave_solver.add_interface("apb", apb_signals, field_config=apb_field_config)

    # Bind CMD/RSP signals for CDC visualization
    # Note: The apb_slave_cdc module uses cmd_*/rsp_* naming (not gaxi_cmd_*)
    cmd_signals = {
        'aclk': 'aclk',
        'aresetn': 'aresetn',
        'valid': 'cmd_valid',
        'ready': 'cmd_ready',
        'pwrite': 'cmd_pwrite',
        'paddr': 'cmd_paddr',
        'pwdata': 'cmd_pwdata'
    }
    wave_solver.add_interface("cmd", cmd_signals, field_config=gaxi_field_config)

    rsp_signals = {
        'valid': 'rsp_valid',
        'ready': 'rsp_ready',
        'prdata': 'rsp_prdata',
        'pslverr': 'rsp_pslverr'
    }
    wave_solver.add_interface("rsp", rsp_signals, field_config=gaxi_field_config)

    # Create CDC-aware signal list (APB + CMD + RSP interfaces)
    cdc_signals_to_show = [
        'apb_pclk', 'cmd_aclk', '|',  # Both clocks (period will be added post-generation)
        'apb_presetn', 'cmd_aresetn', '|',  # Both resets
        ['APB', 'apb_psel', 'apb_penable', 'apb_pready', 'apb_pwrite', 'apb_paddr', 'apb_pwdata', 'apb_prdata', 'apb_pslverr'], '|',
        ['CMD', 'cmd_valid', 'cmd_ready', 'cmd_pwrite', 'cmd_paddr', 'cmd_pwdata'], '|',
        ['RSP', 'rsp_valid', 'rsp_ready', 'rsp_prdata', 'rsp_pslverr']
    ]

    # Clock period configuration for VISUAL 1:2 ratio (pclk:aclk)
    # Actual hardware is 5:1 (10ns:2ns), but we display as 1:2 for readability
    # This will be applied to generated WaveJSON to make aclk visually compact
    clock_periods = {
        'apb_pclk': 1.0,   # Base period (full width)
        'cmd_aclk': 0.4    # 40% period (visually compact, appears ~2x faster)
    }

    # Manually create comprehensive constraints with CDC-aware signal lists
    from CocoTBFramework.tbclasses.wavedrom_user.apb import (
        create_apb_write_sequence_constraint,
        create_apb_read_sequence_constraint,
        APBConstraints
    )

    # 1. Basic write - with CDC signals
    constraint_write = create_apb_write_sequence_constraint(
        max_window=50, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_write.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_write)

    # 2. Basic read - with CDC signals
    constraint_read = create_apb_read_sequence_constraint(
        max_window=50, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_read.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_read)

    # 3. Back-to-back writes - with CDC signals
    constraint_b2b_wr = APBConstraints.back_to_back_writes(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_b2b_wr.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_b2b_wr)

    # 4. Back-to-back reads - with CDC signals
    constraint_b2b_rd = APBConstraints.back_to_back_reads(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_b2b_rd.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_b2b_rd)

    # 5. Write-to-read - with CDC signals
    constraint_wr2rd = APBConstraints.write_to_read(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_wr2rd.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_wr2rd)

    # 6. Read-to-write - with CDC signals
    constraint_rd2wr = APBConstraints.read_to_write(
        max_cycles=60, required=True, clock_group="default",
        field_config=apb_field_config, post_match_cycles=3
    )
    constraint_rd2wr.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_rd2wr)

    # 7. Error - with CDC signals (optional)
    constraint_err = APBConstraints.error_transaction(
        max_cycles=50, required=False, clock_group="default",
        field_config=apb_field_config
    )
    constraint_err.signals_to_show = cdc_signals_to_show
    wave_solver.add_constraint(constraint_err)

    dut._log.info(f"WaveDrom configured with 7 CDC-aware APB constraints (APB + CMD + RSP interfaces)")

    # Start command handler
    await tb.cmd_handler.start()

    # Start sampling for all scenarios
    await wave_solver.start_sampling()

    # Generate all 7 APB transaction scenarios (comprehensive preset)
    dut._log.info("=== Generating All APB Slave CDC WaveDrom Scenarios ===")

    # Scenarios 1-2: Basic write and read
    dut._log.info("Generating: Basic write and read with CDC")
    await tb.send_apb_transaction(is_write=True, addr=0x1000, data=0xDEADBEEF)
    await tb.wait_clocks('pclk', 10)  # Extra time for CDC
    await tb.send_apb_transaction(is_write=False, addr=0x1000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 3: Back-to-back writes
    dut._log.info("Generating: Back-to-back writes with CDC")
    await tb.send_apb_transaction(is_write=True, addr=0x2000, data=0xAAAAAAAA)
    await tb.send_apb_transaction(is_write=True, addr=0x2004, data=0xBBBBBBBB)
    await tb.wait_clocks('pclk', 10)

    # Scenario 4: Back-to-back reads
    dut._log.info("Generating: Back-to-back reads with CDC")
    await tb.send_apb_transaction(is_write=False, addr=0x3000)
    await tb.send_apb_transaction(is_write=False, addr=0x3004)
    await tb.wait_clocks('pclk', 10)

    # Scenario 5: Write-to-read transition
    dut._log.info("Generating: Write-to-read transition with CDC")
    await tb.send_apb_transaction(is_write=True, addr=0x4000, data=0x12345678)
    await tb.send_apb_transaction(is_write=False, addr=0x4000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 6: Read-to-write transition
    dut._log.info("Generating: Read-to-write transition with CDC")
    await tb.send_apb_transaction(is_write=False, addr=0x5000)
    await tb.send_apb_transaction(is_write=True, addr=0x5000, data=0x87654321)
    await tb.wait_clocks('pclk', 10)

    # Scenario 7: Error transaction (if supported by slave)
    dut._log.info("Generating: Error scenario (if slave supports)")
    await tb.wait_clocks('pclk', 5)

    # Stop sampling and generate all waveforms
    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    results = wave_solver.get_results()

    # Post-process WaveJSON files to add period attributes for visual 1:2 clock ratio
    import json
    import os
    import glob

    # WaveJSON files are written to current directory (where cocotb test runs)
    sim_build = os.getcwd()

    # Find all generated JSON files
    json_files = glob.glob(os.path.join(sim_build, "apb_*.json"))
    dut._log.info(f"Searching in: {sim_build}")
    dut._log.info(f"Found {len(json_files)} waveform JSON files to post-process")

    for json_file in json_files:
        try:
            with open(json_file, 'r') as f:
                wavejson = json.load(f)

            # Add period attribute to clock signals for visual 1:2 ratio display
            modified = False
            for sig in wavejson.get('signal', []):
                if isinstance(sig, dict) and sig.get('name') in clock_periods:
                    sig['period'] = clock_periods[sig['name']]
                    modified = True

            if modified:
                # Write back updated WaveJSON
                with open(json_file, 'w') as f:
                    json.dump(wavejson, f, indent=2)

                dut._log.info(f"✓ Added clock periods to {os.path.basename(json_file)}")
        except Exception as e:
            dut._log.warning(f"Could not update {os.path.basename(json_file)}: {e}")

    # Check if all required waveforms were generated
    if not results['all_required_satisfied']:
        dut._log.error(f"❌ NOT ALL REQUIRED WAVEFORMS GENERATED ❌")
        dut._log.error(f"Failed constraints: {results['failed_constraints']}")
        raise AssertionError(f"Required waveforms not generated: {results['failed_constraints']}")

    # Cleanup
    tb.done = True
    await tb.cmd_handler.stop()
    await tb.wait_clocks('pclk', 10)

    dut._log.info("=" * 80)
    dut._log.info(f"✅ APB Slave CDC WaveDrom Complete: {len(results['solutions'])} scenarios generated")
    dut._log.info("   Clock ratio: pclk (period=1.0) : aclk (period=0.5) = 1:2")
    dut._log.info("=" * 80)


@cocotb.test(timeout_time=60, timeout_unit="ms")  # Longer timeout for CDC tests
async def comprehensive_apb_cdc_test(dut):
    """Comprehensive APB-GAXI CDC test with cross-domain validation."""

    tb = APBSlaveCDCTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using CDC test seed: {seed}")

    # Start both clocks for CDC testing
    await tb.start_clock('aclk',  1, 'ns')  # Fast AXI clock - 1GHz
    await tb.start_clock('pclk', 10, 'ns')  # Slower APB clock - 100MHz

    # Reset DUT with CDC-specific reset sequence
    await tb.reset_dut()

    # Start command handler
    await tb.cmd_handler.start()

    try:
        # First run the basic CDC comprehensive test
        result = await tb.run_cdc_comprehensive_test()

        if result:
            tb.log.info("🎉 APB-GAXI CDC BASIC TEST PASSED! 🎉")
        else:
            tb.log.error("❌ APB-GAXI CDC BASIC TEST FAILED ❌")
            tb.log.error("Check the detailed CDC analysis above to identify cross-domain issues")
            assert False, "APB-GAXI CDC basic test failed"

        # Run comprehensive test suite
        await tb.run_comprehensive_cdc_test_suite()

        # Final verification with CDC timing
        final_result = await tb.verify_scoreboard(timeout=5000)

        if final_result and tb.test_stats['failed_tests'] == 0:
            tb.log.info("🎉 COMPREHENSIVE CDC TEST SUITE PASSED! 🎉")
        else:
            tb.log.error("❌ COMPREHENSIVE CDC TEST SUITE FAILED ❌")
            assert False, f"CDC test suite failed: {tb.test_stats['failed_tests']} failed tests"

    finally:
        # Clean shutdown
        tb.done = True
        await tb.cmd_handler.stop()
        # Final CDC synchronization wait
        await tb.wait_clocks('aclk', 20)
        await tb.wait_clocks('pclk', 20)


@pytest.mark.parametrize("addr_width, data_width, depth", [(32, 32, 2)])
def test_apb_slave_cdc_robust(request, addr_width, data_width, depth):
    """Robust APB-GAXI CDC test with comprehensive validation."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':  'rtl/amba/apb',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave_cdc"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'],         "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],  "cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_apb'],          "apb_slave.sv"),
        os.path.join(rtl_dict['rtl_apb'],         f"{dut_name}.sv")
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth"]
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(42),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]

    plusargs = ["--trace"]

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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ APB-GAXI CDC robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")

    except Exception as e:
        print(f"❌ APB-GAXI CDC robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC analysis.")
        raise


# ===============================================================================
# WaveDrom Test
# ===============================================================================

def generate_apb_slave_cdc_wavedrom_params():
    """Generate test parameters for APB slave CDC WaveDrom test."""
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Robust APB-GAXI CDC test with comprehensive validation."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':  'rtl/amba/apb',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave_cdc"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'],         "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],  "cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_apb'],          "apb_slave.sv"),
        os.path.join(rtl_dict['rtl_apb'],         f"{dut_name}.sv")
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth"]
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(42),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]

    plusargs = ["--trace"]

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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ APB-GAXI CDC robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")

    except Exception as e:
        print(f"❌ APB-GAXI CDC robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC analysis.")
        raise


# ===============================================================================
# WaveDrom Test
# ===============================================================================

def generate_apb_slave_cdc_wavedrom_params():
    """Generate test parameters for APB slave CDC WaveDrom test."""
    return [
        # (addr_width, data_width, rsp_depth, cmd_depth)
        (32, 32, 2, 2),  # Standard CDC configuration
    ]


wavedrom_params = generate_apb_slave_cdc_wavedrom_params()


@pytest.mark.parametrize("addr_width, data_width, rsp_depth, cmd_depth", wavedrom_params)
def test_apb_slave_cdc_wavedrom(request, addr_width, data_width, rsp_depth, cmd_depth):
    """
    APB slave CDC WaveDrom test - generates timing diagrams with APB and CMD/RSP interfaces.

    Run with: ENABLE_WAVEDROM=1 pytest val/amba/test_apb_slave_cdc.py::test_apb_slave_cdc_wavedrom -v
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':  'rtl/amba/apb',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave_cdc"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'],         "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],  "cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_apb'],          "apb_slave.sv"),
        os.path.join(rtl_dict['rtl_apb'],         f"{dut_name}.sv")
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    rd_str = TBBase.format_dec(rsp_depth, 3)
    cd_str = TBBase.format_dec(cmd_depth, 3)
    test_name_plus_params = f"test_{worker_id}_apb_slave_cdc_aw{aw_str}_dw{dw_str}_rd{rd_str}_cd{cd_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'DEPTH': rsp_depth,  # apb_slave_cdc uses single DEPTH parameter
    }

    extra_env = {
        'ENABLE_WAVEDROM': '1',  # ← Enable WaveDrom!
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_RSP_DEPTH': str(rsp_depth),
        'TEST_CMD_DEPTH': str(cmd_depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
    ]


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
            testcase="apb_slave_cdc_wavedrom_test",  # ← Run wavedrom test specifically!
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Disable FST - using WaveDrom instead
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ APB Slave CDC WaveDrom test completed!")
        print(f"Logs: {log_path}")
        print(f"WaveJSON files: val/amba/WaveJSON/test_apb_slave_cdc_*.json")
        print(f"Note: Waveforms show BOTH APB and CMD/RSP (GAXI) interfaces across clock domains")

    except Exception as e:
        print(f"❌ APB Slave CDC WaveDrom test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        raise
