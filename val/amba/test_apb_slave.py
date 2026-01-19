# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBGAXIDebugTB
# Purpose: APB-GAXI Debug testbench - focus on finding refactor issues.
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
from CocoTBFramework.components.wavedrom.wavejson_gen import create_apb_wavejson_generator
from CocoTBFramework.components.wavedrom.utility import get_apb_field_config
from CocoTBFramework.tbclasses.wavedrom_user.apb import setup_apb_constraints_with_boundaries


class APBGAXIDebugTB(TBBase):
    """APB-GAXI Debug testbench - focus on finding refactor issues."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = 32
        self.DATA_WIDTH = 32
        self.STRB_WIDTH = 4
        self.done = False
        self.num_line = 1024

        # Enhanced debug tracking
        self.debug_stats = {
            'apb_writes': 0,
            'apb_reads': 0,
            'gaxi_commands': 0,
            'gaxi_responses': 0,
            'cmd_handler_responses': 0,
            'signal_checks': {}
        }

        # Test statistics for comprehensive suite
        self.test_stats = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': 0,
            'total_transactions': 0,
            'error_transactions': 0,
            'configurations_tested': set()
        }

        # Initialize components
        self._init_components_with_debug()

    def _init_components_with_debug(self):
        """Initialize components with enhanced debugging for refactor issues."""
        self.log.info("=== APB-GAXI DEBUG: Component initialization ===")

        # Memory model
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)
        self.log.info(f"✓ Memory model created: {self.num_line} lines x {self.STRB_WIDTH} bytes")

        # APB components - these should be unchanged by GAXI refactor
        self.apb_master = create_apb_master(
            self.dut, 'APB Master', 's_apb', self.dut.pclk,
            addr_width=self.ADDR_WIDTH, data_width=self.DATA_WIDTH,
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log
        )
        self.log.info("✓ APB Master created")

        self.apb_monitor = create_apb_monitor(
            self.dut, 'APB Monitor', 's_apb', self.dut.pclk,
            addr_width=self.ADDR_WIDTH, data_width=self.DATA_WIDTH,
            log=self.log
        )
        self.log.info("✓ APB Monitor created")

        # GAXI field configurations - check if refactor changed these
        self.apbgaxiconfig = APBGAXIConfig(
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            strb_width=self.STRB_WIDTH
        )
        self.cmd_field_config = self.apbgaxiconfig.create_cmd_field_config()
        self.rsp_field_config = self.apbgaxiconfig.create_rsp_field_config()

        self.log.info(f"✓ Field configs created:")

        # Handle field_names as either method or property after refactor
        try:
            cmd_fields = self.cmd_field_config.field_names() if callable(getattr(self.cmd_field_config, 'field_names', None)) else getattr(self.cmd_field_config, 'field_names', 'unknown')
            self.log.info(f"  CMD fields: {list(cmd_fields) if hasattr(cmd_fields, '__iter__') and not isinstance(cmd_fields, str) else cmd_fields}")
        except Exception as e:
            self.log.info(f"  CMD fields: unable to access ({e})")

        try:
            rsp_fields = self.rsp_field_config.field_names() if callable(getattr(self.rsp_field_config, 'field_names', None)) else getattr(self.rsp_field_config, 'field_names', 'unknown')
            self.log.info(f"  RSP fields: {list(rsp_fields) if hasattr(rsp_fields, '__iter__') and not isinstance(rsp_fields, str) else rsp_fields}")
        except Exception as e:
            self.log.info(f"  RSP fields: unable to access ({e})")

        # GAXI components - focus on what the refactor might have changed
        self.log.info("Creating GAXI components with debug...")

        # Command interface (slave side - receives commands from APB slave)
        try:
            self.cmd_monitor = create_gaxi_monitor(
                self.dut, 'CMD Monitor', '', self.dut.pclk,
                field_config=self.cmd_field_config,
                pkt_prefix='cmd', is_slave=True,
                log=self.log, super_debug=True, multi_sig=True
            )
            self.log.info("✓ CMD Monitor created")

            # Check what signals it resolved to
            if hasattr(self.cmd_monitor, 'signal_resolver'):
                resolved = getattr(self.cmd_monitor.signal_resolver, 'resolved_signals', {})
                self.log.info(f"  CMD Monitor resolved signals: {resolved}")

        except Exception as e:
            self.log.error(f"✗ CMD Monitor creation failed: {e}")
            raise

        try:
            self.cmd_slave = create_gaxi_slave(
                self.dut, 'CMD Slave', '', self.dut.pclk,
                field_config=self.cmd_field_config,
                pkt_prefix='cmd',
                randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
                memory_model=None,  # Don't use memory in slave
                log=self.log, super_debug=True, multi_sig=True
            )
            self.log.info("✓ CMD Slave created")

            # Check what signals it resolved to
            if hasattr(self.cmd_slave, 'signal_resolver'):
                resolved = getattr(self.cmd_slave.signal_resolver, 'resolved_signals', {})
                self.log.info(f"  CMD Slave resolved signals: {resolved}")

        except Exception as e:
            self.log.error(f"✗ CMD Slave creation failed: {e}")
            raise

        # Response interface (master side - sends responses back to APB slave)
        try:
            self.rsp_monitor = create_gaxi_monitor(
                self.dut, 'RSP Monitor', '', self.dut.pclk,
                field_config=self.rsp_field_config,
                pkt_prefix='rsp', is_slave=False,
                log=self.log, super_debug=True, multi_sig=True
            )
            self.log.info("✓ RSP Monitor created")

            # Check what signals it resolved to
            if hasattr(self.rsp_monitor, 'signal_resolver'):
                resolved = getattr(self.rsp_monitor.signal_resolver, 'resolved_signals', {})
                self.log.info(f"  RSP Monitor resolved signals: {resolved}")

        except Exception as e:
            self.log.error(f"✗ RSP Monitor creation failed: {e}")
            raise

        try:
            self.rsp_master = create_gaxi_master(
                self.dut,
                'RSP Master',
                '',
                self.dut.pclk,
                field_config=self.rsp_field_config,
                pkt_prefix='rsp',
                randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
                memory_model=None,
                log=self.log,
                super_debug=True,
                multi_sig=True
            )
            self.log.info("✓ RSP Master created")

            # Check what signals it resolved to
            if hasattr(self.rsp_master, 'signal_resolver'):
                resolved = getattr(self.rsp_master.signal_resolver, 'resolved_signals', {})
                self.log.info(f"  RSP Master resolved signals: {resolved}")

        except Exception as e:
            self.log.error(f"✗ RSP Master creation failed: {e}")
            raise

        # Command handler - this orchestrates the command/response flow
        try:
            self.cmd_handler = GAXICommandHandler(
                master=self.rsp_master,
                slave=self.cmd_slave,
                memory_model=self.mem,
                log=self.log,
                response_generation_mode=True
            )
            self.log.info("✓ Command Handler created in response generation mode")

        except Exception as e:
            self.log.error(f"✗ Command Handler creation failed: {e}")
            raise

        # Scoreboard for matching APB and GAXI transactions
        self.apb_gaxi_scoreboard = APBGAXIScoreboard('Debug Scoreboard', log=self.log)
        self.log.info("✓ Scoreboard created")

        # Connect callbacks with enhanced debugging
        self.log.info("Connecting callbacks...")

        try:
            self.apb_monitor.add_callback(self.debug_apb_callback)
            self.log.info("✓ APB Monitor callback connected")
        except Exception as e:
            self.log.error(f"✗ APB Monitor callback failed: {e}")

        try:
            self.cmd_monitor.add_callback(self.debug_cmd_callback)
            self.log.info("✓ CMD Monitor callback connected")
        except Exception as e:
            self.log.error(f"✗ CMD Monitor callback failed: {e}")

        try:
            self.rsp_monitor.add_callback(self.debug_rsp_callback)
            self.log.info("✓ RSP Monitor callback connected")
        except Exception as e:
            self.log.error(f"✗ RSP Monitor callback failed: {e}")

        self.log.info("=== APB-GAXI DEBUG: Component initialization complete ===")

    def debug_apb_callback(self, transaction):
        """Debug APB transaction callback with detailed field inspection."""
        try:
            pwrite = getattr(transaction, 'pwrite', None)
            paddr = getattr(transaction, 'paddr', None)

            if pwrite == 1:
                self.debug_stats['apb_writes'] += 1
                pwdata = getattr(transaction, 'pwdata', None)
                pstrb = getattr(transaction, 'pstrb', None)
                self.log.info(f"🔵 APB WRITE #{self.debug_stats['apb_writes']}: addr=0x{paddr:X}, data=0x{pwdata:X}, strb=0x{pstrb:X}")
            elif pwrite == 0:
                self.debug_stats['apb_reads'] += 1
                prdata = getattr(transaction, 'prdata', None)
                pslverr = getattr(transaction, 'pslverr', None)
                self.log.info(f"🔵 APB READ #{self.debug_stats['apb_reads']}: addr=0x{paddr:X}, data=0x{prdata:X}, err={pslverr}")
            else:
                self.log.error(f"🔴 APB UNKNOWN: pwrite={pwrite}")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_apb_transaction(transaction)
            self.log.debug("✓ APB transaction added to scoreboard")

        except Exception as e:
            self.log.error(f"🔴 APB callback error: {e}")

    def debug_cmd_callback(self, transaction):
        """Debug GAXI command callback with field inspection."""
        try:
            self.debug_stats['gaxi_commands'] += 1

            # Handle both field storage methods
            if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
                fields = transaction.fields
                pwrite = fields.get('pwrite', 'N/A')
                paddr = fields.get('paddr', 'N/A')
                pwdata = fields.get('pwdata', 'N/A')
                self.log.info(f"🟢 GAXI CMD #{self.debug_stats['gaxi_commands']} (fields dict): pwrite={pwrite}, addr=0x{paddr:X}, data=0x{pwdata:X}")
            else:
                pwrite = getattr(transaction, 'pwrite', 'N/A')
                paddr = getattr(transaction, 'paddr', 'N/A')
                pwdata = getattr(transaction, 'pwdata', 'N/A')
                self.log.info(f"🟢 GAXI CMD #{self.debug_stats['gaxi_commands']} (attributes): pwrite={pwrite}, addr=0x{paddr:X}, data=0x{pwdata:X}")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)
            self.log.debug("✓ GAXI CMD transaction added to scoreboard")

        except Exception as e:
            self.log.error(f"🔴 GAXI CMD callback error: {e}")

    def debug_rsp_callback(self, transaction):
        """Debug GAXI response callback with field inspection."""
        try:
            self.debug_stats['gaxi_responses'] += 1

            # Handle both field storage methods
            if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
                fields = transaction.fields
                prdata = fields.get('prdata', 'N/A')
                pslverr = fields.get('pslverr', 'N/A')
                self.log.info(f"🟡 GAXI RSP #{self.debug_stats['gaxi_responses']} (fields dict): data=0x{prdata:X}, err={pslverr}")
            else:
                prdata = getattr(transaction, 'prdata', 'N/A')
                pslverr = getattr(transaction, 'pslverr', 'N/A')
                self.log.info(f"🟡 GAXI RSP #{self.debug_stats['gaxi_responses']} (attributes): data=0x{prdata:X}, err={pslverr}")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)
            self.log.debug("✓ GAXI RSP transaction added to scoreboard")

        except Exception as e:
            self.log.error(f"🔴 GAXI RSP callback error: {e}")

    async def reset_dut(self):
        """Reset DUT and all components."""
        self.log.info('=== APB-GAXI DEBUG: Starting reset ===')

        # Reset DUT
        self.dut.presetn.value = 0
        await self.wait_clocks('pclk', 5)

        # Reset all components
        await self.apb_master.reset_bus()
        await self.cmd_slave.reset_bus()
        await self.rsp_master.reset_bus()
        await self.wait_clocks('pclk', 5)

        # Release reset
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 10)

        # Clear tracking
        self.debug_stats = {k: 0 if isinstance(v, int) else {} for k, v in self.debug_stats.items()}
        self.apb_gaxi_scoreboard.clear()

        self.log.info('=== APB-GAXI DEBUG: Reset complete ===')

    async def check_signal_connectivity(self):
        """Check signal connectivity after refactor."""
        self.log.info("=== CHECKING SIGNAL CONNECTIVITY POST-REFACTOR ===")

        signal_checks = {}

        # Check APB signals
        apb_signals = ['PSEL', 'PENABLE', 'PWRITE', 'PADDR', 'PWDATA', 'PRDATA', 'PREADY', 'PSTRB', 'PPROT', 'PSLVERR']
        for sig in apb_signals:
            try:
                signal_name = f's_apb_{sig}'
                signal_obj = getattr(self.dut, signal_name)
                signal_checks[signal_name] = '✓ accessible'
                self.log.debug(f"✓ {signal_name} accessible")
            except AttributeError:
                signal_checks[signal_name] = '✗ missing'
                self.log.warning(f"✗ {signal_name} not found")

        # Check GAXI command signals (what your refactor might have changed)
        cmd_signals = ['cmd_valid', 'cmd_ready', 'cmd_pwrite', 'cmd_paddr', 'cmd_pwdata', 'cmd_pstrb', 'cmd_pprot']
        for sig in cmd_signals:
            for direction in ['', '']:
                try:
                    signal_name = f'{direction}{sig}'
                    signal_obj = getattr(self.dut, signal_name)
                    signal_checks[signal_name] = '✓ accessible'
                    self.log.debug(f"✓ {signal_name} accessible")
                except AttributeError:
                    signal_checks[signal_name] = '✗ missing'
                    self.log.debug(f"✗ {signal_name} not found")

        # Check GAXI response signals
        rsp_signals = ['rsp_valid', 'rsp_ready', 'rsp_prdata', 'rsp_pslverr']
        for sig in rsp_signals:
            for direction in ['', '']:
                try:
                    signal_name = f'{direction}{sig}'
                    signal_obj = getattr(self.dut, signal_name)
                    signal_checks[signal_name] = '✓ accessible'
                    self.log.debug(f"✓ {signal_name} accessible")
                except AttributeError:
                    signal_checks[signal_name] = '✗ missing'
                    self.log.debug(f"✗ {signal_name} not found")

        self.debug_stats['signal_checks'] = signal_checks

        # Summary
        accessible_count = sum(1 for status in signal_checks.values() if '✓' in status)
        total_count = len(signal_checks)
        self.log.info(f"Signal connectivity: {accessible_count}/{total_count} signals accessible")

        if accessible_count < total_count:
            self.log.warning("Some signals missing - this might be related to your refactor")
            for sig, status in signal_checks.items():
                if '✗' in status:
                    self.log.warning(f"  Missing: {sig}")

        return accessible_count >= len(apb_signals)  # At least APB signals should work

    async def wait_for_queue_empty(self, obj, timeout=5000):
        """Wait for transmit queue to empty."""
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
            await self.wait_clocks('pclk', 1)
            cycle_count += 1

            if cycle_count % 20 == 0:
                self.log.debug(f"{obj.__class__.__name__} queue: {len(queue)} items after {cycle_count} cycles")

            if get_sim_time('ns') - start_time > timeout:
                self.log.error(f"TIMEOUT: {obj.__class__.__name__} queue still has {len(queue)} items")
                break

    async def send_apb_write_read_pair(self, addr, data):
        """Send write then read to test full flow."""
        self.log.info(f"=== TESTING WRITE-READ PAIR: addr=0x{addr:X}, data=0x{data:X} ===")

        # Send write
        self.log.info("Sending WRITE...")
        write_transaction = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
        write_packet = write_transaction.next()
        write_packet.pwrite = 1
        write_packet.paddr = addr
        write_packet.pwdata = data
        write_packet.pstrb = 0xF
        write_packet.direction = "WRITE"

        await self.apb_master.send(write_packet)
        await self.wait_for_queue_empty(self.apb_master)
        await self.wait_clocks('pclk', 20)  # Allow processing time

        # Send read
        self.log.info("Sending READ...")
        read_transaction = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
        read_packet = read_transaction.next()
        read_packet.pwrite = 0
        read_packet.paddr = addr
        read_packet.direction = "READ"

        await self.apb_master.send(read_packet)
        await self.wait_for_queue_empty(self.apb_master)
        await self.wait_clocks('pclk', 20)  # Allow processing time

        self.log.info("=== WRITE-READ PAIR COMPLETE ===")

    async def run_refactor_debug_test(self):
        """Run test focused on finding refactor issues."""
        self.log.info("=== STARTING APB-GAXI REFACTOR DEBUG TEST ===")

        # Step 1: Check signal connectivity
        signals_ok = await self.check_signal_connectivity()

        # Step 2: Start command handler (critical for response generation)
        self.log.info("Starting command handler...")
        try:
            await self.cmd_handler.start()
            handler_stats = self.cmd_handler.get_stats()
            self.log.info(f"✓ Command handler started: {handler_stats}")
        except Exception as e:
            self.log.error(f"✗ Command handler start failed: {e}")
            return False

        # Step 3: Wait for stable state
        await self.wait_clocks('pclk', 10)

        # Step 4: Test the full APB->GAXI->APB flow
        test_addr = 0x1000
        test_data = 0x12345678

        initial_stats = self.debug_stats.copy()
        await self.send_apb_write_read_pair(test_addr, test_data)

        # Step 5: Check what happened
        self.log.info("=== FLOW ANALYSIS ===")
        self.log.info(f"APB Writes: {initial_stats['apb_writes']} → {self.debug_stats['apb_writes']}")
        self.log.info(f"APB Reads: {initial_stats['apb_reads']} → {self.debug_stats['apb_reads']}")
        self.log.info(f"GAXI Commands: {initial_stats['gaxi_commands']} → {self.debug_stats['gaxi_commands']}")
        self.log.info(f"GAXI Responses: {initial_stats['gaxi_responses']} → {self.debug_stats['gaxi_responses']}")

        # Step 6: Command handler analysis
        handler_stats = self.cmd_handler.get_stats()
        self.log.info(f"Command Handler Stats: {handler_stats}")

        # Step 7: Scoreboard analysis
        await self.wait_clocks('pclk', 50)  # Allow final processing
        scoreboard_stats = self.apb_gaxi_scoreboard.get_stats()
        self.log.info(f"Scoreboard Stats: {scoreboard_stats}")

        # Step 8: Determine what's broken
        apb_flow_working = (self.debug_stats['apb_writes'] > 0 and self.debug_stats['apb_reads'] > 0)
        gaxi_cmd_working = (self.debug_stats['gaxi_commands'] > 0)
        gaxi_rsp_working = (self.debug_stats['gaxi_responses'] > 0)
        scoreboard_working = (scoreboard_stats['matched_pairs'] > 0)

        self.log.info("=== REFACTOR DEBUG ANALYSIS ===")
        self.log.info(f"Signal connectivity: {'✓' if signals_ok else '✗'}")
        self.log.info(f"APB transaction flow: {'✓' if apb_flow_working else '✗'}")
        self.log.info(f"GAXI command generation: {'✓' if gaxi_cmd_working else '✗'}")
        self.log.info(f"GAXI response generation: {'✓' if gaxi_rsp_working else '✗'}")
        self.log.info(f"Scoreboard matching: {'✓' if scoreboard_working else '✗'}")

        # Identify likely refactor issues
        if not gaxi_cmd_working:
            self.log.error("🔥 ISSUE: GAXI commands not being generated - check signal mapping in refactor")
        if not gaxi_rsp_working:
            self.log.error("🔥 ISSUE: GAXI responses not being generated - check command handler or RSP master")
        if gaxi_cmd_working and gaxi_rsp_working and not scoreboard_working:
            self.log.error("🔥 ISSUE: GAXI flow works but scoreboard doesn't match - check field formats")

        success = apb_flow_working and gaxi_cmd_working and gaxi_rsp_working and scoreboard_working

        if success:
            self.log.info("✓ APB-GAXI REFACTOR DEBUG TEST PASSED")
        else:
            self.log.error("✗ APB-GAXI REFACTOR DEBUG TEST FAILED - issues identified above")

        return success

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

    async def run_comprehensive_test_suite(self):
        """Run comprehensive test suite with all configurations."""
        self.log.info("=== Starting Comprehensive APB Test Suite ===")

        # Test configuration matrix
        test_matrix = [
            ('fixed', 'fixed', 'Basic Fixed Timing'),
            ('constrained', 'constrained', 'Constrained Random Timing'),
            ('fast', 'fast', 'Fast Timing'),
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

        # # High-throughput stress test
        # await self.run_stress_tests()

        # # Error injection tests
        # await self.run_error_injection_tests()

        # Generate final report
        self.generate_test_report()

    async def run_stress_tests(self):
        """Run stress tests with high transaction volumes."""
        self.log.info("=== Running Stress Tests ===")

        stress_configs = [
            ('high_throughput', 'high_throughput', 'High Throughput Stress'),
            # ('backtoback', 'backtoback', 'Back-to-Back Stress'),
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


@cocotb.test(timeout_time=10, timeout_unit="sec")
async def apb_slave_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for APB slave.

    Generates 7 comprehensive scenarios from the slave perspective:
    1. Basic write transaction
    2. Basic read transaction
    3. Back-to-back writes
    4. Back-to-back reads
    5. Write-to-read transition
    6. Read-to-write transition
    7. Error response (if supported)

    All waveforms include clock and reset signals with APB signals grouped.

    Enable with ENABLE_WAVEDROM=1 environment variable.
    """
    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '0'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled (ENABLE_WAVEDROM=0), skipping wavedrom test")
        return

    # Setup testbench
    tb = APBGAXIDebugTB(dut)
    await tb.start_clock('pclk', 10, 'ns')
    await tb.reset_dut()

    # Setup WaveDrom with comprehensive 7-scenario preset
    field_config = get_apb_field_config(tb.ADDR_WIDTH, tb.DATA_WIDTH)
    wave_generator = create_apb_wavejson_generator(field_config)
    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=field_config
    )
    wave_solver.add_clock_group('default', dut.pclk)

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
    wave_solver.add_interface("apb", apb_signals, field_config=field_config)

    # Use comprehensive preset with all 7 standard APB scenarios
    num_constraints = setup_apb_constraints_with_boundaries(
        wave_solver=wave_solver,
        preset_name="comprehensive",
        max_cycles=30,
        clock_group="default",
        data_width=tb.DATA_WIDTH,
        addr_width=tb.ADDR_WIDTH,
        enable_packet_callbacks=True,
        use_signal_names=True,
        post_match_cycles=3
    )

    dut._log.info(f"WaveDrom configured with {num_constraints} comprehensive APB constraints")

    # Start command handler to generate GAXI responses
    await tb.cmd_handler.start()

    # Start sampling for all scenarios
    await wave_solver.start_sampling()

    # Generate all 7 transaction scenarios
    dut._log.info("=== Generating All APB Slave WaveDrom Scenarios ===")

    # Scenarios 1-2: Basic write and read
    dut._log.info("Generating: Basic write and read")
    await tb.send_apb_transaction(is_write=True, addr=0x1000, data=0xDEADBEEF)
    await tb.wait_clocks('pclk', 5)
    await tb.send_apb_transaction(is_write=False, addr=0x1000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 3: Back-to-back writes
    dut._log.info("Generating: Back-to-back writes")
    await tb.send_apb_transaction(is_write=True, addr=0x2000, data=0xAAAAAAAA)
    await tb.send_apb_transaction(is_write=True, addr=0x2004, data=0xBBBBBBBB)
    await tb.wait_clocks('pclk', 10)

    # Scenario 4: Back-to-back reads
    dut._log.info("Generating: Back-to-back reads")
    await tb.send_apb_transaction(is_write=False, addr=0x3000)
    await tb.send_apb_transaction(is_write=False, addr=0x3004)
    await tb.wait_clocks('pclk', 10)

    # Scenario 5: Write-to-read transition
    dut._log.info("Generating: Write-to-read transition")
    await tb.send_apb_transaction(is_write=True, addr=0x4000, data=0x12345678)
    await tb.send_apb_transaction(is_write=False, addr=0x4000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 6: Read-to-write transition
    dut._log.info("Generating: Read-to-write transition")
    await tb.send_apb_transaction(is_write=False, addr=0x5000)
    await tb.send_apb_transaction(is_write=True, addr=0x5000, data=0x87654321)
    await tb.wait_clocks('pclk', 10)

    # Scenario 7: Error transaction (if supported by slave)
    # Note: Error generation depends on slave configuration
    dut._log.info("Generating: Error scenario (if slave supports)")
    await tb.wait_clocks('pclk', 5)

    # Stop sampling and generate all waveforms
    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    results = wave_solver.get_results()

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
    dut._log.info(f"✅ APB Slave WaveDrom Complete: {len(results['solutions'])} scenarios generated")
    dut._log.info("=" * 80)


@cocotb.test(timeout_time=300, timeout_unit="us")  # Increased timeout for comprehensive tests
async def comprehensive_apb_gaxi_test(dut):
    """Comprehensive APB-GAXI test with all sequences."""

    tb = APBGAXIDebugTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start clock
    await tb.start_clock('pclk', 10, 'ns')

    # Reset DUT
    await tb.reset_dut()

    # Start command handler
    await tb.cmd_handler.start()

    try:

        # Simple refactor debug test
        result = await tb.run_refactor_debug_test()

        if result:
            tb.log.info("🎉 APB-GAXI DEBUG TEST PASSED! 🎉")
        else:
            tb.log.error("❌ APB-GAXI DEBUG TEST FAILED ❌")
            tb.log.error("Check the detailed analysis above to identify refactor issues")
            assert False, "APB-GAXI debug test failed"

        # Run comprehensive test suite
        await tb.run_comprehensive_test_suite()

        # Final verification
        final_result = await tb.verify_scoreboard(timeout=5000)

        if final_result and tb.test_stats['failed_tests'] == 0:
            tb.log.info("🎉 COMPREHENSIVE TEST SUITE PASSED! 🎉")
        else:
            tb.log.error("❌ COMPREHENSIVE TEST SUITE FAILED ❌")
            assert False, f"Test suite failed: {tb.test_stats['failed_tests']} failed tests"

    finally:
        # Clean shutdown
        tb.done = True
        await tb.cmd_handler.stop()
        await tb.wait_clocks('pclk', 10)


@pytest.mark.parametrize("addr_width, data_width, depth", [(32, 32, 2)])
def test_apb_gaxi_refactor_debug(request, addr_width, data_width, depth):
    """APB-GAXI refactor debug test."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba': 'rtl/amba'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"apb/{dut_name}.sv")
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
        'COCOTB_LOG_LEVEL': 'DEBUG',
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

        print(f"✓ APB-GAXI refactor debug test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")

    except Exception as e:
        print(f"❌ APB-GAXI refactor debug test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed refactor issue analysis.")
        raise


# ===============================================================================
# WaveDrom Test
# ===============================================================================

def generate_apb_slave_wavedrom_params():
    """Generate test parameters for APB slave WaveDrom test."""
    return [
        # (addr_width, data_width, depth)
        (32, 32, 2),  # Standard configuration
    ]


wavedrom_params = generate_apb_slave_wavedrom_params()


@pytest.mark.parametrize("addr_width, data_width, depth", wavedrom_params)
def test_apb_slave_wavedrom(request, addr_width, data_width, depth):
    """
    APB slave WaveDrom test - generates timing diagrams.

    Run with: ENABLE_WAVEDROM=1 pytest val/amba/test_apb_slave.py::test_apb_slave_wavedrom -v
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba': 'rtl/amba'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"apb/{dut_name}.sv")
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_apb_slave_aw{aw_str}_dw{dw_str}_d{d_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'DEPTH': depth,
    }

    extra_env = {
        'ENABLE_WAVEDROM': '1',  # ← Enable WaveDrom!
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
            testcase="apb_slave_wavedrom_test",  # ← Run wavedrom test specifically!
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ APB Slave WaveDrom test completed!")
        print(f"Logs: {log_path}")
        print(f"WaveJSON files: val/amba/WaveJSON/test_apb_slave_*.json")

    except Exception as e:
        print(f"❌ APB Slave WaveDrom test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        raise
