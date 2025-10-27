# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBSlaveCDCCGTB
# Purpose: Enhanced APB-GAXI CDC testbench with comprehensive clock gating testing and vali
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

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction, APBPacket
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import create_apb_master, create_apb_monitor
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class APBSlaveCDCCGTB(TBBase):
    """Enhanced APB-GAXI CDC testbench with comprehensive clock gating testing and validation."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.CG_IDLE_COUNT_WIDTH = self.convert_to_int(os.environ.get('TEST_CG_IDLE_COUNT_WIDTH', '4'))
        self.done = False
        self.num_line = 32768  # Large memory for comprehensive testing

        # Enhanced debug tracking with clock gating metrics
        self.debug_stats = {
            'apb_writes': 0,
            'apb_reads': 0,
            'gaxi_commands': 0,
            'gaxi_responses': 0,
            'cmd_handler_responses': 0,
            'signal_checks': {},
            'clock_domain_crossings': 0,
            'aclk_cycles': 0,
            'pclk_cycles': 0,
            # Clock gating specific metrics
            'pclk_gated_cycles': 0,
            'aclk_gated_cycles': 0,
            'pclk_idle_cycles': 0,
            'aclk_idle_cycles': 0,
            'clock_gate_activations': 0,
            'clock_gate_wakeups': 0,
            'power_savings_pclk': 0.0,
            'power_savings_aclk': 0.0
        }

        # Test statistics for comprehensive suite with clock gating
        self.test_stats = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': 0,
            'total_transactions': 0,
            'error_transactions': 0,
            'configurations_tested': set(),
            'cdc_violations': 0,
            'clock_gating_violations': 0,
            'power_efficiency_tests': 0,
            'idle_detection_tests': 0
        }

        # Clock gating test configurations
        max_idle_count = (1 << self.CG_IDLE_COUNT_WIDTH) - 1  # Max value for the bit width
        self.cg_test_configs = [
            {'enable': True, 'idle_count': min(2, max_idle_count), 'name': 'aggressive'},
            {'enable': True, 'idle_count': min(4, max_idle_count), 'name': 'moderate'},
            {'enable': True, 'idle_count': min(8, max_idle_count), 'name': 'conservative'},
            {'enable': True, 'idle_count': max_idle_count, 'name': 'very_conservative'},  # Use max possible
            {'enable': False, 'idle_count': 0, 'name': 'disabled'}
        ]

        # Initialize components with CDC and clock gating support
        self._init_cdc_cg_components_with_debug()

    def _init_cdc_cg_components_with_debug(self):
        """Initialize CDC components with clock gating controllers and enhanced debugging."""
        self.log.info("=== APB-GAXI CDC + Clock Gating: Component initialization ===")

        # Memory model - larger for comprehensive testing
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)
        self.log.info(f"✓ Memory model created: {self.num_line} lines x {self.STRB_WIDTH} bytes")
        self.log.info(f"Clock gating parameters: CG_IDLE_COUNT_WIDTH={self.CG_IDLE_COUNT_WIDTH}, max_idle_count={(1 << self.CG_IDLE_COUNT_WIDTH) - 1}")

        # Log the actual test configurations being used
        for config in self.cg_test_configs:
            self.log.info(f"Clock gating config: {config['name']} - enable={config['enable']}, idle_count={config['idle_count']}")

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

        self.log.info(f"✓ Field configs created for CDC + Clock Gating operation")

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
        # CDC: Uses aclk (faster clock) for response generation
        try:
            self.rsp_monitor = create_gaxi_monitor(
                self.dut, 'RSP Monitor', '', self.dut.aclk,  # CDC: aclk domain
                field_config=self.rsp_field_config,
                pkt_prefix='rsp', is_slave=False,
                log=self.log, super_debug=super_debug, multi_sig=True
            )
            self.log.info("✓ RSP Monitor created (aclk domain)")

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
            self.log.info("✓ RSP Master created (aclk domain)")

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

        # Clock gating controllers for both domains
        self._init_clock_gating_controllers()

        # Enhanced scoreboard for CDC testing
        self.apb_gaxi_scoreboard = APBGAXIScoreboard('CDC + Clock Gating Scoreboard', log=self.log)
        self.log.info("✓ Enhanced Scoreboard created")

        # Connect callbacks with CDC-aware debugging
        self.log.info("Connecting CDC + Clock Gating aware callbacks...")

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
            self.log.info("✓ RSP Monitor callback connected (aclk domain)")
        except Exception as e:
            self.log.error(f"✗ RSP Monitor callback failed: {e}")

        self.log.info("=== APB-GAXI CDC + Clock Gating: Component initialization complete ===")

    def _init_clock_gating_controllers(self):
        """Initialize clock gating controllers for both PCLK and ACLK domains."""
        try:
            # PCLK domain clock gating controller
            self.pclk_cg_ctrl = AxiClockGateCtrl(
                self.dut,
                instance_path="",  # Top level since signals are at DUT level
                clock_signal_name="pclk",
                user_valid_signals=["s_apb_PSEL", "w_rsp_valid"],
                axi_valid_signals=["w_cmd_valid"],
                gating_signal_name="pclk_cg_gating",
                idle_signal_name="pclk_cg_idle",
                enable_signal_name="cfg_cg_enable",
                idle_count_signal_name="cfg_cg_idle_count"
            )
            self.log.info("✓ PCLK Clock Gating Controller created")

            # ACLK domain clock gating controller  
            self.aclk_cg_ctrl = AxiClockGateCtrl(
                self.dut,
                instance_path="",  # Top level since signals are at DUT level
                clock_signal_name="aclk",
                user_valid_signals=["rsp_valid"],
                axi_valid_signals=["cmd_valid", "cmd_ready"],
                gating_signal_name="aclk_cg_gating",
                idle_signal_name="aclk_cg_idle",
                enable_signal_name="cfg_cg_enable",    # Shared config
                idle_count_signal_name="cfg_cg_idle_count"  # Shared config
            )
            self.log.info("✓ ACLK Clock Gating Controller created")

        except Exception as e:
            self.log.error(f"✗ Clock Gating Controller creation failed: {e}")
            raise

    def debug_apb_callback(self, transaction):
        """CDC + Clock Gating aware APB transaction callback with cross-domain tracking."""
        try:
            pwrite = getattr(transaction, 'pwrite', None)
            paddr = getattr(transaction, 'paddr', None)

            # Track clock domain crossing
            self.debug_stats['clock_domain_crossings'] += 1

            # Check if transaction occurred during clock gating
            pclk_state = self.pclk_cg_ctrl.get_current_state()
            aclk_state = self.aclk_cg_ctrl.get_current_state()
            pclk_gated = pclk_state.get('is_gated', False)
            aclk_gated = aclk_state.get('is_gated', False)
            
            if pwrite == 1:
                self.debug_stats['apb_writes'] += 1
                pwdata = getattr(transaction, 'pwdata', None)
                pstrb = getattr(transaction, 'pstrb', None)
                gated_str = f" [PCLK:{pclk_gated}, ACLK:{aclk_gated}]"
                self.log.info(f"🔵 APB WRITE #{self.debug_stats['apb_writes']} (pclk→aclk): "
                                f"addr=0x{paddr:X}, data=0x{pwdata:X}, strb=0x{pstrb:X}{gated_str}")
            elif pwrite == 0:
                self.debug_stats['apb_reads'] += 1
                prdata = getattr(transaction, 'prdata', None)
                pslverr = getattr(transaction, 'pslverr', None)
                gated_str = f" [PCLK:{pclk_gated}, ACLK:{aclk_gated}]"
                self.log.info(f"🔵 APB READ #{self.debug_stats['apb_reads']} (pclk→aclk): "
                                f"addr=0x{paddr:X}, data=0x{prdata:X}, err={pslverr}{gated_str}")
            else:
                self.log.error(f"🔴 APB UNKNOWN: pwrite={pwrite}")

            # Detect potential clock gating violations
            if pclk_gated or aclk_gated:
                self.test_stats['clock_gating_violations'] += 1
                self.log.warning(f"⚠️ APB transaction during gating - PCLK:{pclk_gated}, ACLK:{aclk_gated}")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_apb_transaction(transaction)
            self.log.debug("✓ APB transaction added to CDC + Clock Gating scoreboard")

        except Exception as e:
            self.log.error(f"🔴 APB CDC + Clock Gating callback error: {e}")

    def debug_cmd_callback(self, transaction):
        """CDC + Clock Gating aware GAXI command callback with aclk domain tracking."""
        try:
            self.debug_stats['gaxi_commands'] += 1
            self.debug_stats['aclk_cycles'] += 1

            # Check if transaction occurred during clock gating
            aclk_state = self.aclk_cg_ctrl.get_current_state()
            aclk_gated = aclk_state.get('is_gated', False)

            # Handle both field storage methods
            if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
                fields = transaction.fields
                pwrite = fields.get('pwrite', 'N/A')
                paddr = fields.get('paddr', 'N/A')
                pwdata = fields.get('pwdata', 'N/A')
            else:
                pwrite = getattr(transaction, 'pwrite', 'N/A')
                paddr = getattr(transaction, 'paddr', 'N/A')
                pwdata = getattr(transaction, 'pwdata', 'N/A')

            gated_str = " [DURING GATING]" if aclk_gated else ""
            self.log.info(f"🟢 GAXI CMD #{self.debug_stats['gaxi_commands']} (aclk): "
                            f"pwrite={pwrite}, addr=0x{paddr:X}, data=0x{pwdata:X}{gated_str}")

            # Detect potential clock gating violations
            if aclk_gated:
                self.test_stats['clock_gating_violations'] += 1
                self.log.warning(f"⚠️ GAXI CMD transaction during ACLK gating - potential violation!")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)
            self.log.debug("✓ GAXI CMD transaction added to CDC + Clock Gating scoreboard")

        except Exception as e:
            self.log.error(f"🔴 GAXI CMD CDC + Clock Gating callback error: {e}")

    def debug_rsp_callback(self, transaction):
        """CDC + Clock Gating aware GAXI response callback with aclk domain tracking."""
        try:
            self.debug_stats['gaxi_responses'] += 1
            self.debug_stats['aclk_cycles'] += 1

            # Check if transaction occurred during clock gating
            aclk_state = self.aclk_cg_ctrl.get_current_state()
            aclk_gated = aclk_state.get('is_gated', False)

            # Handle both field storage methods
            if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
                fields = transaction.fields
                prdata = fields.get('prdata', 'N/A')
                pslverr = fields.get('pslverr', 'N/A')
            else:
                prdata = getattr(transaction, 'prdata', 'N/A')
                pslverr = getattr(transaction, 'pslverr', 'N/A')

            gated_str = " [DURING GATING]" if aclk_gated else ""
            self.log.info(f"🟡 GAXI RSP #{self.debug_stats['gaxi_responses']} (aclk→pclk): "
                            f"data=0x{prdata:X}, err={pslverr}{gated_str}")

            # Detect potential clock gating violations
            if aclk_gated:
                self.test_stats['clock_gating_violations'] += 1
                self.log.warning(f"⚠️ GAXI RSP transaction during ACLK gating - potential violation!")

            # Add to scoreboard
            self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)
            self.log.debug("✓ GAXI RSP transaction added to CDC + Clock Gating scoreboard")

        except Exception as e:
            self.log.error(f"🔴 GAXI RSP CDC + Clock Gating callback error: {e}")

    async def reset_dut(self):
        """Enhanced CDC reset with separate clock domain handling and clock gating reset."""
        self.log.info('=== APB-GAXI CDC + Clock Gating: Starting reset ===')

        # CDC Reset: Both clock domains need reset
        self.dut.aresetn.value = 0  # AXI clock domain (aclk)
        self.dut.presetn.value = 0  # APB clock domain (pclk)

        # Initialize clock gating configuration to disabled during reset
        self.dut.cfg_cg_enable.value = 0
        self.dut.cfg_cg_idle_count.value = 0

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
        self.debug_stats = {k: 0 if isinstance(v, int) else {} if isinstance(v, dict) else 0.0 for k, v in self.debug_stats.items()}
        self.apb_gaxi_scoreboard.clear()

        self.log.info('=== APB-GAXI CDC + Clock Gating: Reset complete ===')

    async def configure_clock_gating(self, enable=True, idle_count=4):
        """Configure clock gating parameters for both domains."""
        # Clamp idle_count to the maximum supported by the signal width
        max_idle_count = (1 << self.CG_IDLE_COUNT_WIDTH) - 1
        if idle_count > max_idle_count:
            self.log.warning(f"Idle count {idle_count} exceeds maximum {max_idle_count} for {self.CG_IDLE_COUNT_WIDTH}-bit signal, clamping")
            idle_count = max_idle_count

        self.log.info(f"=== Configuring Clock Gating: enable={enable}, idle_count={idle_count} (max={max_idle_count}) ===")

        # Configure through DUT signals
        self.dut.cfg_cg_enable.value = 1 if enable else 0
        self.dut.cfg_cg_idle_count.value = idle_count

        # Configure through individual clock gating controllers
        self.pclk_cg_ctrl.enable_clock_gating(enable)
        self.pclk_cg_ctrl.set_idle_count(idle_count)
        
        self.aclk_cg_ctrl.enable_clock_gating(enable)
        self.aclk_cg_ctrl.set_idle_count(idle_count)

        # Allow configuration to take effect
        await self.wait_clocks('aclk', 5)
        await self.wait_clocks('pclk', 5)

        self.log.info(f"✓ Clock gating configured: enable={enable}, idle_count={idle_count}")

    async def check_cdc_cg_signal_connectivity(self):
        """Check signal connectivity for CDC + Clock Gating specific signals."""
        self.log.info("=== CHECKING CDC + CLOCK GATING SIGNAL CONNECTIVITY ===")

        signal_checks = {}

        # Check basic CDC signals (from parent class)
        # APB signals (pclk domain)
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
            try:
                signal_obj = getattr(self.dut, sig)
                signal_checks[f"{sig} (aclk)"] = '✓ accessible'
                self.log.debug(f"✓ {sig} accessible in aclk domain")
            except AttributeError:
                signal_checks[f"{sig} (aclk)"] = '✗ missing'
                self.log.debug(f"✗ {sig} not found in aclk domain")

        # Check GAXI response signals (aclk domain)
        rsp_signals = ['rsp_valid', 'rsp_ready', 'rsp_prdata', 'rsp_pslverr']
        for sig in rsp_signals:
            try:
                signal_obj = getattr(self.dut, sig)
                signal_checks[f"{sig} (aclk)"] = '✓ accessible'
                self.log.debug(f"✓ {sig} accessible in aclk domain")
            except AttributeError:
                signal_checks[f"{sig} (aclk)"] = '✗ missing'
                self.log.debug(f"✗ {sig} not found in aclk domain")

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

        # Check Clock Gating specific signals
        cg_signals = [
            'cfg_cg_enable', 'cfg_cg_idle_count', 
            'pclk_cg_gating', 'pclk_cg_idle',
            'aclk_cg_gating', 'aclk_cg_idle'
        ]
        for sig in cg_signals:
            try:
                signal_obj = getattr(self.dut, sig)
                signal_checks[f"{sig} (CG)"] = '✓ accessible'
                self.log.debug(f"✓ {sig} Clock Gating signal accessible")
            except AttributeError:
                signal_checks[f"{sig} (CG)"] = '✗ missing'
                self.log.warning(f"✗ {sig} Clock Gating signal not found")

        self.debug_stats['signal_checks'] = signal_checks

        # Summary
        accessible_count = sum(1 for status in signal_checks.values() if '✓' in status)
        total_count = len(signal_checks)
        self.log.info(f"CDC + Clock Gating Signal connectivity: {accessible_count}/{total_count} signals accessible")

        if accessible_count < total_count:
            self.log.warning("Some CDC + Clock Gating signals missing - check clock domain assignments")
            for sig, status in signal_checks.items():
                if '✗' in status:
                    self.log.warning(f"  Missing: {sig}")

        return accessible_count >= len(apb_signals) + len(cdc_signals) + len(cg_signals)  # Core signals should work

    async def monitor_clock_gating_activity(self, duration=1000, units='ns'):
        """Monitor clock gating activity for both domains."""
        self.log.info(f"=== Monitoring Clock Gating Activity for {duration} {units} ===")

        # Monitor both domains simultaneously
        pclk_stats = await self.pclk_cg_ctrl.monitor_activity(duration, units)
        aclk_stats = await self.aclk_cg_ctrl.monitor_activity(duration, units)

        # Update debug stats
        self.debug_stats['pclk_gated_cycles'] += pclk_stats.get('gated_cycles', 0)
        self.debug_stats['aclk_gated_cycles'] += aclk_stats.get('gated_cycles', 0)
        self.debug_stats['power_savings_pclk'] = pclk_stats.get('gated_percent', 0.0)
        self.debug_stats['power_savings_aclk'] = aclk_stats.get('gated_percent', 0.0)

        self.log.info(f"PCLK Domain: {pclk_stats['active_percent']:.1f}% active, {pclk_stats['gated_percent']:.1f}% gated")
        self.log.info(f"ACLK Domain: {aclk_stats['active_percent']:.1f}% active, {aclk_stats['gated_percent']:.1f}% gated")

        return {'pclk': pclk_stats, 'aclk': aclk_stats}

    async def test_clock_gating_idle_detection(self):
        """Test that clock gating properly detects idle conditions."""
        self.log.info("=== Testing Clock Gating Idle Detection ===")

        # Configure aggressive clock gating
        await self.configure_clock_gating(enable=True, idle_count=2)

        # Send a single transaction to create activity
        await self.send_apb_write_read_pair(0x1000, 0x12345678)

        # Wait for idle detection
        pclk_idle = await self.pclk_cg_ctrl.wait_for_idle(timeout=500, units='ns')
        aclk_idle = await self.aclk_cg_ctrl.wait_for_idle(timeout=500, units='ns')

        # Wait for gating activation
        pclk_gated = await self.pclk_cg_ctrl.wait_for_gating(timeout=500, units='ns')
        aclk_gated = await self.aclk_cg_ctrl.wait_for_gating(timeout=500, units='ns')

        idle_success = pclk_idle and aclk_idle
        gating_success = pclk_gated and aclk_gated

        self.test_stats['idle_detection_tests'] += 1

        if idle_success and gating_success:
            self.log.info("✓ Clock gating idle detection test PASSED")
            return True
        else:
            self.log.error(f"✗ Clock gating idle detection test FAILED: idle={idle_success}, gating={gating_success}")
            return False

    async def test_clock_gating_wakeup(self):
        """Test that clock gating properly wakes up from gated state."""
        self.log.info("=== Testing Clock Gating Wakeup ===")

        # Configure aggressive clock gating and wait for gating
        await self.configure_clock_gating(enable=True, idle_count=2)
        await self.wait_clocks('pclk', 20)  # Allow gating to activate

        # Force wakeup by asserting valid signals
        original_values = self.pclk_cg_ctrl.force_wakeup()
        
        # Wait a few cycles
        await self.wait_clocks('pclk', 5)
        
        # Check if clocks are active
        pclk_state = self.pclk_cg_ctrl.get_current_state()
        aclk_state = self.aclk_cg_ctrl.get_current_state()
        
        # Restore signals
        self.pclk_cg_ctrl.restore_signals(original_values)

        wakeup_success = not pclk_state['is_gated'] and not aclk_state['is_gated']

        if wakeup_success:
            self.debug_stats['clock_gate_wakeups'] += 1
            self.log.info("✓ Clock gating wakeup test PASSED")
            return True
        else:
            self.log.error("✗ Clock gating wakeup test FAILED")
            return False

    async def test_power_efficiency(self, cg_config):
        """Test power efficiency with different clock gating configurations."""
        self.log.info(f"=== Testing Power Efficiency: {cg_config['name']} ===")

        # Configure clock gating
        await self.configure_clock_gating(
            enable=cg_config['enable'], 
            idle_count=cg_config['idle_count']
        )

        # Run a typical workload
        initial_stats = self.debug_stats.copy()
        
        # Send sparse transactions to allow gating opportunities
        for i in range(5):
            await self.send_apb_write_read_pair(0x2000 + i*4, 0x20000 + i)
            # Long delay between transactions to allow gating
            await self.wait_clocks('pclk', 50)
            await self.wait_clocks('aclk', 25)

        # Monitor gating activity
        cg_stats = await self.monitor_clock_gating_activity(1000, 'ns')

        # Calculate power savings
        power_savings = {
            'pclk': cg_stats['pclk']['gated_percent'],
            'aclk': cg_stats['aclk']['gated_percent']
        }

        self.test_stats['power_efficiency_tests'] += 1

        expected_savings = 30.0 if cg_config['enable'] else 0.0
        efficiency_pass = (power_savings['pclk'] >= expected_savings or 
                          power_savings['aclk'] >= expected_savings or
                          not cg_config['enable'])

        if efficiency_pass:
            self.log.info(f"✓ Power efficiency test PASSED: {cg_config['name']} - "
                         f"PCLK: {power_savings['pclk']:.1f}%, ACLK: {power_savings['aclk']:.1f}%")
            return True
        else:
            self.log.error(f"✗ Power efficiency test FAILED: {cg_config['name']} - "
                          f"PCLK: {power_savings['pclk']:.1f}%, ACLK: {power_savings['aclk']:.1f}%")
            return False

    async def run_cdc_cg_comprehensive_test(self):
        """Run comprehensive CDC + Clock Gating test with cross-domain validation."""
        self.log.info("=== STARTING APB-GAXI CDC + CLOCK GATING COMPREHENSIVE TEST ===")

        # Step 1: Check CDC + Clock Gating signal connectivity
        signals_ok = await self.check_cdc_cg_signal_connectivity()

        # Step 2: Start command handler (critical for response generation)
        self.log.info("Starting CDC + Clock Gating command handler...")
        try:
            await self.cmd_handler.start()
            handler_stats = self.cmd_handler.get_stats()
            self.log.info(f"✓ CDC + Clock Gating Command handler started: {handler_stats}")
        except Exception as e:
            self.log.error(f"✗ CDC + Clock Gating Command handler start failed: {e}")
            return False

        # Step 3: Test basic functionality with clock gating disabled
        self.log.info("Testing basic CDC functionality with clock gating disabled...")
        await self.configure_clock_gating(enable=False, idle_count=0)
        
        # Wait for CDC stabilization
        await self.wait_clocks('aclk', 15)
        await self.wait_clocks('pclk', 15)

        # Test the full APB->GAXI->APB flow across clock domains
        test_addr = 0x1000
        test_data = 0x12345678

        initial_stats = self.debug_stats.copy()
        await self.send_apb_write_read_pair(test_addr, test_data)

        # Step 4: Test with different clock gating configurations
        cg_test_results = []
        for cg_config in self.cg_test_configs:
            self.log.info(f"Testing clock gating configuration: {cg_config['name']}")
            
            # Test power efficiency
            power_result = await self.test_power_efficiency(cg_config)
            cg_test_results.append(power_result)
            
            # Reset for next test
            await self.wait_clocks('aclk', 20)
            await self.wait_clocks('pclk', 20)

        # Step 5: Test idle detection and wakeup
        idle_result = await self.test_clock_gating_idle_detection()
        wakeup_result = await self.test_clock_gating_wakeup()

        # Step 6: Check what happened across clock domains
        self.log.info("=== CDC + CLOCK GATING FLOW ANALYSIS ===")
        self.log.info(f"APB Writes: {initial_stats['apb_writes']} → {self.debug_stats['apb_writes']}")
        self.log.info(f"APB Reads: {initial_stats['apb_reads']} → {self.debug_stats['apb_reads']}")
        self.log.info(f"GAXI Commands (aclk): {initial_stats['gaxi_commands']} → {self.debug_stats['gaxi_commands']}")
        self.log.info(f"GAXI Responses (aclk): {initial_stats['gaxi_responses']} → {self.debug_stats['gaxi_responses']}")
        self.log.info(f"Clock Domain Crossings: {self.debug_stats['clock_domain_crossings']}")
        self.log.info(f"Clock Gating Violations: {self.test_stats['clock_gating_violations']}")
        self.log.info(f"PCLK Gated Cycles: {self.debug_stats['pclk_gated_cycles']}")
        self.log.info(f"ACLK Gated Cycles: {self.debug_stats['aclk_gated_cycles']}")

        # Step 7: Command handler analysis
        handler_stats = self.cmd_handler.get_stats()
        self.log.info(f"CDC + Clock Gating Command Handler Stats: {handler_stats}")

        # Step 8: Scoreboard analysis with CDC timing
        await self.wait_clocks('aclk', 25)  # Allow final aclk processing
        await self.wait_clocks('pclk', 25)  # Allow final pclk processing
        scoreboard_stats = self.apb_gaxi_scoreboard.get_stats()
        self.log.info(f"CDC + Clock Gating Scoreboard Stats: {scoreboard_stats}")

        # Step 9: Determine success criteria
        apb_flow_working = (self.debug_stats['apb_writes'] > 0 and self.debug_stats['apb_reads'] > 0)
        gaxi_cmd_working = (self.debug_stats['gaxi_commands'] > 0)
        gaxi_rsp_working = (self.debug_stats['gaxi_responses'] > 0)
        scoreboard_working = (scoreboard_stats['matched_pairs'] > 0)
        cdc_working = (self.debug_stats['clock_domain_crossings'] > 0)
        clock_gating_working = (sum(cg_test_results) >= len(cg_test_results) // 2)  # At least half should pass
        no_cg_violations = (self.test_stats['clock_gating_violations'] == 0)

        self.log.info("=== CDC + CLOCK GATING COMPREHENSIVE ANALYSIS ===")
        self.log.info(f"Signal connectivity: {'✓' if signals_ok else '✗'}")
        self.log.info(f"APB transaction flow (pclk): {'✓' if apb_flow_working else '✗'}")
        self.log.info(f"GAXI command generation (aclk): {'✓' if gaxi_cmd_working else '✗'}")
        self.log.info(f"GAXI response generation (aclk): {'✓' if gaxi_rsp_working else '✗'}")
        self.log.info(f"CDC clock domain crossing: {'✓' if cdc_working else '✗'}")
        self.log.info(f"Clock gating functionality: {'✓' if clock_gating_working else '✗'}")
        self.log.info(f"Clock gating violations: {'✓' if no_cg_violations else '✗'}")
        self.log.info(f"Idle detection: {'✓' if idle_result else '✗'}")
        self.log.info(f"Wakeup mechanism: {'✓' if wakeup_result else '✗'}")
        self.log.info(f"Scoreboard matching: {'✓' if scoreboard_working else '✗'}")

        # CDC + Clock Gating specific issue identification
        if not gaxi_cmd_working:
            self.log.error("🔥 CDC ISSUE: GAXI commands not crossing pclk→aclk - check CDC handshake")
        if not gaxi_rsp_working:
            self.log.error("🔥 CDC ISSUE: GAXI responses not crossing aclk→pclk - check CDC response path")
        if not cdc_working:
            self.log.error("🔥 CDC ISSUE: No clock domain crossings detected - check CDC implementation")
        if not clock_gating_working:
            self.log.error("🔥 CLOCK GATING ISSUE: Clock gating not functioning properly")
        if not no_cg_violations:
            self.log.error("🔥 CLOCK GATING VIOLATION: Transactions detected during gating")
        if not idle_result:
            self.log.error("🔥 CLOCK GATING ISSUE: Idle detection not working")
        if not wakeup_result:
            self.log.error("🔥 CLOCK GATING ISSUE: Wakeup mechanism not working")

        success = (apb_flow_working and gaxi_cmd_working and gaxi_rsp_working and 
                  scoreboard_working and cdc_working and clock_gating_working and 
                  no_cg_violations and idle_result and wakeup_result)

        if success:
            self.log.info("✓ APB-GAXI CDC + CLOCK GATING COMPREHENSIVE TEST PASSED")
        else:
            self.log.error("✗ APB-GAXI CDC + CLOCK GATING COMPREHENSIVE TEST FAILED - Issues identified above")

        return success

    # Inherit and extend methods from parent class
    async def wait_for_queue_empty(self, obj, timeout=5000):
        """Enhanced queue empty waiting with CDC + Clock Gating awareness."""
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
            # For CDC + Clock Gating, wait on the appropriate clock domain
            if 'RSP' in obj.title:
                await self.wait_clocks('aclk', 1)  # Response components use aclk
            else:
                await self.wait_clocks('pclk', 1)  # APB components use pclk
            cycle_count += 1

            if cycle_count % 20 == 0:
                self.log.debug(f"{obj.__class__.__name__} queue: {len(queue)} items after {cycle_count} cycles")

            if get_sim_time('ns') - start_time > timeout:
                self.log.error(f"TIMEOUT: {obj.__class__.__name__} queue still has {len(queue)} items")
                break

    async def send_apb_write_read_pair(self, addr, data):
        """Enhanced write-read pair with CDC + Clock Gating timing considerations."""
        self.log.info(f"=== CDC + CLOCK GATING TESTING WRITE-READ PAIR: addr=0x{addr:X}, data=0x{data:X} ===")

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

        # CDC + Clock Gating: Extra wait for cross-domain synchronization and potential ungating
        await self.wait_clocks('aclk', 15)  # Allow command processing and potential ungating
        await self.wait_clocks('pclk', 15)  # Allow response generation and potential ungating

        # Send read
        self.log.info("Sending READ (pclk domain)...")
        read_transaction = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)
        read_packet = read_transaction.next()
        read_packet.pwrite = 0
        read_packet.paddr = addr
        read_packet.direction = "READ"

        await self.apb_master.send(read_packet)
        await self.wait_for_queue_empty(self.apb_master)

        # CDC + Clock Gating: Extra wait for cross-domain synchronization and potential ungating
        await self.wait_clocks('aclk', 15)  # Allow command processing and potential ungating
        await self.wait_clocks('pclk', 15)  # Allow response generation and potential ungating

        self.log.info("=== CDC + CLOCK GATING WRITE-READ PAIR COMPLETE ===")

    def create_cg_test_sequences(self):
        """Create test sequences optimized for clock gating validation."""
        sequences = {}

        # Sparse sequence - good for testing clock gating activation
        sequences['sparse_for_gating'] = APBSequence(
            name="sparse_for_gating",
            pwrite_seq=[True, False] * 3,
            addr_seq=[0x1000 + i*4 for i in range(6)],
            data_seq=[0x1000 + i for i in range(6)],
            strb_seq=[0xF] * 6,
            inter_cycle_delays=[50] * 6  # Large delays to trigger gating
        )

        # Burst sequence - should keep clocks active
        sequences['burst_no_gating'] = APBSequence(
            name="burst_no_gating",
            pwrite_seq=[True, False] * 5,
            addr_seq=[0x2000 + i*4 for i in range(10)],
            data_seq=[0x2000 + i for i in range(10)],
            strb_seq=[0xF] * 10,
            inter_cycle_delays=[1] * 10  # Minimal delays - no gating
        )

        # Mixed sequence - alternate between gating opportunities and activity
        sequences['mixed_gating'] = APBSequence(
            name="mixed_gating",
            pwrite_seq=[True, False] * 4,
            addr_seq=[0x3000 + i*4 for i in range(8)],
            data_seq=[0x3000 + i for i in range(8)],
            strb_seq=[0xF] * 8,
            inter_cycle_delays=[1, 1, 30, 30, 1, 1, 50, 50]  # Mixed delays
        )

        return sequences

    async def run_comprehensive_cdc_cg_test_suite(self):
        """Run comprehensive CDC + Clock Gating test suite with all configurations."""
        self.log.info("=== Starting Comprehensive CDC + Clock Gating APB Test Suite ===")

        # CDC + Clock Gating specific test configuration matrix
        test_matrix = [
            ('fixed', 'fixed', 'CDC + CG Basic Fixed Timing'),
            ('constrained', 'constrained', 'CDC + CG Constrained Random Timing'),
            ('fast', 'fast', 'CDC + CG Fast Timing'),
            ('backtoback', 'backtoback', 'Back-to-Back with Clock Gating'),
        ]

        # Create clock gating optimized test sequences
        cg_sequences = self.create_cg_test_sequences()
        
        # Combine with regular sequences
        test_sequences = [
            ('sparse_for_gating', lambda: cg_sequences['sparse_for_gating']),
            ('burst_no_gating', lambda: cg_sequences['burst_no_gating']),
            ('mixed_gating', lambda: cg_sequences['mixed_gating']),
        ]

        total_test_combinations = len(test_matrix) * len(test_sequences) * len(self.cg_test_configs)
        current_test = 0

        for apb_config, axi_config, config_desc in test_matrix:
            for cg_config in self.cg_test_configs:
                for seq_name, seq_generator in test_sequences:
                    current_test += 1
                    test_name = f"{config_desc} - {seq_name} - CG:{cg_config['name']}"
                    self.log.info(f"=== CDC + CG Test {current_test}/{total_test_combinations}: {test_name} ===")

                    try:
                        # Set APB/AXI configuration
                        self.set_randomizer_config(
                            apb_master_config=APB_MASTER_RANDOMIZER_CONFIGS[apb_config],
                            axi_config=AXI_RANDOMIZER_CONFIGS[axi_config]
                        )

                        # Set clock gating configuration
                        await self.configure_clock_gating(
                            enable=cg_config['enable'],
                            idle_count=cg_config['idle_count']
                        )

                        # Generate and run sequence
                        sequence = seq_generator()
                        await self.run_test_sequence(sequence)

                        # Monitor clock gating during test
                        cg_stats = await self.monitor_clock_gating_activity(500, 'ns')

                        # Verify results with CDC + Clock Gating timing
                        result = await self.verify_scoreboard(timeout=5000)

                        if result:
                            self.log.info(f"✓ CDC + CG Test {current_test} PASSED: {test_name}")
                        else:
                            self.log.error(f"✗ CDC + CG Test {current_test} FAILED: {test_name}")

                        # Allow CDC + Clock Gating settling time between tests
                        await self.wait_clocks('aclk', 30)
                        await self.wait_clocks('pclk', 30)

                        self.test_stats['total_tests'] += 1

                    except Exception as e:
                        self.log.error(f"✗ CDC + CG Test {current_test} EXCEPTION: {test_name}: {e}")
                        self.test_stats['failed_tests'] += 1
                        continue

        # Generate final report
        self.generate_cdc_cg_test_report()

    def generate_cdc_cg_test_report(self):
        """Generate comprehensive CDC + Clock Gating test report."""
        self.log.info("=== COMPREHENSIVE CDC + CLOCK GATING TEST REPORT ===")
        self.log.info(f"Total Tests: {self.test_stats['total_tests']}")
        self.log.info(f"Passed Tests: {self.test_stats['passed_tests']}")
        self.log.info(f"Failed Tests: {self.test_stats['failed_tests']}")
        self.log.info(f"Total Transactions: {self.test_stats['total_transactions']}")
        self.log.info(f"Error Transactions: {self.test_stats['error_transactions']}")
        self.log.info(f"CDC Violations: {self.test_stats['cdc_violations']}")
        self.log.info(f"Clock Gating Violations: {self.test_stats['clock_gating_violations']}")
        self.log.info(f"Clock Domain Crossings: {self.debug_stats['clock_domain_crossings']}")

        # Clock Gating specific metrics
        self.log.info(f"PCLK Gated Cycles: {self.debug_stats['pclk_gated_cycles']}")
        self.log.info(f"ACLK Gated Cycles: {self.debug_stats['aclk_gated_cycles']}")
        self.log.info(f"PCLK Power Savings: {self.debug_stats['power_savings_pclk']:.1f}%")
        self.log.info(f"ACLK Power Savings: {self.debug_stats['power_savings_aclk']:.1f}%")
        self.log.info(f"Clock Gate Activations: {self.debug_stats['clock_gate_activations']}")
        self.log.info(f"Clock Gate Wakeups: {self.debug_stats['clock_gate_wakeups']}")
        self.log.info(f"Power Efficiency Tests: {self.test_stats['power_efficiency_tests']}")
        self.log.info(f"Idle Detection Tests: {self.test_stats['idle_detection_tests']}")

        if self.test_stats['total_tests'] > 0:
            pass_rate = (self.test_stats['passed_tests'] / self.test_stats['total_tests']) * 100
            self.log.info(f"CDC + Clock Gating Pass Rate: {pass_rate:.1f}%")

        self.log.info(f"Configurations Tested: {len(self.test_stats['configurations_tested'])}")
        for config in sorted(self.test_stats['configurations_tested']):
            self.log.info(f"  - {config}")

        self.log.info("=== END CDC + CLOCK GATING TEST REPORT ===")

    # Inherit other methods from parent class and adapt as needed
    def set_randomizer_config(self, apb_master_config=None, apb_slave_config=None, axi_config=None):
        """Set randomizer configurations for all components with CDC + Clock Gating awareness."""
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
        """Run a test sequence with CDC + Clock Gating aware timing."""
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

                # CDC + Clock Gating: Add extra delays for cross-domain synchronization and gating opportunities
                if i < num_transactions - 1:
                    delay = sequence_config.next_delay()
                    if delay > 0:
                        await self.wait_clocks('pclk', delay)
                        await self.wait_clocks('aclk', delay // 2)  # Some aclk cycles too

        except Exception as e:
            self.log.error(f"CDC + Clock Gating test sequence failed: {e}")
            self.test_stats['failed_tests'] += 1
            raise

        return results

    async def send_apb_transaction(self, is_write, addr, data=None, strobe=None):
        """Send APB transaction with CDC + Clock Gating aware timing."""
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
        await self.wait_for_queue_empty(self.apb_master, timeout=15000)

        # CDC + Clock Gating: Wait for cross-domain processing and potential ungating
        await self.wait_clocks('aclk', 10)  # Command processing and potential ungating
        await self.wait_clocks('pclk', 10)  # Response processing and potential ungating

        return xmit_transaction

    async def verify_scoreboard(self, timeout=3000):
        """Verify scoreboard with CDC + Clock Gating aware timing."""
        # CDC + Clock Gating: Longer timeout for cross-domain synchronization and ungating
        result = await self.apb_gaxi_scoreboard.check_scoreboard(timeout)

        if result:
            self.test_stats['passed_tests'] += 1
            self.log.info("CDC + Clock Gating Scoreboard verification passed")
        else:
            self.test_stats['failed_tests'] += 1
            self.log.error("CDC + Clock Gating Scoreboard verification failed")

        return result


@cocotb.test(timeout_time=90, timeout_unit="ms")  # Longer timeout for clock gating tests
async def comprehensive_apb_cdc_cg_test(dut):
    """Comprehensive APB-GAXI CDC + Clock Gating test with cross-domain and power validation."""

    tb = APBSlaveCDCCGTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using CDC + Clock Gating test seed: {seed}")

    # Start both clocks for CDC testing
    await tb.start_clock('aclk',  1, 'ns')  # Fast AXI clock - 1GHz
    await tb.start_clock('pclk', 10, 'ns')  # Slower APB clock - 100MHz

    # Reset DUT with CDC + Clock Gating specific reset sequence
    await tb.reset_dut()

    # Start command handler
    await tb.cmd_handler.start()

    try:
        # First run the basic CDC + Clock Gating comprehensive test
        result = await tb.run_cdc_cg_comprehensive_test()

        if result:
            tb.log.info("🎉 APB-GAXI CDC + CLOCK GATING BASIC TEST PASSED! 🎉")
        else:
            tb.log.error("❌ APB-GAXI CDC + CLOCK GATING BASIC TEST FAILED ❌")
            tb.log.error("Check the detailed CDC + Clock Gating analysis above to identify issues")
            assert False, "APB-GAXI CDC + Clock Gating basic test failed"

        # Run comprehensive test suite
        await tb.run_comprehensive_cdc_cg_test_suite()

        # Final verification with CDC + Clock Gating timing
        final_result = await tb.verify_scoreboard(timeout=8000)

        if final_result and tb.test_stats['failed_tests'] == 0:
            tb.log.info("🎉 COMPREHENSIVE CDC + CLOCK GATING TEST SUITE PASSED! 🎉")
        else:
            tb.log.error("❌ COMPREHENSIVE CDC + CLOCK GATING TEST SUITE FAILED ❌")
            assert False, f"CDC + Clock Gating test suite failed: {tb.test_stats['failed_tests']} failed tests"

    finally:
        # Clean shutdown
        tb.done = True
        await tb.cmd_handler.stop()
        # Final CDC + Clock Gating synchronization wait
        await tb.wait_clocks('aclk', 30)
        await tb.wait_clocks('pclk', 30)


@pytest.mark.parametrize("addr_width, data_width, depth, cg_idle_count_width", [(32, 32, 2, 4), (32, 32, 2, 12)])
def test_apb_slave_cdc_cg_robust(request, addr_width, data_width, depth, cg_idle_count_width):
    """Robust APB-GAXI CDC + Clock Gating test with comprehensive validation."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':        'rtl/common',
        'rtl_amba':       'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':        'rtl/amba/apb',
        'rtl_gaxi':       'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave_cdc_cg"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'],          "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'],          "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],         "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],  "cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],  "amba_clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_apb'],          "apb_slave.sv"),
        os.path.join(rtl_dict['rtl_apb'],         f"{dut_name}.sv")
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cg_str = TBBase.format_dec(cg_idle_count_width, 2)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_cg{cg_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth", "cg_idle_count_width"]
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
        'TEST_CG_IDLE_COUNT_WIDTH': str(cg_idle_count_width),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-max-width", "512",
    ]

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

        print(f"✓ APB-GAXI CDC + Clock Gating robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Clock Gating Analysis Available in Logs")

    except Exception as e:
        print(f"❌ APB-GAXI CDC + Clock Gating robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC + Clock Gating analysis.")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Robust APB-GAXI CDC + Clock Gating test with comprehensive validation."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':        'rtl/common',
        'rtl_amba':       'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_apb':        'rtl/amba/apb',
        'rtl_gaxi':       'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave_cdc_cg"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'],          "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'],          "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],         "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],  "cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],  "amba_clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_apb'],          "apb_slave.sv"),
        os.path.join(rtl_dict['rtl_apb'],         f"{dut_name}.sv")
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cg_str = TBBase.format_dec(cg_idle_count_width, 2)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_cg{cg_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth", "cg_idle_count_width"]
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
        'TEST_CG_IDLE_COUNT_WIDTH': str(cg_idle_count_width),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-max-width", "512",
    ]

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

        print(f"✓ APB-GAXI CDC + Clock Gating robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Clock Gating Analysis Available in Logs")

    except Exception as e:
        print(f"❌ APB-GAXI CDC + Clock Gating robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC + Clock Gating analysis.")
        raise
