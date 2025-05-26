"""
Wrapper class for AXI Error Monitor Base testbench.

This module provides a wrapper class that integrates all the components needed
for testing the AXI Error Monitor Base module, including masters, slaves,
monitors, and test classes.
"""

import os
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer, Edge
from cocotb.utils import get_sim_time
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket

# Import the ready signal controller
from .axi_errmon_readyctrl import ReadySignalController

# Import the test classes
from .axi_errmon_basic_test import AXIErrorMonBasicTest
from .axi_errmon_fifo_test import AXIErrorMonFIFOTest
from .axi_errmon_error_test import AXIErrorMonErrorTest
from .axi_errmon_multichannel_test import AXIErrorMonMultiChannelTest
from .axi_errmon_random_test import AXIErrorMonRandomTest


RANDOMIZER_CONFIGS = {
    'fixed': {
            'ready_delay': ([[2, 2]], [1])
    },
    'constrained': {
            'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
    },
    'fast': {
            'ready_delay': ([[0, 0], [1, 8], [9, 30]], [5, 0, 0])
    },
    'backtoback': {
            'ready_delay': ([[0, 0]], [1])
    },
    'burst_pause': {
            'ready_delay': ([[0, 0], [1, 5]], [10, 1])
    },
    'slow_consumer': {
            'ready_delay': ([[10, 20]], [1])
    },
}

class AXIErrorMonitorTB(TBBase):
    """
    Wrapper class for AXI Error Monitor testbench.
    Manages masters, slaves, monitors, and provides interface to test classes.
    """

    def __init__(self, dut,
                    addr_width=32,
                    id_width=8,
                    is_read=True,
                    is_axi=True,
                    error_fifo_depth=4,
                    addr_fifo_depth=4,
                    channels=1):
        """Initialize with DUT and configuration parameters"""
        super().__init__(dut)

        # Store configuration parameters
        self.addr_width = addr_width
        self.id_width = id_width
        self.is_read = is_read
        self.is_axi = is_axi
        timeout_addr = 40
        self.timeout_addr = timeout_addr
        self.timeout_data = timeout_addr * 4
        self.timeout_resp = timeout_addr * 6
        self.error_fifo_depth = error_fifo_depth
        self.addr_fifo_depth = addr_fifo_depth
        self.channels = channels

        # set the errmon delay configss
        self.dut.i_cfg_freq_sel.value = 4
        self.dut.i_cfg_addr_cnt.value = 1
        self.dut.i_cfg_data_cnt.value = 5
        self.dut.i_cfg_resp_cnt.value = 6

        # Compute maximum timer values
        self.max_timer_value = 16384

        # Constants for error types (must match RTL definitions)
        self.ERROR_ADDR_TIMEOUT = 0x1  # Address timeout
        self.ERROR_DATA_TIMEOUT = 0x2  # Data timeout
        self.ERROR_RESP_TIMEOUT = 0x4  # Response timeout
        self.ERROR_RESP_ERROR = 0x8    # Response error

        # adjust the randomized configs
        self.randomizer_configs = RANDOMIZER_CONFIGS
        timeout = timeout_addr + 50
        self.randomizer_configs['slow_consumer']['ready_delay'] = ([[timeout, timeout]], [1])
        self.master_randomizer_configs = {
                                            'fixed': {
                                                    'valid_delay': ([[2, 2]], [1])
                                            },
                                            'slow_producer': {
                                                    'valid_delay': ([[timeout, timeout]], [1])
                                            },
        }
        # Create field configurations
        self._create_field_configs()

        # Initialize GAXI components
        self._init_gaxi_components()

        # Initialize ready signal controller
        self.ready_ctrl = ReadySignalController(dut, log=self.log)

        # Initialize monitoring structures
        self.errors_detected = []
        self.axi_transactions = []

        # Create test classes
        self._create_test_classes()

        # Log configuration
        self._log_config()

    def _create_field_configs(self):
        """Create field configurations for all channels"""
        self.addr_field_config = self._create_addr_field_config()
        self.data_field_config = self._create_data_field_config()
        self.resp_field_config = None if self.is_read else self._create_resp_field_config()
        self.error_field_config = self._create_error_field_config()

    def _create_addr_field_config(self):
        """Create field configuration for address channel"""
        field_config = FieldConfig()
        field_config.add_field(FieldDefinition(
            name="addr",
            bits=self.addr_width,
            default=0,
            format="hex",
            display_width=8,
            description="Address value"
        ))
        field_config.add_field(FieldDefinition(
            name="id",
            bits=self.id_width,
            default=0,
            format="hex",
            display_width=2,
            description="Transaction ID"
        ))
        return field_config

    def _create_data_field_config(self):
        """Create field configuration for data channel"""
        field_config = FieldConfig()
        field_config.add_field(FieldDefinition(
            name="id",
            bits=self.id_width,
            default=0,
            format="hex",
            display_width=2,
            description="Transaction ID"
        ))
        field_config.add_field(FieldDefinition(
            name="last",
            bits=1,
            default=0,
            format="bin",
            display_width=1,
            description="Last flag"
        ))
        field_config.add_field(FieldDefinition(
            name="resp",
            bits=2,
            default=0,
            format="bin",
            display_width=2,
            description="Response code (read data)"
        ))
        return field_config

    def _create_resp_field_config(self):
        """Create field configuration for response channel (write only)"""
        field_config = FieldConfig()
        field_config.add_field(FieldDefinition(
            name="id",
            bits=self.id_width,
            default=0,
            format="hex",
            display_width=2,
            description="Transaction ID"
        ))
        field_config.add_field(FieldDefinition(
            name="resp",
            bits=2,
            default=0,
            format="bin",
            display_width=2,
            description="Response code"
        ))
        return field_config

    def _create_error_field_config(self):
        """Create field configuration for error reporting FIFO"""
        field_config = FieldConfig()
        field_config.add_field(FieldDefinition(
            name="error_type",
            bits=8,
            default=0,
            format="hex",
            display_width=1,
            description="Error type"
        ))
        field_config.set_encoding("error_type", {
            1: "AddrTO",   # Address timeout  (0b00000001)
            2: "DataTO",   # Data timeout     (0b00000010)
            4: "RespTO",   # Response timeout (0b00000100)
            8: "RespErr"   # Response error   (0b00001000)
        })
        field_config.add_field(FieldDefinition(
            name="error_id",
            bits=self.id_width,
            default=0,
            format="hex",
            display_width=2,
            description="Error ID"
        ))
        field_config.add_field(FieldDefinition(
            name="error_addr",
            bits=self.addr_width,
            default=0,
            format="hex",
            display_width=8,
            description="Error address"
        ))
        field_config.add_field(FieldDefinition(
            name="error_unit_id",
            bits=self.addr_width,
            default=0,
            format="hex",
            display_width=2,
            description="Error Unit ID"
        ))
        field_config.add_field(FieldDefinition(
            name="error_agent_id",
            bits=self.addr_width,
            default=0,
            format="hex",
            display_width=2,
            description="Error Agent ID"
        ))
        return field_config

    def _init_gaxi_components(self):
        """Initialize all GAXI components"""
        # Create address channel master
        self.addr_master = GAXIMaster(
            self.dut, 'AddrMaster', '', self.dut.aclk,
            field_config=self.addr_field_config,
            multi_sig=True,
            timeout_cycles=10000,
            signal_map={
                'm2s_valid': 'i_addr_valid',
                's2m_ready': 'i_addr_ready'
            },
            optional_signal_map={
                'm2s_pkt_addr': 'i_addr_addr',
                'm2s_pkt_id': 'i_addr_id'
            },
            log=self.log,
            randomizer=FlexRandomizer(self.master_randomizer_configs['fixed'])
        )

        # Create data channel master
        data_valid_signal = 'i_data_valid'
        data_ready_signal = 'i_data_ready'
        data_optional_map = {
            'm2s_pkt_id': 'i_data_id',
            'm2s_pkt_last': 'i_data_last',
            'm2s_pkt_resp': 'i_data_resp'
        }

        self.data_master = GAXIMaster(
            self.dut, 'DataMaster', '', self.dut.aclk,
            field_config=self.data_field_config,
            multi_sig=True,
            timeout_cycles=10000,
            signal_map={
                'm2s_valid': data_valid_signal,
                's2m_ready': data_ready_signal
            },
            optional_signal_map=data_optional_map,
            log=self.log,
            randomizer=FlexRandomizer(self.master_randomizer_configs['fixed'])
        )

        # Create response channel master (write only)
        self.resp_master = None
        if not self.is_read:
            self.resp_master = GAXIMaster(
                self.dut, 'RespMaster', '', self.dut.aclk,
                field_config=self.resp_field_config,
                multi_sig=True,
            timeout_cycles=10000,
                signal_map={
                    'm2s_valid': 'i_resp_valid',
                    's2m_ready': 'i_resp_ready'
                },
                optional_signal_map={
                    'm2s_pkt_id': 'i_resp_id',
                    'm2s_pkt_resp': 'i_resp'
                },
                log=self.log,
            randomizer=FlexRandomizer(self.master_randomizer_configs['fixed'])

            )

        # Create error reporting FIFO slave
        self.error_slave = GAXISlave(
            self.dut, 'ErrorSlave', '', self.dut.aclk,
            field_config=self.error_field_config,
            multi_sig=True,
            signal_map={
                'm2s_valid': 'o_error_valid',
                's2m_ready': 'i_error_ready'
            },
            optional_signal_map={
                'm2s_pkt_error_type':     'o_error_type',
                'm2s_pkt_error_id':       'o_error_id',
                'm2s_pkt_error_addr':     'o_error_addr',
                'm2s_pkt_error_unit_id':  'o_error_unit_id',
                'm2s_pkt_error_agent_id': 'o_error_agent_id',
            },
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_configs['fixed'])
        )

        # Create monitors
        self.addr_monitor = GAXIMonitor(
            self.dut, 'AddrMonitor', '', self.dut.aclk,
            field_config=self.addr_field_config,
            is_slave=False,
            multi_sig=True,
            signal_map={
                'm2s_valid': 'i_addr_valid',
                's2m_ready': 'i_addr_ready'
            },
            optional_signal_map={
                'm2s_pkt_addr': 'i_addr_addr',
                'm2s_pkt_id': 'i_addr_id'
            },
            log=self.log
        )

        self.data_monitor = GAXIMonitor(
            self.dut, 'DataMonitor', '', self.dut.aclk,
            field_config=self.data_field_config,
            is_slave=False,
            multi_sig=True,
            signal_map={
                'm2s_valid': data_valid_signal,
                's2m_ready': data_ready_signal
            },
            optional_signal_map={
                'm2s_pkt_id': 'i_data_id',
                'm2s_pkt_last': 'i_data_last'
            },
            log=self.log
        )

        # Create response monitor (write only)
        self.resp_monitor = None
        if not self.is_read:
            self.resp_monitor = GAXIMonitor(
                self.dut, 'RespMonitor', '', self.dut.aclk,
                field_config=self.resp_field_config,
                is_slave=False,
                multi_sig=True,
                signal_map={
                    'm2s_valid': 'i_resp_valid',
                    's2m_ready': 'i_resp_ready'
                },
                optional_signal_map={
                    'm2s_pkt_id': 'i_resp_id',
                    'm2s_pkt_resp': 'i_resp'
                },
                log=self.log
            )

        # Set up callbacks
        self.error_slave.add_callback(self._on_error_report)

    def _on_error_report(self, packet):
        """Callback for error reports from the error FIFO"""
        self.log.info(f"Error report: {packet.formatted(compact=True)}{self.get_time_ns_str()}")

        # Extract error information
        error_info = {
            'time': get_sim_time('ns'),
            'type': packet.error_type,
            'id': packet.error_id,
            'addr': packet.error_addr
        }

        # Add decoded error type string
        error_type_str = []
        if error_info['type'] & self.ERROR_ADDR_TIMEOUT:
            error_type_str.append("ADDR_TIMEOUT")
        if error_info['type'] & self.ERROR_DATA_TIMEOUT:
            error_type_str.append("DATA_TIMEOUT")
        if error_info['type'] & self.ERROR_RESP_TIMEOUT:
            error_type_str.append("RESP_TIMEOUT")
        if error_info['type'] & self.ERROR_RESP_ERROR:
            error_type_str.append("RESP_ERROR")

        error_info['type_str'] = "|".join(error_type_str)

        # Store error
        self.errors_detected.append(error_info)

    def _create_test_classes(self):
        """Create the test classes"""
        self.basic_test = AXIErrorMonBasicTest(self)
        self.fifo_test = AXIErrorMonFIFOTest(self)
        self.error_test = AXIErrorMonErrorTest(self)
        self.multichannel_test = AXIErrorMonMultiChannelTest(self)
        self.random_test = AXIErrorMonRandomTest(self)

    def _log_config(self):
        """Log the testbench configuration"""
        self.log.info(f"{'=' * 80}")
        self.log.info("AXI Error Monitor Testbench Configuration:")
        self.log.info(f"{'-' * 80}")
        self.log.info(f"Address Width:     {self.addr_width}")
        self.log.info(f"ID Width:          {self.id_width}")
        self.log.info(f"Channels:          {self.channels}")
        self.log.info(f"Mode:              {'Read' if self.is_read else 'Write'}")
        self.log.info(f"Interface:         {'AXI' if self.is_axi else 'AXI-Lite'}")
        self.log.info(f"Addr Timeout:      {self.timeout_addr}")
        self.log.info(f"Data Timeout:      {self.timeout_data}")
        self.log.info(f"Resp Timeout:      {self.timeout_resp}")
        self.log.info(f"Error FIFO Depth:  {self.error_fifo_depth}")
        self.log.info(f"Addr FIFO Depth:   {self.addr_fifo_depth}")
        self.log.info(f"{'=' * 80}")

    async def reset_dut(self):
        """Reset the DUT and all testbench components"""
        self.log.debug(f"Resetting DUT{self.get_time_ns_str()}")

        # Reset the DUT
        self.dut.aresetn.value = 0

        # Reset monitoring structures
        self.errors_detected = []
        self.axi_transactions = []

        # Wait for reset to stabilize
        await self.wait_clocks('aclk', 5)

        # Release reset
        self.dut.aresetn.value = 1

        # Reset GAXI components
        await self.addr_master.reset_bus()
        await self.data_master.reset_bus()
        if self.resp_master:
            await self.resp_master.reset_bus()
        await self.error_slave.reset_bus()

        # Start ready signal controller
        await self.ready_ctrl.start()

        # Wait for stabilization
        await self.wait_clocks('aclk', 5)

        self.log.debug(f"Reset complete{self.get_time_ns_str()}")

    def set_data_resp(self, resp_value):
        """
        Set the i_data_resp signal value for read transactions.

        Args:
            resp_value: Response code (0-3)
                0: OKAY
                1: EXOKAY (exclusive access OK)
                2: SLVERR (slave error)
                3: DECERR (decode error)
        """
        # Only applicable for read mode
        if self.is_read:
            self.dut.i_data_resp.value = resp_value
            self.log.debug(f"Set i_data_resp = {resp_value}{self.get_time_ns_str()}")
        else:
            self.log.warning(f"set_data_resp() called in write mode (ignored){self.get_time_ns_str()}")

    async def run_all_tests(self, test_level='basic'):
        """
        Run all tests according to the test level

        Args:
            test_level: Test level ('basic', 'medium', or 'full')

        Returns:
            True if all tests passed, False otherwise
        """
        self.log.info(f"Running tests at level: {test_level}{self.get_time_ns_str()}")

        all_passed = True

        # Basic tests always run
        basic_passed = await self.basic_test.run()
        all_passed = all_passed and basic_passed

        fifo_passed = await self.fifo_test.run()
        all_passed = all_passed and fifo_passed

        # Medium adds error detection
        if test_level != 'basic':
            error_passed = await self.error_test.run()
            all_passed = all_passed and error_passed

            # Run random traffic test with moderate number of transactions
            if test_level == 'medium':
                random_passed = await self.random_test.run(num_transactions=20)
                all_passed = all_passed and random_passed

        # Full adds multichannel test and more extensive random testing
        if test_level == 'full':
            # multichannel_passed = await self.multichannel_test.run()
            # all_passed = all_passed and multichannel_passed

            # Run more extensive random traffic test
            random_passed = await self.random_test.run(num_transactions=50)
            all_passed = all_passed and random_passed

        if all_passed:
            self.log.info(f"All tests at level {test_level} passed{self.get_time_ns_str()}")
        else:
            self.log.error(f"Some tests at level {test_level} failed{self.get_time_ns_str()}")

        return all_passed

    def verify_timer_operation(self, timer_operation):
        """
        Verify timer operation type matches the expected behavior

        Args:
            timer_operation: Expected timer operation ('count_up' or 'count_down')

        Returns:
            True if the operation is as expected, False otherwise
        """
        # In the updated RTL, timers always count down from MAX
        expected_operation = 'count_down'

        if timer_operation != expected_operation:
            self.log.error(f"Timer operation mismatch: expected {expected_operation}, got {timer_operation}{self.get_time_ns_str()}")
            return False

        return True
