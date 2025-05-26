"""
Wrapper class for AXI Error Monitor Base testbench.

This module provides a wrapper class that integrates all the components needed
for testing the AXI Error Monitor Base module, including masters, slaves,
monitors, and test classes.

Updated to match the RTL's consolidated 64-bit interrupt bus interface.
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

# Import the interrupt bus monitor
from ..intrbus import IntrBusComponents, extract_packet_fields

# Import the test classes
from .axi_errmon_basic_test import AXIErrorMonBasicTest
# Comment out test imports until implemented
# from .axi_errmon_fifo_test import AXIErrorMonFIFOTest
# from .axi_errmon_error_test import AXIErrorMonErrorTest
# from .axi_errmon_multichannel_test import AXIErrorMonMultiChannelTest
# from .axi_errmon_random_test import AXIErrorMonRandomTest
# from .axi_errmon_intrbus_test import AXIErrorMonIntrBusTest


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
    Updated for consolidated 64-bit interrupt bus interface.
    """

    def __init__(self, dut,
                    addr_width=32,
                    id_width=8,
                    is_read=True,
                    is_axi=True,
                    intr_fifo_depth=8,
                    debug_fifo_depth=8,
                    unit_id=9,
                    agent_id=99,
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
        self.intr_fifo_depth = intr_fifo_depth
        self.debug_fifo_depth = debug_fifo_depth
        self.channels = channels
        self.unit_id = unit_id
        self.agent_id = agent_id

        # Set the errmon delay configs to match timeout values
        self.dut.i_cfg_freq_sel.value = 4  # Timer frequency
        self.dut.i_cfg_addr_cnt.value = 1  # Address timeout threshold
        self.dut.i_cfg_data_cnt.value = 5  # Data timeout threshold
        self.dut.i_cfg_resp_cnt.value = 6  # Response timeout threshold

        # Enable all packet types by default
        self.dut.i_cfg_error_enable.value = 1
        self.dut.i_cfg_compl_enable.value = 1
        self.dut.i_cfg_threshold_enable.value = 1
        self.dut.i_cfg_timeout_enable.value = 1
        self.dut.i_cfg_perf_enable.value = 1
        self.dut.i_cfg_debug_enable.value = 1

        # Set threshold configuration values
        self.dut.i_cfg_active_trans_threshold.value = 10
        self.dut.i_cfg_latency_threshold.value = 1000

        # Set debug configuration (if debug module enabled)
        if hasattr(self.dut, 'i_cfg_debug_level'):
            self.dut.i_cfg_debug_level.value = 0xF  # All debug levels
        if hasattr(self.dut, 'i_cfg_debug_mask'):
            self.dut.i_cfg_debug_mask.value = 0xFFFF  # All debug events

        # Compute maximum timer values
        self.max_timer_value = 16384

        # Constants for error types (must match RTL definitions from axi_errmon_types.sv)
        self.ERROR_ADDR_TIMEOUT = 0x1  # EVT_ADDR_TIMEOUT
        self.ERROR_DATA_TIMEOUT = 0x2  # EVT_DATA_TIMEOUT
        self.ERROR_RESP_TIMEOUT = 0x3  # EVT_RESP_TIMEOUT
        self.ERROR_RESP_SLVERR = 0x4   # EVT_RESP_SLVERR
        self.ERROR_RESP_DECERR = 0x5   # EVT_RESP_DECERR

        # Packet type constants (from axi_errmon_types.sv)
        self.PKT_TYPE_ERROR = 0x0      # PktTypeError
        self.PKT_TYPE_COMPLETION = 0x1 # PktTypeCompletion
        self.PKT_TYPE_THRESHOLD = 0x2  # PktTypeThreshold
        self.PKT_TYPE_TIMEOUT = 0x3    # PktTypeTimeout
        self.PKT_TYPE_PERF = 0x4       # PktTypePerf
        self.PKT_TYPE_DEBUG = 0xF      # PktTypeDebug

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

        # Initialize interrupt bus components
        self._init_intrbus_components()

        # Initialize ready signal controller
        self.ready_ctrl = ReadySignalController(dut, log=self.log)

        # Initialize monitoring structures
        self.errors_detected = []
        self.intrbus_events = []
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

        # Add AXI-specific fields
        if self.is_axi:
            field_config.add_field(FieldDefinition(
                name="len",
                bits=8,
                default=0,
                format="dec",
                display_width=2,
                description="Burst length"
            ))
            field_config.add_field(FieldDefinition(
                name="size",
                bits=3,
                default=0b010,  # Default to 4 bytes
                format="bin",
                display_width=3,
                description="Burst size"
            ))
            field_config.add_field(FieldDefinition(
                name="burst",
                bits=2,
                default=0b01,  # INCR
                format="bin",
                display_width=2,
                description="Burst type"
            ))
        return field_config

    def _create_data_field_config(self):
        """Create field configuration for data channel"""
        field_config = FieldConfig()

        if self.is_read:
            # Read data channel includes ID and response
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
                description="Response code (read data)"
            ))

            # AXI-specific field
            if self.is_axi:
                field_config.add_field(FieldDefinition(
                    name="last",
                    bits=1,
                    default=0,
                    format="bin",
                    display_width=1,
                    description="Last beat"
                ))
        else:
            # Write data channel - note: for monitoring only, so no data value
            # fields for strobe and last signal
            field_config.add_field(FieldDefinition(
                name="last",
                bits=1,
                default=1,  # Default to last beat
                format="bin",
                display_width=1,
                description="Last flag"
            ))

            if not self.is_axi:  # AXI-Lite doesn't have data signals beyond valid/ready
                field_config.add_field(FieldDefinition(
                    name="strb",
                    bits=4,
                    default=0xF,
                    format="bin",
                    display_width=4,
                    description="Byte strobe"
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

    def _init_gaxi_components(self):
        """Initialize all GAXI components"""
        # Create address channel master
        addr_optional_map = {
            'm2s_pkt_addr': 'i_addr_addr',
            'm2s_pkt_id': 'i_addr_id'
        }

        if self.is_axi:  # Add AXI-specific signals
            addr_optional_map |= {
                'm2s_pkt_len': 'i_addr_len',
                'm2s_pkt_size': 'i_addr_size',
                'm2s_pkt_burst': 'i_addr_burst',
            }

        self.addr_master = GAXIMaster(
            self.dut, 'AddrMaster', '', self.dut.aclk,
            field_config=self.addr_field_config,
            multi_sig=True,
            timeout_cycles=10000,
            signal_map={
                'm2s_valid': 'i_addr_valid',
                's2m_ready': 'i_addr_ready'
            },
            optional_signal_map=addr_optional_map,
            log=self.log,
            randomizer=FlexRandomizer(self.master_randomizer_configs['fixed'])
        )

        # Create data channel master
        data_valid_signal = 'i_data_valid'
        data_ready_signal = 'i_data_ready'
        data_optional_map = {}

        if self.is_read:
            # For read mode, we connect to data ID, last and resp
            data_optional_map = {
                'm2s_pkt_id': 'i_data_id',
                'm2s_pkt_last': 'i_data_last',
                'm2s_pkt_resp': 'i_data_resp'
            }
        else:
            # For write mode, we only connect to last signal
            data_optional_map = {
                'm2s_pkt_last': 'i_data_last'
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
            optional_signal_map=addr_optional_map,
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
            optional_signal_map=data_optional_map,
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

    def _init_intrbus_components(self):
        """Initialize interrupt bus components"""
        # Create intrbus components using IntrBusComponents class
        self.intrbus_components = IntrBusComponents(
            self.dut,
            self.dut.aclk,
            title_prefix="IntrBus",
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_configs['fixed'])
        )

        # Extract individual components for easier access
        self.intrbus_master = self.intrbus_components.master
        self.intrbus_slave = self.intrbus_components.slave
        self.intrbus_monitor = self.intrbus_components.monitor

        # Set up callbacks for the monitor
        self.intrbus_monitor.add_callback(self._on_intrbus_event)

    def _on_intrbus_event(self, packet):
        """Callback for all interrupt bus events"""
        # Extract fields from the 64-bit packet
        if hasattr(packet, 'intrbus_packet'):
            fields = extract_packet_fields(packet.intrbus_packet)
        else:
            # Fallback - try to get individual fields
            fields = {
                'packet_type': getattr(packet, 'packet_type', 0),
                'event_code': getattr(packet, 'event_code', 0),
                'channel_id': getattr(packet, 'channel_id', 0),
                'unit_id': getattr(packet, 'unit_id', 0),
                'agent_id': getattr(packet, 'agent_id', 0),
                'addr': getattr(packet, 'addr', 0)
            }

        # Format the event for logging
        event_desc = self.intrbus_components.format_event(packet)
        self.log.info(f"Interrupt bus event detected: {event_desc}{self.get_time_ns_str()}")

        # Store event for analysis
        event_info = {
            'time': get_sim_time('ns'),
            'packet_type': fields['packet_type'],
            'event_code': fields['event_code'],
            'channel_id': fields['channel_id'],
            'unit_id': fields['unit_id'],
            'agent_id': fields['agent_id'],
            'addr': fields['addr'],
            'description': event_desc
        }

        self.intrbus_events.append(event_info)

        # Additional processing based on packet type
        if fields['packet_type'] == self.PKT_TYPE_ERROR:  # Error event
            error_info = {
                'time': get_sim_time('ns'),
                'type': self._map_event_code_to_error_type(fields['event_code']),
                'id': fields['channel_id'],
                'addr': fields['addr'],
                'event_code': fields['event_code']
            }

            # Add decoded error type string
            error_type_str = []
            if fields['event_code'] == 0x1:  # ADDR_TIMEOUT
                error_type_str.append("ADDR_TIMEOUT")
            elif fields['event_code'] == 0x2:  # DATA_TIMEOUT
                error_type_str.append("DATA_TIMEOUT")
            elif fields['event_code'] == 0x3:  # RESP_TIMEOUT
                error_type_str.append("RESP_TIMEOUT")
            elif fields['event_code'] == 0x4:  # RESP_SLVERR
                error_type_str.append("RESP_SLVERR")
            elif fields['event_code'] == 0x5:  # RESP_DECERR
                error_type_str.append("RESP_DECERR")
            elif fields['event_code'] == 0x6:  # DATA_ORPHAN
                error_type_str.append("DATA_ORPHAN")
            elif fields['event_code'] == 0x7:  # RESP_ORPHAN
                error_type_str.append("RESP_ORPHAN")
            elif fields['event_code'] == 0x8:  # PROTOCOL
                error_type_str.append("PROTOCOL")

            error_info['type_str'] = "|".join(error_type_str)

            # Store error
            self.errors_detected.append(error_info)

            self.log.info(f"Error event detected: {error_info['type_str']}, ID={fields['channel_id']}, addr=0x{fields['addr']:X}{self.get_time_ns_str()}")

    def _map_event_code_to_error_type(self, event_code):
        """Map event code to error type constant"""
        if event_code == 0x1:  # ADDR_TIMEOUT
            return self.ERROR_ADDR_TIMEOUT
        elif event_code == 0x2:  # DATA_TIMEOUT
            return self.ERROR_DATA_TIMEOUT
        elif event_code == 0x3:  # RESP_TIMEOUT
            return self.ERROR_RESP_TIMEOUT
        elif event_code in [0x4, 0x5]:  # RESP_SLVERR or RESP_DECERR
            return 0x8  # Generic response error bit
        else:
            return 0

    def _create_test_classes(self):
        """Create the test classes"""
        self.basic_test = AXIErrorMonBasicTest(self)
        # Comment out test class creation until implemented
        # self.fifo_test = AXIErrorMonFIFOTest(self)
        # self.error_test = AXIErrorMonErrorTest(self)
        # self.multichannel_test = AXIErrorMonMultiChannelTest(self)
        # self.random_test = AXIErrorMonRandomTest(self)
        # self.intrbus_test = AXIErrorMonIntrBusTest(self)

    def _log_config(self):
        """Log the testbench configuration"""
        self.log.info(f"{'=' * 80}")
        self.log.info("AXI Error Monitor Testbench Configuration:")
        self.log.info(f"{'-' * 80}")
        self.log.info(f"Address Width:     {self.addr_width}")
        self.log.info(f"ID Width:          {self.id_width}")
        self.log.info(f"Channels:          {self.channels}")
        self.log.info(f"Unit ID:           {self.unit_id}")
        self.log.info(f"Agent ID:          {self.agent_id}")
        self.log.info(f"Mode:              {'Read' if self.is_read else 'Write'}")
        self.log.info(f"Interface:         {'AXI' if self.is_axi else 'AXI-Lite'}")
        self.log.info(f"Addr Timeout:      {self.timeout_addr}")
        self.log.info(f"Data Timeout:      {self.timeout_data}")
        self.log.info(f"Resp Timeout:      {self.timeout_resp}")
        self.log.info(f"Intr FIFO Depth:   {self.intr_fifo_depth}")
        self.log.info(f"Debug FIFO Depth:  {self.debug_fifo_depth}")
        self.log.info(f"{'=' * 80}")

    async def reset_dut(self):
        """Reset the DUT and all testbench components"""
        self.log.debug(f"Resetting DUT{self.get_time_ns_str()}")

        # Reset the DUT
        self.dut.aresetn.value = 0

        # Reset monitoring structures
        self.errors_detected = []
        self.intrbus_events = []
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

        # Reset the interrupt bus components
        await self.intrbus_components.reset_bus()

        # Set intrbus slave to normal ready speed
        self.intrbus_slave.set_randomizer(FlexRandomizer(self.randomizer_configs['fixed']))

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

        # Comment out advanced tests until implemented
        # if test_level != 'basic':
        #     # Medium adds error detection
        #     error_passed = await self.error_test.run()
        #     all_passed = all_passed and error_passed
        #
        #     # Run intrbus-specific tests
        #     intrbus_passed = await self.intrbus_test.run()
        #     all_passed = all_passed and intrbus_passed
        #
        #     # Run random traffic test with moderate number of transactions
        #     if test_level == 'medium':
        #         random_passed = await self.random_test.run(num_transactions=20)
        #         all_passed = all_passed and random_passed
        #
        # # Full adds multichannel test and more extensive random testing
        # if test_level == 'full':
        #     multichannel_passed = await self.multichannel_test.run()
        #     all_passed = all_passed and multichannel_passed
        #
        #     # Run more extensive random traffic test
        #     random_passed = await self.random_test.run(num_transactions=50)
        #     all_passed = all_passed and random_passed

        if all_passed:
            self.log.info(f"All tests at level {test_level} passed{self.get_time_ns_str()}")
        else:
            self.log.error(f"Some tests at level {test_level} failed{self.get_time_ns_str()}")

        return all_passed
