"""
Wrapper class for AXI Error Monitor Base testbench.

This module provides a wrapper class that integrates all the components needed
for testing the AXI Error Monitor Base module, including masters, slaves,
monitors, and test classes.

Updated to match the RTL's consolidated 64-bit interrupt bus interface.
Updated to use separate intrbus component creation functions.
Enhanced with comprehensive parameter control for systematic testing.
Fixed to properly use GAXIPacket field access throughout.
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

# Import the updated interrupt bus components and constants
from ..intrbus import (
    create_intrbus_slave, create_intrbus_monitor, create_intrbus_specialized_monitor,
    create_intrbus_field_config, EVENT_CODES, PACKET_TYPES,
    get_event_name, get_packet_type_name, is_error_event, is_timeout_event, is_response_error_event
)

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
    Updated for consolidated 64-bit interrupt bus interface with separate component creation.
    Enhanced with comprehensive parameter control for systematic testing.
    Fixed to properly use GAXIPacket field access throughout.
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
                    channels=1,
                    # NEW: Enhanced configuration parameters
                    timer_config=None,
                    packet_enable_config=None):
        """Initialize with DUT and configuration parameters"""
        super().__init__(dut)

        # Store configuration parameters
        self.addr_width = addr_width
        self.id_width = id_width
        self.is_read = is_read
        self.is_axi = is_axi
        self.intr_fifo_depth = intr_fifo_depth
        self.debug_fifo_depth = debug_fifo_depth
        self.channels = channels
        self.unit_id = unit_id
        self.agent_id = agent_id

        if timer_config is None:
            timer_config = {
                'freq_sel': 4,
                'addr_cnt': 1,
                'data_cnt': 5,
                'resp_cnt': 6,
                'description': 'Default basic timing'
            }
        self.timer_config = timer_config

        # NEW: Packet enable configuration
        if packet_enable_config is None:
            packet_enable_config = {
                'error_enable': True,
                'compl_enable': False,
                'threshold_enable': False,
                'timeout_enable': False,
                'perf_enable': False,
                'debug_enable': False,
                'description': 'Default error-only mode'
            }
        self.packet_enable_config = packet_enable_config

        # Calculate timeout values based on timer configuration
        base_timeout = 40  # Base timeout value
        freq_multiplier = max(1, 6 - self.timer_config['freq_sel'])  # Higher freq_sel = faster timer

        self.timeout_addr = self.timer_config['addr_cnt'] * freq_multiplier
        self.timeout_data = self.timer_config['data_cnt'] * freq_multiplier
        self.timeout_resp = self.timer_config['resp_cnt'] * freq_multiplier

        # Apply RTL configuration - these will be set in configure_rtl_parameters()
        self.rtl_configured = False

        # Use imported constants from intrbus module
        self.EVENT_CODES = EVENT_CODES
        self.PACKET_TYPES = PACKET_TYPES

        # Adjust randomizer configs based on timeouts
        self.randomizer_configs = RANDOMIZER_CONFIGS.copy()
        timeout = max(self.timeout_addr, self.timeout_data, self.timeout_resp) + 50
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

        # Initialize interrupt bus components (updated to use separate creation)
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

    async def configure_rtl_parameters(self):
        """Configure RTL parameters based on the provided configurations"""
        if self.rtl_configured:
            return

        # Configure timer parameters
        self.dut.i_cfg_freq_sel.value = self.timer_config['freq_sel']
        self.dut.i_cfg_addr_cnt.value = self.timer_config['addr_cnt']
        self.dut.i_cfg_data_cnt.value = self.timer_config['data_cnt']
        self.dut.i_cfg_resp_cnt.value = self.timer_config['resp_cnt']

        # Configure packet type enables
        self.dut.i_cfg_error_enable.value = 1 if self.packet_enable_config['error_enable'] else 0
        self.dut.i_cfg_compl_enable.value = 1 if self.packet_enable_config['compl_enable'] else 0
        self.dut.i_cfg_threshold_enable.value = 1 if self.packet_enable_config['threshold_enable'] else 0
        self.dut.i_cfg_timeout_enable.value = 1 if self.packet_enable_config['timeout_enable'] else 0
        self.dut.i_cfg_perf_enable.value = 1 if self.packet_enable_config['perf_enable'] else 0
        self.dut.i_cfg_debug_enable.value = 1 if self.packet_enable_config['debug_enable'] else 0

        # Set threshold configuration values (reasonable defaults)
        self.dut.i_cfg_active_trans_threshold.value = 10
        self.dut.i_cfg_latency_threshold.value = 1000

        # Set debug configuration (if debug module enabled)
        if hasattr(self.dut, 'i_cfg_debug_level'):
            self.dut.i_cfg_debug_level.value = 0xF  # All debug levels
        if hasattr(self.dut, 'i_cfg_debug_mask'):
            self.dut.i_cfg_debug_mask.value = 0xFFFF  # All debug events

        self.rtl_configured = True

        self.log.info(f"RTL configured with timer: {self.timer_config['description']}")
        self.log.info(f"RTL configured with packets: {self.packet_enable_config['description']}")

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
        """Initialize interrupt bus components using separate creation functions"""
        # Create interrupt bus field configuration
        self.intrbus_field_config = create_intrbus_field_config()

        # Create interrupt bus slave (for handling ready signal and backpressure)
        self.intrbus_slave = create_intrbus_slave(
            self.dut,
            self.dut.aclk,
            title_prefix="IntrBusSlave",
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_configs['fixed']),
            signal_prefix="",
            field_config=self.intrbus_field_config
        )

        # Create basic interrupt bus monitor
        self.intrbus_monitor = create_intrbus_monitor(
            self.dut,
            self.dut.aclk,
            title_prefix="IntrBusMonitor",
            log=self.log,
            signal_prefix="",
            field_config=self.intrbus_field_config,
            is_slave=True
        )

        # Create specialized monitor for enhanced callback capabilities
        self.intrbus_specialized_monitor = create_intrbus_specialized_monitor(
            self.dut,
            self.dut.aclk,
            title_prefix="IntrBusSpecializedMonitor",
            log=self.log,
            signal_prefix="",
            field_config=self.intrbus_field_config
        )

        # Set up callbacks for the basic monitor (maintains existing interface)
        self.intrbus_monitor.add_callback(self._on_intrbus_event)

        # Set up specialized callbacks for error detection
        self.intrbus_specialized_monitor.add_callback(self._on_error_event, 'error')
        self.intrbus_specialized_monitor.add_callback(self._on_timeout_event, 'timeout')
        self.intrbus_specialized_monitor.add_callback(self._on_completion_event, 'completion')

    def _on_intrbus_event(self, packet):
        """Callback for all interrupt bus events using direct field access"""
        # Validate packet type
        if not isinstance(packet, GAXIPacket):
            self.log.error(f"Expected GAXIPacket, got {type(packet)}")
            return

        # Validate required fields
        required_fields = ['packet_type', 'event_code', 'channel_id', 'unit_id', 'agent_id', 'payload']
        missing_fields = [field for field in required_fields if not hasattr(packet, field)]
        if missing_fields:
            self.log.error(f"Packet missing required fields: {missing_fields}")
            return

        # Use direct field access - no manual extraction needed!
        event_desc = self.intrbus_specialized_monitor.format_event(packet)
        self.log.info(f"Interrupt bus event detected: {event_desc}{self.get_time_ns_str()}")

        # Store event for analysis using direct field access
        event_info = {
            'time': get_sim_time('ns'),
            'packet_type': packet.packet_type,
            'event_code': packet.event_code,
            'channel_id': packet.channel_id,
            'unit_id': packet.unit_id,
            'agent_id': packet.agent_id,
            'addr': packet.payload,  # Map payload to addr for backward compatibility
            'description': event_desc
        }

        self.intrbus_events.append(event_info)

        # Additional processing based on packet type
        if packet.packet_type == self.PACKET_TYPES['ERROR']:  # Error event
            self._process_error_event(packet)

    def _on_error_event(self, packet):
        """Specialized callback for error events using direct field access"""
        if not isinstance(packet, GAXIPacket):
            self.log.error(f"Expected GAXIPacket, got {type(packet)}")
            return

        self.log.info(f"Error callback triggered: code={packet.event_code}, addr=0x{packet.payload:X}{self.get_time_ns_str()}")

    def _on_timeout_event(self, packet):
        """Specialized callback for timeout events using direct field access"""
        if not isinstance(packet, GAXIPacket):
            self.log.error(f"Expected GAXIPacket, got {type(packet)}")
            return

        self.log.info(f"Timeout callback triggered: code={packet.event_code}, addr=0x{packet.payload:X}{self.get_time_ns_str()}")

    def _on_completion_event(self, packet):
        """Specialized callback for completion events using direct field access"""
        if not isinstance(packet, GAXIPacket):
            self.log.error(f"Expected GAXIPacket, got {type(packet)}")
            return

        self.log.debug(f"Completion callback triggered: addr=0x{packet.payload:X}, ch={packet.channel_id}{self.get_time_ns_str()}")

    def _process_error_event(self, packet):
        """Process error events using direct field access"""
        if not isinstance(packet, GAXIPacket):
            self.log.error(f"Expected GAXIPacket, got {type(packet)}")
            return

        error_info = {
            'time': get_sim_time('ns'),
            'type': self._map_event_code_to_error_type(packet.event_code),
            'id': packet.channel_id,
            'addr': packet.payload,  # Map payload to addr for backward compatibility
            'event_code': packet.event_code
        }

        # Add decoded error type string using direct field access and constants
        error_type_str = []
        if packet.event_code == self.EVENT_CODES['ADDR_TIMEOUT']:
            error_type_str.append("ADDR_TIMEOUT")
        elif packet.event_code == self.EVENT_CODES['DATA_TIMEOUT']:
            error_type_str.append("DATA_TIMEOUT")
        elif packet.event_code == self.EVENT_CODES['RESP_TIMEOUT']:
            error_type_str.append("RESP_TIMEOUT")
        elif packet.event_code == self.EVENT_CODES['RESP_SLVERR']:
            error_type_str.append("RESP_SLVERR")
        elif packet.event_code == self.EVENT_CODES['RESP_DECERR']:
            error_type_str.append("RESP_DECERR")
        elif packet.event_code == self.EVENT_CODES['DATA_ORPHAN']:
            error_type_str.append("DATA_ORPHAN")
        elif packet.event_code == self.EVENT_CODES['RESP_ORPHAN']:
            error_type_str.append("RESP_ORPHAN")
        elif packet.event_code == self.EVENT_CODES['PROTOCOL']:
            error_type_str.append("PROTOCOL")

        error_info['type_str'] = "|".join(error_type_str) if error_type_str else f"UNKNOWN_ERROR_{packet.event_code:X}"

        # Store error
        self.errors_detected.append(error_info)

        self.log.info(f"Error event detected: {error_info['type_str']}, ID={packet.channel_id}, addr=0x{packet.payload:X}{self.get_time_ns_str()}")

    def _map_event_code_to_error_type(self, event_code):
        """Map event code to error type constant"""
        if event_code == self.EVENT_CODES['ADDR_TIMEOUT']:
            return self.EVENT_CODES['ADDR_TIMEOUT']
        elif event_code == self.EVENT_CODES['DATA_TIMEOUT']:
            return self.EVENT_CODES['DATA_TIMEOUT']
        elif event_code == self.EVENT_CODES['RESP_TIMEOUT']:
            return self.EVENT_CODES['RESP_TIMEOUT']
        elif event_code in [self.EVENT_CODES['RESP_SLVERR'], self.EVENT_CODES['RESP_DECERR']]:
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
        """Log the testbench configuration with enhanced information"""
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
        self.log.info(f"{'-' * 40}")
        self.log.info(f"Timer Configuration: {self.timer_config['description']}")
        self.log.info(f"  Freq Sel:        {self.timer_config['freq_sel']}")
        self.log.info(f"  Addr Count:      {self.timer_config['addr_cnt']}")
        self.log.info(f"  Data Count:      {self.timer_config['data_cnt']}")
        self.log.info(f"  Resp Count:      {self.timer_config['resp_cnt']}")
        self.log.info(f"  Calculated Timeouts:")
        self.log.info(f"    Addr Timeout:  {self.timeout_addr}")
        self.log.info(f"    Data Timeout:  {self.timeout_data}")
        self.log.info(f"    Resp Timeout:  {self.timeout_resp}")
        self.log.info(f"{'-' * 40}")
        self.log.info(f"Packet Configuration: {self.packet_enable_config['description']}")
        self.log.info(f"  Error Enable:    {self.packet_enable_config['error_enable']}")
        self.log.info(f"  Compl Enable:    {self.packet_enable_config['compl_enable']}")
        self.log.info(f"  Threshold Enable: {self.packet_enable_config['threshold_enable']}")
        self.log.info(f"  Timeout Enable:  {self.packet_enable_config['timeout_enable']}")
        self.log.info(f"  Perf Enable:     {self.packet_enable_config['perf_enable']}")
        self.log.info(f"  Debug Enable:    {self.packet_enable_config['debug_enable']}")
        self.log.info(f"{'-' * 40}")
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

        # Configure RTL parameters after reset
        await self.configure_rtl_parameters()

        # Reset GAXI components
        await self.addr_master.reset_bus()
        await self.data_master.reset_bus()
        if self.resp_master:
            await self.resp_master.reset_bus()

        # Reset the interrupt bus components
        if hasattr(self.intrbus_slave, 'set_randomizer'):
            self.intrbus_slave.set_randomizer(FlexRandomizer(self.randomizer_configs['fixed']))

        # Clear specialized monitor stats if needed
        if hasattr(self.intrbus_specialized_monitor, 'reset_stats'):
            self.intrbus_specialized_monitor.reset_stats()

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

    def get_intrbus_stats(self):
        """
        Get interrupt bus statistics from the specialized monitor.

        Returns:
            Dictionary containing interrupt bus statistics
        """
        if hasattr(self.intrbus_specialized_monitor, 'get_stats'):
            return self.intrbus_specialized_monitor.get_stats()
        else:
            # Fallback for basic stats
            return {
                'total_events': len(self.intrbus_events),
                'error_events': len(self.errors_detected)
            }

    def set_intrbus_backpressure(self, config_name='fixed'):
        """
        Set interrupt bus backpressure configuration.

        Args:
            config_name: Configuration name from RANDOMIZER_CONFIGS
        """
        if config_name in self.randomizer_configs:
            if hasattr(self.intrbus_slave, 'set_randomizer'):
                self.intrbus_slave.set_randomizer(
                    FlexRandomizer(self.randomizer_configs[config_name])
                )
            self.log.info(f"Set intrbus backpressure to '{config_name}'{self.get_time_ns_str()}")
        else:
            self.log.warning(f"Unknown backpressure config: {config_name}{self.get_time_ns_str()}")

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

        # Log final interrupt bus statistics
        intrbus_stats = self.get_intrbus_stats()
        self.log.info(f"Final interrupt bus statistics: {intrbus_stats}{self.get_time_ns_str()}")

        if all_passed:
            self.log.info(f"All tests at level {test_level} passed{self.get_time_ns_str()}")
        else:
            self.log.error(f"Some tests at level {test_level} failed{self.get_time_ns_str()}")

        return all_passed
