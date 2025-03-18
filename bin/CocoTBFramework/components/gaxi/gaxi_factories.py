"""
Factory functions for creating and configuring GAXI components
"""
from CocoTBFramework.components.gaxi.gaxi_components import GAXIMaster, GAXISlave, GAXIMonitor
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.gaxi.gaxi_enhancements import EnhancedGAXIMaster, EnhancedGAXISlave
from scoreboards.gaxi_scoreboard import GAXIScoreboard

# Default field configuration for GAXI components
DEFAULT_FIELD_CONFIG = {
    'data': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data value'
    }
}

# Command-response field configuration for GAXI components
COMMAND_FIELD_CONFIG = {
    'cmd': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Command (0=Read, 1=Write)'
    },
    'addr': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Address'
    },
    'data': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data'
    },
    'strb': {
        'bits': 4,
        'default': 0xF,
        'format': 'bin',
        'display_width': 4,
        'active_bits': (3, 0),
        'description': 'Byte strobe'
    },
    'ack': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Acknowledge'
    }
}


def create_gaxi_master(dut, title, prefix, clock, field_config=None,
                        randomizer=None, enhanced=False, memory_model=None,
                        memory_fields=None, log=None, signal_map=None,
                        optional_signal_map=None):
    """
    Create a GAXI Master component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        randomizer: Timing randomizer
        enhanced: If True, create an EnhancedGAXIMaster (default: False)
        memory_model: Memory model for enhanced master
        memory_fields: Field mapping for memory operations
        log: Logger instance (default: dut's logger)
        signal_map: Signal mapping for multi-signal mode
        optional_signal_map: Optional signal mapping

    Returns:
        GAXIMaster or EnhancedGAXIMaster instance
    """
    # Use default field config if none provided
    field_config = field_config or DEFAULT_FIELD_CONFIG.copy()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create base master
    master = GAXIMaster(
        dut, title, prefix, clock,
        field_config=field_config,
        randomizer=randomizer,
        memory_model=memory_model,
        memory_fields=memory_fields,
        log=log,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    # Create enhanced master if requested
    return EnhancedGAXIMaster(master, log=log) if enhanced else master


def create_gaxi_slave(dut, title, prefix, clock, field_config=None,
                        randomizer=None, enhanced=False, memory_model=None,
                        memory_fields=None, log=None, mode='skid',
                        signal_map=None, optional_signal_map=None):
    """
    Create a GAXI Slave component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        randomizer: Timing randomizer
        enhanced: If True, create an EnhancedGAXISlave (default: False)
        memory_model: Memory model for enhanced slave
        memory_fields: Field mapping for memory operations
        log: Logger instance (default: dut's logger)
        mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
        signal_map: Signal mapping for multi-signal mode
        optional_signal_map: Optional signal mapping

    Returns:
        GAXISlave or EnhancedGAXISlave instance
    """
    # Use default field config if none provided
    field_config = field_config or DEFAULT_FIELD_CONFIG.copy()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create base slave
    slave = GAXISlave(
        dut, title, prefix, clock,
        field_config=field_config,
        randomizer=randomizer,
        memory_model=memory_model,
        memory_fields=memory_fields,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    # Create enhanced slave if requested
    if enhanced:
        return EnhancedGAXISlave(slave, memory_model=memory_model, log=log)

    return slave


def create_gaxi_monitor(dut, title, prefix, clock, field_config=None,
                        is_slave=False, log=None, mode='skid',
                        signal_map=None, optional_signal_map=None):
    """
    Create a GAXI Monitor component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        is_slave: If True, monitor slave side; if False, monitor master side
        log: Logger instance (default: dut's logger)
        mode: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
        signal_map: Signal mapping for multi-signal mode
        optional_signal_map: Optional signal mapping

    Returns:
        GAXIMonitor instance
    """
    # Use default field config if none provided
    field_config = field_config or DEFAULT_FIELD_CONFIG.copy()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create monitor
    return GAXIMonitor(
        dut, title, prefix, clock,
        field_config=field_config,
        is_slave=is_slave,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )


def create_gaxi_scoreboard(name, field_config=None, log=None):
    """
    Create a GAXI Scoreboard with configuration.

    Args:
        name: Scoreboard name
        field_config: Field configuration for packets (default: standard data field)
        log: Logger instance

    Returns:
        GAXIScoreboard instance
    """
    # Use default field config if none provided
    field_config = field_config or DEFAULT_FIELD_CONFIG.copy()

    # Create scoreboard
    return GAXIScoreboard(name, field_config, log=log)


def create_gaxi_components(dut, clock, title_prefix="", field_config=None,
                            enhanced=False, memory_model=None, log=None,
                            mode='skid', signal_map=None, optional_signal_map=None):
    """
    Create a complete set of GAXI components (master, slave, monitors, scoreboard).

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        field_config: Field configuration for packets (default: standard data field)
        enhanced: If True, create enhanced master/slave components
        memory_model: Memory model for enhanced components
        log: Logger instance
        mode: Operating mode for slave/monitor
        signal_map: Signal mapping for multi-signal mode
        optional_signal_map: Optional signal mapping

    Returns:
        Dictionary containing all created components
    """
    # Use default field config if none provided
    field_config = field_config or DEFAULT_FIELD_CONFIG.copy()

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create memory model if needed but not provided
    if enhanced and memory_model is None:
        memory_model = MemoryModel(
            num_lines=1024,
            bytes_per_line=4,  # 32-bit default
            log=log
        )

    # Create components
    master = create_gaxi_master(
        dut, f"{title_prefix}Master", "", clock,
        field_config=field_config,
        enhanced=enhanced,
        memory_model=memory_model,
        log=log,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    slave = create_gaxi_slave(
        dut, f"{title_prefix}Slave", "", clock,
        field_config=field_config,
        enhanced=enhanced,
        memory_model=memory_model,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    master_monitor = create_gaxi_monitor(
        dut, f"{title_prefix}MasterMonitor", "", clock,
        field_config=field_config,
        is_slave=False,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    slave_monitor = create_gaxi_monitor(
        dut, f"{title_prefix}SlaveMonitor", "", clock,
        field_config=field_config,
        is_slave=True,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map
    )

    scoreboard = create_gaxi_scoreboard(
        f"{title_prefix}Scoreboard",
        field_config=field_config,
        log=log
    )

    # Start enhanced slave processor if applicable
    if enhanced and hasattr(slave, 'start_processor'):
        slave.start_processor()

    # Return all components
    return {
        'master': master,
        'slave': slave,
        'master_monitor': master_monitor,
        'slave_monitor': slave_monitor,
        'scoreboard': scoreboard,
        'memory_model': memory_model
    }


def get_command_response_field_config(addr_width=32, data_width=32):
    """
    Get field configuration for command-response protocol.

    Args:
        addr_width: Address width in bits
        data_width: Data width in bits

    Returns:
        Field configuration dictionary for command-response protocol
    """
    # Copy base configuration
    config = COMMAND_FIELD_CONFIG.copy()

    # Update widths
    config['addr']['bits'] = addr_width
    config['addr']['active_bits'] = (addr_width-1, 0)

    config['data']['bits'] = data_width
    config['data']['active_bits'] = (data_width-1, 0)

    # Update strobe width
    strb_width = data_width // 8
    config['strb']['bits'] = strb_width
    config['strb']['active_bits'] = (strb_width-1, 0)

    return config
