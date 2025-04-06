"""
Factory functions for creating and configuring GAXI components
"""
from ..memory_model import MemoryModel
from ..field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard


def get_default_field_config(data_width=32):
    """
    Get field configuration for command-response protocol.

    Args:
        data_width: Data width in bits

    Returns:
        FieldConfig object for command-response protocol
    """
    # Create a new field configuration
    config = FieldConfig()
    
    # Add data field
    config.add_field_dict('data', {
        'bits': data_width,
        'default': 0,
        'format': 'hex',
        'display_width': data_width // 4,
        'active_bits': (data_width-1, 0),
        'description': 'Data value'
    })
    
    return config


def create_gaxi_master(dut, title, prefix, clock, field_config=None,
                        randomizer=None, memory_model=None,
                        memory_fields=None, log=None, signal_map=None,
                        optional_signal_map=None, field_mode=False, multi_sig=False):
    """
    Create a GAXI Master component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        randomizer: Timing randomizer
        memory_model: Memory model for enhanced master
        memory_fields: Field mapping for memory operations
        log: Logger instance (default: dut's logger)
        signal_map: Signal mapping for multi-signal mode
        optional_signal_map: Optional signal mapping

    Returns:
        GAXIMaster or EnhancedGAXIMaster instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    return GAXIMaster(
        dut,
        title,
        prefix,
        clock,
        field_config=field_config,
        field_mode=field_mode,
        randomizer=randomizer,
        memory_model=memory_model,
        memory_fields=memory_fields,
        log=log,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig,
    )


def create_gaxi_slave(dut, title, prefix, clock, field_config=None, field_mode=False,
                        randomizer=None, memory_model=None,
                        memory_fields=None, log=None, mode='skid',
                        signal_map=None, optional_signal_map=None, multi_sig=False):
    """
    Create a GAXI Slave component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        randomizer: Timing randomizer
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
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create base slave
    return  GAXISlave(
        dut, title, prefix, clock,
        field_config=field_config,
        field_mode=field_mode,
        randomizer=randomizer,
        memory_model=memory_model,
        memory_fields=memory_fields,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )


def create_gaxi_monitor(dut, title, prefix, clock, field_config=None, field_mode=False,
                        is_slave=False, log=None, mode='skid',
                        signal_map=None, optional_signal_map=None, multi_sig=False):
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
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create monitor
    return GAXIMonitor(
        dut, title, prefix, clock,
        field_config=field_config,
        field_mode=field_mode,
        is_slave=is_slave,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
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
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Create scoreboard
    return GAXIScoreboard(name, field_config, log=log)


def create_gaxi_components(dut, clock, title_prefix="", field_config=None, field_mode=False,
                            memory_model=None, log=None,
                            mode='skid', signal_map=None, optional_signal_map=None, multi_sig=False):
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
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create memory model if needed but not provided
    if memory_model is None:
        memory_model = MemoryModel(
            num_lines=1024,
            bytes_per_line=4,  # 32-bit default
            log=log
        )

    # Create components
    master = create_gaxi_master(
        dut, f"{title_prefix}Master", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        memory_model=memory_model,
        log=log,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )

    slave = create_gaxi_slave(
        dut, f"{title_prefix}Slave", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        memory_model=memory_model,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )

    master_monitor = create_gaxi_monitor(
        dut, f"{title_prefix}MasterMonitor", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        is_slave=False,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )

    slave_monitor = create_gaxi_monitor(
        dut, f"{title_prefix}SlaveMonitor", "", clock,
        field_config=field_config,
        field_mode=field_mode,
        is_slave=True,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )

    scoreboard = create_gaxi_scoreboard(
        f"{title_prefix}Scoreboard",
        field_config=field_config,
        log=log
    )

    # Return all components
    return {
        'master': master,
        'slave': slave,
        'master_monitor': master_monitor,
        'slave_monitor': slave_monitor,
        'scoreboard': scoreboard,
        'memory_model': memory_model
    }
