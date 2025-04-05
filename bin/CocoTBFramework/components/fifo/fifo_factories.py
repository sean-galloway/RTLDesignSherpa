"""
Factory functions for creating and configuring FIFO components
"""
from CocoTBFramework.components.fifo.fifo_master import FIFOMaster
from CocoTBFramework.components.fifo.fifo_slave import FIFOSlave
from CocoTBFramework.components.fifo.fifo_monitor import FIFOMonitor
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.scoreboards.fifo_scoreboard import FIFOScoreboard
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# Default field configuration for FIFO components
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

# Standard FIFO signal maps
DEFAULT_MASTER_SIGNAL_MAP = {
    'i_write': 'i_write',
    'o_wr_full': 'o_wr_full'
}

DEFAULT_MASTER_OPTIONAL_SIGNAL_MAP = {
    'i_wr_data': 'i_wr_data'
}

DEFAULT_SLAVE_SIGNAL_MAP = {
    'o_rd_empty': 'o_rd_empty',
    'i_read': 'i_read'
}

DEFAULT_SLAVE_OPTIONAL_SIGNAL_MAP = {
    'o_rd_data': 'o_rd_data'
}

DEFAULT_SLAVE_MUX_OPTIONAL_SIGNAL_MAP = {
    'o_rd_data': 'ow_rd_data'
}


def get_default_field_config(data_width=32, addr_width=0, ctrl_width=0):
    """
    Get default field configuration for FIFO packets.

    Args:
        data_width: Data width in bits
        addr_width: Address width in bits (0 to exclude)
        ctrl_width: Control width in bits (0 to exclude)

    Returns:
        Field configuration dictionary or FieldConfig object
    """
    # Start with data-only configuration
    config = FieldConfig()

    # Add data field first
    config.add_field(FieldDefinition(
        name='data',
        bits=data_width,
        default=0,
        format='hex',
        display_width=(data_width + 3) // 4,
        active_bits=(data_width-1, 0),
        description='Data value'
    ))

    # Add address field if requested
    if addr_width > 0:
        config.add_field(FieldDefinition(
            name='addr',
            bits=addr_width,
            default=0,
            format='hex',
            display_width=(addr_width + 3) // 4,
            active_bits=(addr_width-1, 0),
            description='Address'
        ))

    # Add control field if requested
    if ctrl_width > 0:
        config.add_field(FieldDefinition(
            name='ctrl',
            bits=ctrl_width,
            default=0,
            format='hex',
            display_width=(ctrl_width + 3) // 4,
            active_bits=(ctrl_width-1, 0),
            description='Control'
        ))

    return config


def create_fifo_master(dut, title, prefix, clock, field_config=None,
                       randomizer=None, memory_model=None,
                       memory_fields=None, log=None, signal_map=None,
                       optional_signal_map=None, multi_sig=False):
    """
    Create a FIFO Master component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        randomizer: Timing randomizer
        memory_model: Memory model for data storage
        memory_fields: Field mapping for memory operations
        log: Logger instance (default: dut's logger)
        signal_map: Signal mapping for FIFO signals
        optional_signal_map: Optional signal mapping for data signals
        multi_sig: Whether to use multi-signal mode (separate signals for fields)

    Returns:
        FIFOMaster instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Use default signal maps if none provided
    signal_map = signal_map or DEFAULT_MASTER_SIGNAL_MAP
    optional_signal_map = optional_signal_map or DEFAULT_MASTER_OPTIONAL_SIGNAL_MAP

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create master
    return FIFOMaster(
        dut, title, prefix, clock,
        field_config=field_config,
        randomizer=randomizer,
        memory_model=memory_model,
        memory_fields=memory_fields,
        log=log,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )


def create_fifo_slave(dut, title, prefix, clock, field_config=None,
                      randomizer=None, memory_model=None,
                      memory_fields=None, log=None, mode='fifo_mux',
                      signal_map=None, optional_signal_map=None, multi_sig=False):
    """
    Create a FIFO Slave component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        randomizer: Timing randomizer
        memory_model: Memory model for data storage
        memory_fields: Field mapping for memory operations
        log: Logger instance (default: dut's logger)
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        signal_map: Signal mapping for FIFO signals
        optional_signal_map: Optional signal mapping for data signals
        multi_sig: Whether to use multi-signal mode (separate signals for fields)

    Returns:
        FIFOSlave instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Use default signal maps if none provided
    signal_map = signal_map or DEFAULT_SLAVE_SIGNAL_MAP

    # If no optional_signal_map provided, select based on mode
    if optional_signal_map is None:
        if mode == 'fifo_mux':
            optional_signal_map = DEFAULT_SLAVE_MUX_OPTIONAL_SIGNAL_MAP
        else:
            optional_signal_map = DEFAULT_SLAVE_OPTIONAL_SIGNAL_MAP

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create slave
    return FIFOSlave(
        dut, title, prefix, clock,
        field_config=field_config,
        randomizer=randomizer,
        memory_model=memory_model,
        memory_fields=memory_fields,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )


def create_fifo_monitor(dut, title, prefix, clock, field_config=None,
                        is_slave=False, log=None, mode='fifo_mux',
                        signal_map=None, optional_signal_map=None, multi_sig=False):
    """
    Create a FIFO Monitor component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets (default: standard data field)
        is_slave: If True, monitor read side; if False, monitor write side
        log: Logger instance (default: dut's logger)
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        signal_map: Signal mapping for FIFO signals
        optional_signal_map: Optional signal mapping for data signals
        multi_sig: Whether to use multi-signal mode (separate signals for fields)

    Returns:
        FIFOMonitor instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Use default signal maps based on whether monitoring read or write port
    if signal_map is None:
        if is_slave:
            signal_map = DEFAULT_SLAVE_SIGNAL_MAP
        else:
            signal_map = DEFAULT_MASTER_SIGNAL_MAP

    # If no optional_signal_map provided, select based on mode and port
    if optional_signal_map is None:
        if is_slave:
            if mode == 'fifo_mux':
                optional_signal_map = DEFAULT_SLAVE_MUX_OPTIONAL_SIGNAL_MAP
            else:
                optional_signal_map = DEFAULT_SLAVE_OPTIONAL_SIGNAL_MAP
        else:
            optional_signal_map = DEFAULT_MASTER_OPTIONAL_SIGNAL_MAP

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create monitor
    return FIFOMonitor(
        dut, title, prefix, clock,
        field_config=field_config,
        is_slave=is_slave,
        log=log,
        mode=mode,
        signal_map=signal_map,
        optional_signal_map=optional_signal_map,
        multi_sig=multi_sig
    )


def create_fifo_scoreboard(name, field_config=None, log=None):
    """
    Create a FIFO Scoreboard with configuration.

    Args:
        name: Scoreboard name
        field_config: Field configuration for packets (default: standard data field)
        log: Logger instance

    Returns:
        FIFOScoreboard instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        # Convert dictionary to FieldConfig if needed
        field_config = FieldConfig.validate_and_create(field_config)

    # Create scoreboard
    return FIFOScoreboard(name, field_config, log=log)


def create_fifo_components(dut, clock, title_prefix="", field_config=None,
                           memory_model=None, log=None, mode='fifo_mux',
                           master_signal_map=None, master_optional_signal_map=None,
                           slave_signal_map=None, slave_optional_signal_map=None,
                           multi_sig=False):
    """
    Create a complete set of FIFO components (master, slave, monitors, scoreboard).

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        field_config: Field configuration for packets (default: standard data field)
        memory_model: Memory model for data storage
        log: Logger instance
        mode: Operating mode for slave/monitor
        master_signal_map: Signal mapping for master port
        master_optional_signal_map: Optional signal mapping for master port
        slave_signal_map: Signal mapping for slave port
        slave_optional_signal_map: Optional signal mapping for slave port
        multi_sig: Whether to use multi-signal mode

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

    # Use default signal maps if none provided
    master_signal_map = master_signal_map or DEFAULT_MASTER_SIGNAL_MAP
    master_optional_signal_map = master_optional_signal_map or DEFAULT_MASTER_OPTIONAL_SIGNAL_MAP
    slave_signal_map = slave_signal_map or DEFAULT_SLAVE_SIGNAL_MAP

    # Select slave optional signal map based on mode if not provided
    if slave_optional_signal_map is None:
        if mode == 'fifo_mux':
            slave_optional_signal_map = DEFAULT_SLAVE_MUX_OPTIONAL_SIGNAL_MAP
        else:
            slave_optional_signal_map = DEFAULT_SLAVE_OPTIONAL_SIGNAL_MAP

    # Create components
    master = create_fifo_master(
        dut, f"{title_prefix}Master", "", clock,
        field_config=field_config,
        memory_model=memory_model,
        log=log,
        signal_map=master_signal_map,
        optional_signal_map=master_optional_signal_map,
        multi_sig=multi_sig
    )

    slave = create_fifo_slave(
        dut, f"{title_prefix}Slave", "", clock,
        field_config=field_config,
        memory_model=memory_model,
        log=log,
        mode=mode,
        signal_map=slave_signal_map,
        optional_signal_map=slave_optional_signal_map,
        multi_sig=multi_sig
    )

    master_monitor = create_fifo_monitor(
        dut, f"{title_prefix}MasterMonitor", "", clock,
        field_config=field_config,
        is_slave=False,
        log=log,
        mode=mode,
        signal_map=master_signal_map,
        optional_signal_map=master_optional_signal_map,
        multi_sig=multi_sig
    )

    slave_monitor = create_fifo_monitor(
        dut, f"{title_prefix}SlaveMonitor", "", clock,
        field_config=field_config,
        is_slave=True,
        log=log,
        mode=mode,
        signal_map=slave_signal_map,
        optional_signal_map=slave_optional_signal_map,
        multi_sig=multi_sig
    )

    scoreboard = create_fifo_scoreboard(
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
