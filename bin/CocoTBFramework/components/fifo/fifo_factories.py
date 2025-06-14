"""
Simplified factory functions for creating FIFO components

Leverages modern infrastructure (SignalResolver, FieldConfig, etc.)
to provide clean component creation with minimal configuration needed.
"""
from ..memory_model import MemoryModel
from ..field_config import FieldConfig
from CocoTBFramework.scoreboards.fifo_scoreboard import FIFOScoreboard
from .fifo_master import FIFOMaster
from .fifo_slave import FIFOSlave
from .fifo_monitor import FIFOMonitor
from .fifo_command_handler import FIFOCommandHandler


def get_default_field_config(data_width=32, addr_width=0, ctrl_width=0):
    """
    Get default field configuration for FIFO packets using existing factory methods.

    Args:
        data_width: Data width in bits
        addr_width: Address width in bits (0 to exclude)
        ctrl_width: Control width in bits (0 to exclude)

    Returns:
        FieldConfig object with specified fields
    """
    # Use existing FieldConfig factory methods instead of manual creation
    if addr_width > 0 and ctrl_width > 0:
        # Multi-field configuration with addr, ctrl, and data
        return FieldConfig.create_multi_data(
            addr_width=addr_width, 
            ctrl_width=ctrl_width, 
            data_width=data_width, 
            num_data=1
        )
    elif addr_width > 0:
        # Standard addr + data configuration
        return FieldConfig.create_standard(addr_width, data_width)
    else:
        # Simple data-only configuration
        return FieldConfig.create_data_only(data_width)


def create_fifo_master(dut, title, clock, field_config=None, randomizer=None, 
                       memory_model=None, log=None, **kwargs):
    """
    Create a FIFO Master component with minimal configuration.

    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        field_config: Field configuration (default: 32-bit data field)
        randomizer: Timing randomizer (optional)
        memory_model: Memory model for data storage (optional)
        log: Logger instance (optional)
        **kwargs: Additional arguments passed to FIFOMaster

    Returns:
        FIFOMaster instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create master - SignalResolver handles signal discovery automatically
    master = FIFOMaster(
        dut=dut,
        title=title,
        prefix="",  # Let SignalResolver handle this
        clock=clock,
        field_config=field_config,
        randomizer=randomizer,
        log=log,
        **kwargs
    )
    
    # Attach memory model if provided - use existing MemoryModel directly
    if memory_model:
        master.memory_model = memory_model
    
    return master


def create_fifo_slave(dut, title, clock, field_config=None, randomizer=None,
                      memory_model=None, log=None, mode='fifo_mux', **kwargs):
    """
    Create a FIFO Slave component with minimal configuration.

    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        field_config: Field configuration (default: 32-bit data field)
        randomizer: Timing randomizer (optional)
        memory_model: Memory model for data storage (optional)
        log: Logger instance (optional)
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        **kwargs: Additional arguments passed to FIFOSlave

    Returns:
        FIFOSlave instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create slave - SignalResolver handles signal discovery automatically
    slave = FIFOSlave(
        dut=dut,
        title=title,
        prefix="",  # Let SignalResolver handle this
        clock=clock,
        field_config=field_config,
        randomizer=randomizer,
        log=log,
        mode=mode,
        **kwargs
    )
    
    # Attach memory model if provided - use existing MemoryModel directly
    if memory_model:
        slave.memory_model = memory_model
    
    return slave


def create_fifo_monitor(dut, title, clock, field_config=None, is_slave=False,
                        log=None, mode='fifo_mux', **kwargs):
    """
    Create a FIFO Monitor component with minimal configuration.

    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        field_config: Field configuration (default: 32-bit data field)
        is_slave: If True, monitor read side; if False, monitor write side
        log: Logger instance (optional)
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        **kwargs: Additional arguments passed to FIFOMonitor

    Returns:
        FIFOMonitor instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create monitor - SignalResolver handles signal discovery automatically
    return FIFOMonitor(
        dut=dut,
        title=title,
        prefix="",  # Let SignalResolver handle this
        clock=clock,
        field_config=field_config,
        is_slave=is_slave,
        log=log,
        mode=mode,
        **kwargs
    )


def create_fifo_scoreboard(name, field_config=None, log=None):
    """
    Create a FIFO Scoreboard with configuration.

    Args:
        name: Scoreboard name
        field_config: Field configuration (default: 32-bit data field)
        log: Logger instance

    Returns:
        FIFOScoreboard instance
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        field_config = FieldConfig.validate_and_create(field_config)

    return FIFOScoreboard(name, field_config, log=log)


def create_fifo_command_handler(master, slave, log=None):
    """
    Create a FIFO Command Handler for managing transaction dependencies.

    Args:
        master: FIFOMaster instance
        slave: FIFOSlave instance
        log: Logger instance

    Returns:
        FIFOCommandHandler instance
    """
    # Use master's or slave's logger if none provided
    log = log or getattr(master, 'log', None) or getattr(slave, 'log', None)

    return FIFOCommandHandler(master, slave, log=log)


def create_memory_model(num_lines, bytes_per_line=4, log=None, preset_values=None, debug=False):
    """
    Create a memory model with diagnostics using existing MemoryModel infrastructure.

    Args:
        num_lines: Number of memory lines
        bytes_per_line: Bytes per memory line
        log: Logger instance
        preset_values: Optional initial values for memory
        debug: Enable detailed debug logging

    Returns:
        MemoryModel instance (using existing infrastructure)
    """
    return MemoryModel(
        num_lines=num_lines,
        bytes_per_line=bytes_per_line,
        log=log,
        preset_values=preset_values,
        debug=debug
    )


def create_fifo_components(dut, clock, title_prefix="", field_config=None,
                           memory_model=None, log=None, mode='fifo_mux',
                           fifo_capacity=8):
    """
    Create a complete set of FIFO components with minimal configuration.

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        field_config: Field configuration (default: 32-bit data field)
        memory_model: Memory model for data storage (optional)
        log: Logger instance
        mode: Operating mode for slave/monitor
        fifo_capacity: FIFO capacity in entries for modeling

    Returns:
        Dictionary containing all created components
    """
    # Use default field config if none provided
    if field_config is None:
        field_config = get_default_field_config()
    elif isinstance(field_config, dict):
        field_config = FieldConfig.validate_and_create(field_config)

    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create memory model if needed but not provided - use existing MemoryModel
    if memory_model is None:
        memory_model = create_memory_model(
            num_lines=fifo_capacity,
            bytes_per_line=4,  # 32-bit default
            log=log
        )

    # Create components - simplified creation with SignalResolver handling details
    master = create_fifo_master(
        dut, f"{title_prefix}Master", clock,
        field_config=field_config,
        memory_model=memory_model,
        log=log
    )

    slave = create_fifo_slave(
        dut, f"{title_prefix}Slave", clock,
        field_config=field_config,
        memory_model=memory_model,
        log=log,
        mode=mode
    )

    master_monitor = create_fifo_monitor(
        dut, f"{title_prefix}MasterMonitor", clock,
        field_config=field_config,
        is_slave=False,
        log=log,
        mode=mode
    )

    slave_monitor = create_fifo_monitor(
        dut, f"{title_prefix}SlaveMonitor", clock,
        field_config=field_config,
        is_slave=True,
        log=log,
        mode=mode
    )

    scoreboard = create_fifo_scoreboard(
        f"{title_prefix}Scoreboard",
        field_config=field_config,
        log=log
    )

    command_handler = create_fifo_command_handler(
        master,
        slave,
        log=log
    )

    # Return all components
    return {
        'master': master,
        'slave': slave,
        'master_monitor': master_monitor,
        'slave_monitor': slave_monitor,
        'scoreboard': scoreboard,
        'command_handler': command_handler,
        'memory_model': memory_model
    }


# Convenience functions for common configurations
def create_simple_fifo_test(dut, clock, data_width=32):
    """
    Create a simple FIFO test setup with standard components.

    Args:
        dut: Device under test
        clock: Clock signal
        data_width: Data width in bits

    Returns:
        Dictionary with master, slave, and command_handler
    """
    field_config = get_default_field_config(data_width=data_width)
    
    master = create_fifo_master(dut, "Master", clock, field_config=field_config)
    slave = create_fifo_slave(dut, "Slave", clock, field_config=field_config)
    command_handler = create_fifo_command_handler(master, slave)
    
    return {
        'master': master,
        'slave': slave,
        'command_handler': command_handler
    }


def create_fifo_with_monitors(dut, clock, data_width=32, mode='fifo_mux'):
    """
    Create FIFO components with monitors for comprehensive observation.

    Args:
        dut: Device under test
        clock: Clock signal
        data_width: Data width in bits
        mode: Operating mode

    Returns:
        Dictionary with all components including monitors
    """
    return create_fifo_components(
        dut=dut,
        clock=clock,
        field_config=get_default_field_config(data_width=data_width),
        mode=mode
    )