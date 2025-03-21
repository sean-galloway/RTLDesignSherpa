"""
AXI4 Components for Verification

This package provides components for verifying AXI4 interfaces:
- AXI4 Master
- AXI4 Slave
- AXI4 Monitor
- AXI4 Scoreboard
"""

from CocoTBFramework.components.axi4.axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG,
    AXI4_W_FIELD_CONFIG,
    AXI4_B_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG,
    AXI4_R_FIELD_CONFIG,
    AXI4_MASTER_DEFAULT_CONSTRAINTS,
    AXI4_SLAVE_DEFAULT_CONSTRAINTS,
    adjust_field_configs,
    create_all_signal_maps
)
from CocoTBFramework.components.axi4.axi4_packets import AXI4Packet
from CocoTBFramework.components.axi4.axi4_master import AXI4Master
from CocoTBFramework.components.axi4.axi4_slave import AXI4Slave
from CocoTBFramework.components.axi4.axi4_monitor import AXI4Monitor
from CocoTBFramework.scoreboards.axi4_scoreboard import AXI4Scoreboard, AXI4MemoryScoreboard


def create_axi4_master(dut, title, prefix, clock,
                        id_width=8, addr_width=32, data_width=32, user_width=1,
                        randomizers=None, check_protocol=True, log=None):
    """
    Create an AXI4 Master component.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        id_width: Width of ID fields (default: 8)
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)
        user_width: Width of user fields (default: 1)
        randomizers: Dict of randomizers for each channel (keys: 'aw', 'w', 'ar')
        check_protocol: Enable protocol checking (default: True)
        log: Logger instance

    Returns:
        AXI4Master instance
    """
    # Extract randomizers
    randomizers = randomizers or {}
    aw_randomizer = randomizers.get('aw')
    w_randomizer = randomizers.get('w')
    ar_randomizer = randomizers.get('ar')

    # Create and return master
    return AXI4Master(
        dut, title, prefix, clock,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        aw_randomizer=aw_randomizer,
        w_randomizer=w_randomizer,
        ar_randomizer=ar_randomizer,
        check_protocol=check_protocol,
        log=log
    )


def create_axi4_slave(dut, title, prefix, clock,
                        id_width=8, addr_width=32, data_width=32, user_width=1,
                        memory_model=None, randomizers=None, check_protocol=True,
                        inorder=False, ooo_strategy='random', log=None):
    """
    Create an AXI4 Slave component.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        id_width: Width of ID fields (default: 8)
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)
        user_width: Width of user fields (default: 1)
        memory_model: Memory model for data storage
        randomizers: Dict of randomizers for each channel (keys: 'b', 'r')
        check_protocol: Enable protocol checking (default: True)
        inorder: If True, force in-order responses across different IDs (default: False)
        ooo_strategy: Strategy for out-of-order responses ('random', 'round_robin', 'weighted')
        log: Logger instance

    Returns:
        AXI4Slave instance
    """
    # Create and return slave
    return AXI4Slave(
        dut, title, prefix, clock,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        randomizers=randomizers,
        check_protocol=check_protocol,
        inorder=inorder,
        ooo_strategy=ooo_strategy,
        log=log
    )


def create_axi4_monitor(dut, title, prefix, clock,
                        id_width=8, addr_width=32, data_width=32, user_width=1,
                        is_slave_side=False, check_protocol=True, log=None):
    """
    Create an AXI4 Monitor component.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        id_width: Width of ID fields (default: 8)
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)
        user_width: Width of user fields (default: 1)
        is_slave_side: Whether to monitor slave-side signals (default: False)
        check_protocol: Enable protocol checking (default: True)
        log: Logger instance

    Returns:
        AXI4Monitor instance
    """
    # Create and return monitor
    return AXI4Monitor(
        dut, title, prefix, clock,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        is_slave_side=is_slave_side,
        check_protocol=check_protocol,
        log=log
    )


def create_axi4_scoreboard(name, id_width=8, addr_width=32, data_width=32, user_width=1, log=None):
    """
    Create an AXI4 Scoreboard.

    Args:
        name: Scoreboard name
        id_width: Width of ID fields (default: 8)
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)
        user_width: Width of user fields (default: 1)
        log: Logger instance

    Returns:
        AXI4Scoreboard instance
    """
    # Create and return scoreboard
    return AXI4Scoreboard(
        name,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        log=log
    )


def create_axi4_memory_scoreboard(name, memory_model, id_width=8, addr_width=32, data_width=32, user_width=1, log=None):
    """
    Create an AXI4 Memory Scoreboard.

    Args:
        name: Scoreboard name
        memory_model: Memory model for verification
        id_width: Width of ID fields (default: 8)
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)
        user_width: Width of user fields (default: 1)
        log: Logger instance

    Returns:
        AXI4MemoryScoreboard instance
    """
    # Create and return memory scoreboard
    return AXI4MemoryScoreboard(
        name,
        memory_model,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        log=log
    )


def create_axi4_components(dut, title, prefix, clock,
                            id_width=8, addr_width=32, data_width=32, user_width=1,
                            memory_model=None, randomizers=None, check_protocol=True,
                            inorder=False, ooo_strategy='random', log=None):
    """
    Create a complete set of AXI4 components.

    Args:
        dut: Device under test
        title: Base component title
        prefix: Signal prefix
        clock: Clock signal
        id_width: Width of ID fields (default: 8)
        addr_width: Width of address fields (default: 32)
        data_width: Width of data fields (default: 32)
        user_width: Width of user fields (default: 1)
        memory_model: Memory model for data storage
        randomizers: Dict of randomizers
        check_protocol: Enable protocol checking (default: True)
        inorder: Force in-order responses for the slave (default: False)
        ooo_strategy: Out-of-order strategy for the slave
        log: Logger instance

    Returns:
        Dict of components:
        {
            'master': AXI4Master,
            'slave': AXI4Slave,
            'master_monitor': AXI4Monitor,
            'slave_monitor': AXI4Monitor,
            'scoreboard': AXI4Scoreboard
        }
    """
    # Create master
    master = create_axi4_master(
        dut, f"{title}_Master", prefix, clock,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        randomizers=randomizers,
        check_protocol=check_protocol,
        log=log
    )

    # Create slave
    slave = create_axi4_slave(
        dut, f"{title}_Slave", prefix, clock,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        randomizers=randomizers,
        check_protocol=check_protocol,
        inorder=inorder,
        ooo_strategy=ooo_strategy,
        log=log
    )

    # Create monitors
    master_monitor = create_axi4_monitor(
        dut, f"{title}_Master_Monitor", prefix, clock,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        is_slave_side=False,
        check_protocol=check_protocol,
        log=log
    )

    slave_monitor = create_axi4_monitor(
        dut, f"{title}_Slave_Monitor", prefix, clock,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        is_slave_side=True,
        check_protocol=check_protocol,
        log=log
    )

    # Create scoreboard
    scoreboard = create_axi4_scoreboard(
        f"{title}_Scoreboard",
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        log=log
    )

    # Connect monitors to scoreboard
    master_monitor.set_write_callback(scoreboard._handle_master_write)
    master_monitor.set_read_callback(scoreboard._handle_master_read)
    slave_monitor.set_write_callback(scoreboard._handle_slave_write)
    slave_monitor.set_read_callback(scoreboard._handle_slave_read)

    # Return all components
    return {
        'master': master,
        'slave': slave,
        'master_monitor': master_monitor,
        'slave_monitor': slave_monitor,
        'scoreboard': scoreboard
    }
