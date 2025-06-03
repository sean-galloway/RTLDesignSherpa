"""
AXI4 Components for Verification

This package provides components for verifying AXI4 interfaces:
- AXI4 Master
- AXI4 Slave
- AXI4 Monitor
- AXI4 Scoreboard
"""
import cocotb
from .axi4_master import AXI4Master
from .axi4_slave import AXI4Slave
from .axi4_monitor import AXI4Monitor
from .axi4_packet import AXI4Packet
from CocoTBFramework.scoreboards.axi4_scoreboard import AXI4Scoreboard, AXI4MemoryScoreboard
from ..field_config import FieldConfig, FieldDefinition
from ..flex_randomizer import FlexRandomizer

from .axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG, AXI4_W_FIELD_CONFIG, AXI4_B_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG, AXI4_R_FIELD_CONFIG,
    adjust_field_configs
)


def create_axi4_master(dut, title, prefix, divider, suffix, clock, channels,
                        id_width=8, addr_width=32, data_width=32, user_width=1,
                        randomizers=None, check_protocol=True, log=None):
    """
    Create an AXI4 Master component.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        divider: used if there is an '_' between the channel and the signal
        suffix: optional suffix useed at the end
        clock: Clock signal
        channels: a list of the channels to instantiate
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

    # Create field configs dictionary for adjustment
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust field configs based on specified widths
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    # Create master with explicit callback registration (callbacks registered in constructor)
    master = AXI4Master(
        dut, title, prefix, divider, suffix, clock, channels,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        field_configs=adjusted_configs,
        aw_randomizer=aw_randomizer,
        w_randomizer=w_randomizer,
        ar_randomizer=ar_randomizer,
        check_protocol=check_protocol,
        log=log
    )

    # # Explicitly register callbacks again to ensure they're connected
    # master._register_callbacks()

    # # Log successful creation with callback registration info
    # if log:
    #     if 'R' in channels and hasattr(master, 'r_slave'):
    #         callback_count = len(getattr(master.r_slave, 'callbacks', []))
    #         log.debug(f"AXI4Master '{title}' created with {callback_count} R callbacks registered")
    #     if 'B' in channels and hasattr(master, 'b_slave'):
    #         callback_count = len(getattr(master.b_slave, 'callbacks', []))
    #         log.debug(f"AXI4Master '{title}' created with {callback_count} B callbacks registered")

    return master

def create_axi4_slave(dut, title, prefix, divider, suffix, clock, channels,
                        id_width=8, addr_width=32, data_width=32, user_width=1,
                        memory_model=None, randomizers=None, check_protocol=True,
                        inorder=False, ooo_strategy='random', log=None):
    """
    Create an AXI4 Slave component.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        divider: used if there is an '_' between the channel and the signal
        suffix: optional suffix useed at the end
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
    # Create field configs dictionary for adjustment
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust field configs based on specified widths
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    return AXI4Slave(
        dut,
        title,
        prefix,
        divider,
        suffix,
        clock,
        channels,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        field_configs=adjusted_configs,
        memory_model=memory_model,
        randomizers=randomizers,
        check_protocol=check_protocol,
        inorder=inorder,
        ooo_strategy=ooo_strategy,
        log=log,
    )


def create_axi4_monitor(dut, title, prefix, divider, suffix, clock, channels,
                        id_width=8, addr_width=32, data_width=32, user_width=1,
                        is_slave_side=False, check_protocol=True, log=None):
    """
    Create an AXI4 Monitor component.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        divider: used if there is an '_' between the channel and the signal
        suffix: optional suffix useed at the end
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
    # Create field configs dictionary for adjustment
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust field configs based on specified widths
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    # Create and return monitor
    return AXI4Monitor(
        dut, title, prefix, divider, suffix, clock, channels,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        field_configs=adjusted_configs,
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
    # Create field configs dictionary for adjustment
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust field configs based on specified widths
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    # Create and return scoreboard
    return AXI4Scoreboard(
        name,
        field_configs=adjusted_configs,
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
    # Create field configs dictionary for adjustment
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust field configs based on specified widths
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    # Create and return memory scoreboard
    return AXI4MemoryScoreboard(
        name,
        memory_model,
        field_configs=adjusted_configs,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        log=log
    )
