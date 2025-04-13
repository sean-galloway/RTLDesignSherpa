"""
AXI4 Specialized Factory Functions

This module provides specialized factory functions for common AXI4 use cases,
simplifying the setup of AXI4 components by providing optimized defaults
and hiding unnecessary complexity.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from .axi4_factory import (
    create_axi4_master,
    create_axi4_slave,
    create_axi4_monitor,
    create_axi4_scoreboard,
    create_axi4_memory_scoreboard
)
from .axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG, AXI4_W_FIELD_CONFIG, AXI4_B_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG, AXI4_R_FIELD_CONFIG,
    adjust_field_configs
)
from .axi4_seq_transaction import AXI4TransactionSequence
from .axi4_extensions import create_axi4_extension_handlers
from .axi4_randomization_config import AXI4RandomizationConfig


def create_simple_axi4_master(dut, title, prefix, clock, data_width=32, log=None):
    """
    Create a basic AXI4 master for simple testing scenarios.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        data_width: Width of data in bits (default: 32)
        log: Logger instance

    Returns:
        AXI4Master instance configured for simple testing
    """
    # Set sensible defaults
    id_width = 4  # Simplified ID space
    addr_width = 32
    user_width = 1
    divider = "_"
    suffix = ""
    channels = ["AW", "W", "B", "AR", "R"]  # All channels

    # Create field configs with adjusted widths
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust for data width
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    # Create and return master with default randomizers
    return create_axi4_master(
        dut, title, prefix, divider, suffix, clock, channels,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        field_configs=adjusted_configs,
        check_protocol=True,  # Enable protocol checking by default
        log=log
    )


def create_memory_axi4_slave(dut, title, prefix, clock, memory_model, data_width=32, log=None):
    """
    Create an AXI4 slave specifically configured for memory operations.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        memory_model: Memory model for data storage
        data_width: Width of data in bits (default: 32)
        log: Logger instance

    Returns:
        AXI4Slave instance configured for memory operations
    """
    # Set sensible defaults
    id_width = 4
    addr_width = 32
    user_width = 1
    divider = "_"
    suffix = ""
    channels = ["AW", "W", "B", "AR", "R"]  # All channels

    # Create field configs with adjusted widths
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust for data width
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    # Create extension handlers for memory operations
    extensions = create_axi4_extension_handlers(memory_model, log)

    # Create and return slave
    return create_axi4_slave(
        dut, title, prefix, divider, suffix, clock, channels,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        field_configs=adjusted_configs,
        memory_model=memory_model,
        check_protocol=True,  # Enable protocol checking
        inorder=True,  # Use in-order responses for predictability
        log=log
    )


def create_exclusive_access_master(dut, title, prefix, clock, data_width=32, log=None):
    """
    Create an AXI4 master pre-configured for exclusive access testing.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        data_width: Width of data in bits (default: 32)
        log: Logger instance

    Returns:
        AXI4Master instance configured for exclusive access testing
    """
    # Set sensible defaults
    id_width = 4
    addr_width = 32
    user_width = 1
    divider = "_"
    suffix = ""
    channels = ["AW", "W", "B", "AR", "R"]  # All channels

    # Create field configs with adjusted widths
    field_configs = {
        'AW': AXI4_AW_FIELD_CONFIG,
        'W': AXI4_W_FIELD_CONFIG,
        'B': AXI4_B_FIELD_CONFIG,
        'AR': AXI4_AR_FIELD_CONFIG,
        'R': AXI4_R_FIELD_CONFIG
    }

    # Adjust for data width
    adjusted_configs = adjust_field_configs(
        field_configs, id_width, addr_width, data_width, user_width
    )

    # Create randomization config optimized for exclusive access
    randomization_config = AXI4RandomizationConfig()
    randomization_config.set_exclusive_access_mode(probability=0.5)  # 50% exclusive transactions

    # Create and return master
    master = create_axi4_master(
        dut, title, prefix, divider, suffix, clock, channels,
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        field_configs=adjusted_configs,
        check_protocol=True,
        log=log
    )

    # Create extensions optimized for exclusive access
    # Note: Extensions will be automatically created when needed in the master

    return master


def create_performance_test_environment(dut, prefix, clock, memory_model=None, data_width=32, log=None):
    """
    Create both master and slave components optimized for bandwidth testing.

    Args:
        dut: Device under test
        prefix: Signal prefix base
        clock: Clock signal
        memory_model: Memory model for data storage (optional)
        data_width: Width of data in bits (default: 32)
        log: Logger instance

    Returns:
        Tuple of (AXI4Master, AXI4Slave, AXI4Monitor) configured for performance testing
    """
    # Set sensible defaults optimized for performance
    id_width = 8  # More IDs for better parallelism
    addr_width = 32
    user_width = 1
    divider = "_"

    # Create master with "_m" suffix
    master = create_axi4_master(
        dut, "perf_master", f"{prefix}_m", divider, "", clock,
        ["AW", "W", "B", "AR", "R"],
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        check_protocol=False,  # Disable protocol checking for speed
        log=log
    )

    # Create slave with "_s" suffix
    slave = create_axi4_slave(
        dut, "perf_slave", f"{prefix}_s", divider, "", clock,
        ["AW", "W", "B", "AR", "R"],
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        check_protocol=False,  # Disable protocol checking for speed
        inorder=False,  # Allow out-of-order responses for better performance
        ooo_strategy='round_robin',  # Use round-robin for predictable but efficient ordering
        log=log
    )

    # Create monitor for performance measurements
    monitor = create_axi4_monitor(
        dut, "perf_monitor", f"{prefix}_m", divider, "", clock,
        ["AW", "W", "B", "AR", "R"],
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        check_protocol=False,  # Disable protocol checking for speed
        log=log
    )

    return (master, slave, monitor)


def create_protocol_compliance_environment(dut, prefix, clock, memory_model=None, data_width=32, log=None):
    """
    Set up a full environment with necessary components to verify protocol compliance.

    Args:
        dut: Device under test
        prefix: Signal prefix base
        clock: Clock signal
        memory_model: Memory model for data storage (optional)
        data_width: Width of data in bits (default: 32)
        log: Logger instance

    Returns:
        Tuple of (AXI4Master, AXI4Slave, AXI4Monitor, AXI4Scoreboard) for compliance testing
    """
    # Set sensible defaults for compliance testing
    id_width = 4
    addr_width = 32
    user_width = 1
    divider = "_"

    # Create master with "_m" suffix and strict protocol checking
    master = create_axi4_master(
        dut, "compliance_master", f"{prefix}_m", divider, "", clock,
        ["AW", "W", "B", "AR", "R"],
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        check_protocol=True,  # Enable strict protocol checking
        log=log
    )

    # Create slave with "_s" suffix and strict protocol checking
    slave = create_axi4_slave(
        dut, "compliance_slave", f"{prefix}_s", divider, "", clock,
        ["AW", "W", "B", "AR", "R"],
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        memory_model=memory_model,
        check_protocol=True,  # Enable strict protocol checking
        inorder=True,  # Use in-order responses for predictability in testing
        log=log
    )

    # Create monitor for protocol checking
    monitor = create_axi4_monitor(
        dut, "compliance_monitor", f"{prefix}_m", divider, "", clock,
        ["AW", "W", "B", "AR", "R"],
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        check_protocol=True,  # Enable strict protocol checking
        log=log
    )

    # Create scoreboard for verification
    scoreboard = create_axi4_scoreboard(
        "compliance_scoreboard",
        id_width=id_width,
        addr_width=addr_width,
        data_width=data_width,
        user_width=user_width,
        log=log
    )

    # Connect monitor to scoreboard if appropriate hooks exist
    if hasattr(monitor, 'set_write_callback') and hasattr(scoreboard, 'check_write'):
        monitor.set_write_callback(scoreboard.check_write)
    if hasattr(monitor, 'set_read_callback') and hasattr(scoreboard, 'check_read'):
        monitor.set_read_callback(scoreboard.check_read)

    return (master, slave, monitor, scoreboard)


def create_memory_test_sequence(base_addr=0x1000, data_pattern="incrementing", burst_length=8,
                                id_width=4, data_width=32):
    """
    Create a transaction sequence for testing memory operations.

    Args:
        base_addr: Starting address
        data_pattern: Pattern type ("incrementing", "random", "walking_ones", "walking_zeros", "alternating")
        burst_length: Number of beats in each burst
        id_width: Width of ID field in bits
        data_width: Width of data in bits

    Returns:
        AXI4TransactionSequence configured for memory testing
    """
    # Create sequence with sensible defaults
    sequence = AXI4TransactionSequence(
        name="memory_test",
        id_width=id_width,
        addr_width=32,
        data_width=data_width,
        user_width=1
    )

    # Calculate data width in bytes for address alignment
    bytes_per_word = data_width // 8

    # Generate appropriate data values based on pattern
    if data_pattern == "incrementing":
        data_values = [0xA0000000 + i for i in range(burst_length)]
    elif data_pattern == "walking_ones":
        data_values = [1 << (i % data_width) for i in range(burst_length)]
    elif data_pattern == "walking_zeros":
        data_values = [((1 << data_width) - 1) & ~(1 << (i % data_width)) for i in range(burst_length)]
    elif data_pattern == "alternating":
        data_values = [0x55555555 if i % 2 == 0 else 0xAAAAAAAA for i in range(burst_length)]
    else:  # Random
        import random
        data_values = [random.randint(0, (1 << data_width) - 1) for _ in range(burst_length)]

    # Add write transaction
    write_id = sequence.add_write_transaction(
        addr=base_addr,
        data_values=data_values,
        burst_size=bytes_per_word.bit_length() - 1  # log2 of bytes per word
    )

    # Add read transaction with dependency on write
    read_id = sequence.add_read_transaction(
        addr=base_addr,
        burst_len=burst_length-1,
        burst_size=bytes_per_word.bit_length() - 1,  # log2 of bytes per word
        dependencies=[write_id]
    )

    # Add expected read response
    sequence.add_read_response_data(read_id, data_values)

    return sequence


def create_exclusive_access_sequence(addr=0x2000, initial_value=0xA0000000, new_value=0xB0000000):
    """
    Create a sequence that tests exclusive access operation.

    Args:
        addr: Target address
        initial_value: Initial value to write to memory
        new_value: New value to write with exclusive access

    Returns:
        AXI4TransactionSequence for exclusive access testing
    """
    # Create sequence
    sequence = AXI4TransactionSequence(
        name="exclusive_access_test",
        id_width=4,
        addr_width=32,
        data_width=32,
        user_width=1
    )

    # Step 1: Initialize memory with regular write
    init_id = sequence.add_write_transaction(
        addr=addr,
        data_values=[initial_value],
        lock=0  # Normal access
    )

    # Step 2: Exclusive read
    read_id = sequence.add_read_transaction(
        addr=addr,
        burst_len=0,  # Single beat
        lock=1,  # Exclusive access
        dependencies=[init_id]  # Must happen after initialization
    )

    # Add expected read response
    sequence.add_read_response_data(read_id, [initial_value])

    # Step 3: Exclusive write
    write_id = sequence.add_write_transaction(
        addr=addr,
        data_values=[new_value],
        lock=1,  # Exclusive access
        dependencies=[read_id]  # Must happen after exclusive read
    )

    # Add EXOKAY response expectation
    sequence.add_write_response(write_id, 1)  # 1 = EXOKAY

    # Step 4: Regular read to verify
    verify_id = sequence.add_read_transaction(
        addr=addr,
        burst_len=0,  # Single beat
        lock=0,  # Normal access
        dependencies=[write_id]  # Must happen after exclusive write
    )

    # Add expected read response with new value
    sequence.add_read_response_data(verify_id, [new_value])

    return sequence


def create_burst_test_sequence(base_addr=0x3000, data_width=32):
    """
    Create a sequence that tests different burst types and lengths.

    Args:
        base_addr: Starting address
        data_width: Width of data in bits

    Returns:
        AXI4TransactionSequence for burst testing
    """
    # Create sequence
    sequence = AXI4TransactionSequence(
        name="burst_test",
        id_width=4,
        addr_width=32,
        data_width=data_width,
        user_width=1
    )

    # Calculate bytes per word for size parameter
    bytes_per_word = data_width // 8
    burst_size = bytes_per_word.bit_length() - 1  # log2 of bytes per word

    # Current address offset
    offset = 0

    # Test INCR bursts of different lengths
    incr_lengths = [0, 1, 7, 15]  # 1, 2, 8, 16 beats
    for length in incr_lengths:
        addr = base_addr + offset
        data = [0xA0000000 + i for i in range(length + 1)]

        # Add write transaction
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=data,
            burst_type=1,  # INCR
            burst_size=burst_size
        )

        # Add read transaction
        read_id = sequence.add_read_transaction(
            addr=addr,
            burst_len=length,
            burst_type=1,  # INCR
            burst_size=burst_size,
            dependencies=[write_id]
        )

        # Add expected read response
        sequence.add_read_response_data(read_id, data)

        offset += (length + 1) * bytes_per_word + 64  # Add gap between tests

    # Test WRAP bursts (lengths must be 1, 3, 7, or 15)
    wrap_lengths = [1, 3, 7, 15]  # 2, 4, 8, 16 beats
    for length in wrap_lengths:
        addr = base_addr + offset
        data = [0xB0000000 + i for i in range(length + 1)]

        # Add write transaction
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=data,
            burst_type=2,  # WRAP
            burst_size=burst_size
        )

        # Add read transaction
        read_id = sequence.add_read_transaction(
            addr=addr,
            burst_len=length,
            burst_type=2,  # WRAP
            burst_size=burst_size,
            dependencies=[write_id]
        )

        # Add expected read response
        sequence.add_read_response_data(read_id, data)

        offset += (length + 1) * bytes_per_word + 64  # Add gap between tests

    # Test FIXED bursts
    fixed_lengths = [0, 3]  # 1, 4 beats
    for length in fixed_lengths:
        addr = base_addr + offset
        data = [0xC0000000 + i for i in range(length + 1)]

        # Add write transaction
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=data,
            burst_type=0,  # FIXED
            burst_size=burst_size
        )

        # Add read transaction
        read_id = sequence.add_read_transaction(
            addr=addr,
            burst_len=length,
            burst_type=0,  # FIXED
            burst_size=burst_size,
            dependencies=[write_id]
        )

        # Add expected read response
        sequence.add_read_response_data(read_id, data)

        offset += bytes_per_word + 64  # Add gap between tests (only need one word for FIXED)

    return sequence


def create_qos_test_sequence(base_addr=0x4000, qos_values=None):
    """
    Create a sequence that tests Quality of Service prioritization.

    Args:
        base_addr: Starting address
        qos_values: List of QoS values to test

    Returns:
        AXI4TransactionSequence for QoS testing
    """
    if qos_values is None:
        qos_values = [0, 4, 8, 15]
    # Create sequence
    sequence = AXI4TransactionSequence(
        name="qos_test",
        id_width=4,
        addr_width=32,
        data_width=32,
        user_width=1
    )

    # Add write transactions with different QoS values
    write_ids = []
    for i, qos in enumerate(qos_values):
        addr = base_addr + (i * 4)
        data = [0xD0000000 + i]

        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=data,
            qos=qos
        )
        write_ids.append(write_id)

    # Add read transactions with different QoS values
    read_ids = []
    for i, qos in enumerate(qos_values):
        addr = base_addr + (i * 4)

        read_id = sequence.add_read_transaction(
            addr=addr,
            burst_len=0,  # Single beat
            qos=qos,
            dependencies=[write_ids[i]]  # Depend on corresponding write
        )
        read_ids.append(read_id)

        # Add expected read response
        sequence.add_read_response_data(read_id, [0xD0000000 + i])

    return sequence
