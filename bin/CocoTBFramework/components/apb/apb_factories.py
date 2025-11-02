# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: apb_factories
# Purpose: Factory functions for creating and configuring APB components
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Factory functions for creating and configuring APB components
"""
from .apb_components import APBMaster, APBSlave, APBMonitor
from .apb_sequence import APBSequence

from ..shared.flex_randomizer import FlexRandomizer
from ..shared.memory_model import MemoryModel
from CocoTBFramework.scoreboards.apb_scoreboard import APBScoreboard
from CocoTBFramework.scoreboards.apb_gaxi_transformer import APBtoGAXITransformer


def create_apb_master(dut, title, prefix, clock, addr_width=32, data_width=32,
                        randomizer=None, log=None):
    """
    Create an APB Master component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        addr_width: Address width in bits
        data_width: Data width in bits
        randomizer: Timing randomizer
        log: Logger instance (default: dut's logger)

    Returns:
        APBMaster instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create default randomizer if none provided
    if randomizer is None:
        randomizer = FlexRandomizer({
            'psel':    ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),
            'penable': ([(0, 0), (1, 3)], [3, 1]),
        })

    return APBMaster(
        dut,
        title,
        prefix,
        clock,
        bus_width=data_width,
        addr_width=addr_width,
        randomizer=randomizer,
        log=log
    )


def create_apb_slave(dut, title, prefix, clock, addr_width=32, data_width=32,
                        registers=None, randomizer=None, log=None,
                        error_overflow=False):
    """
    Create an APB Slave component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        addr_width: Address width in bits
        data_width: Data width in bits
        registers: Register values (or number of registers)
        randomizer: Timing randomizer
        log: Logger instance (default: dut's logger)
        error_overflow: Whether to generate errors on address overflow

    Returns:
        APBSlave instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Process registers parameter
    if registers is None:
        registers = []
    elif isinstance(registers, int):
        # If registers is an integer, treat it as the number of registers
        registers = [0] * (registers * (data_width // 8))

    return APBSlave(
        dut,
        title,
        prefix,
        clock,
        registers=registers,
        bus_width=data_width,
        addr_width=addr_width,
        randomizer=randomizer,
        log=log,
        error_overflow=error_overflow
    )


def create_apb_monitor(dut, title, prefix, clock, addr_width=32, data_width=32, log=None):
    """
    Create an APB Monitor component with configuration.

    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        addr_width: Address width in bits
        data_width: Data width in bits
        log: Logger instance (default: dut's logger)

    Returns:
        APBMonitor instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    return APBMonitor(
        dut,
        title,
        prefix,
        clock,
        bus_width=data_width,
        addr_width=addr_width,
        log=log
    )


def create_apb_scoreboard(name, addr_width=32, data_width=32, log=None):
    """
    Create an APB Scoreboard with configuration.

    Args:
        name: Scoreboard name
        addr_width: Address width in bits
        data_width: Data width in bits
        log: Logger instance

    Returns:
        APBScoreboard instance
    """
    return APBScoreboard(name, addr_width, data_width, log)


def create_apb_components(dut, clock, title_prefix="", addr_width=32, data_width=32,
                          memory_lines=1024, randomizer=None, log=None):
    """
    Create a complete set of APB components (master, slave, monitor, scoreboard).

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        addr_width: Address width in bits
        data_width: Data width in bits
        memory_lines: Number of memory lines for shared memory model
        randomizer: Timing randomizer for master
        log: Logger instance

    Returns:
        Dictionary containing all created components
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    # Create shared memory model
    memory_model = MemoryModel(
        num_lines=memory_lines,
        bytes_per_line=data_width // 8,
        log=log
    )

    # Create APB master
    master = create_apb_master(
        dut,
        f"{title_prefix}APB Master",
        "s_apb",
        clock,
        addr_width=addr_width,
        data_width=data_width,
        randomizer=randomizer,
        log=log
    )

    # Create APB monitor
    monitor = create_apb_monitor(
        dut,
        f"{title_prefix}APB Monitor",
        clock,
        addr_width=addr_width,
        data_width=data_width,
        log=log
    )

    # Create APB scoreboard
    scoreboard = create_apb_scoreboard(
        f"{title_prefix}APB_Scoreboard",
        addr_width=addr_width,
        data_width=data_width,
        log=log
    )

    # Create APB command handler if DUT supports it
    command_handler = None
    if hasattr(dut, 'o_cmd_valid'):
        command_handler = create_apb_command_handler(dut, memory_model, log)

    # Return all components
    return {
        'master': master,
        'monitor': monitor,
        'scoreboard': scoreboard,
        'command_handler': command_handler,
        'memory_model': memory_model
    }


def create_apb_transformer(gaxi_field_config, gaxi_packet_class, log=None):
    """
    Create a transformer from APB to GAXI protocol.

    Args:
        gaxi_field_config: GAXI field configuration
        gaxi_packet_class: GAXI packet class
        log: Logger instance

    Returns:
        APBtoGAXITransformer instance
    """
    return APBtoGAXITransformer(gaxi_field_config, gaxi_packet_class, log)


def create_apb_sequence(name="basic", num_regs=10, base_addr=0,
                            pattern="alternating", data_width=32,
                            randomize_delays=True):
    """
    Create an APB Sequence for testing.

    Args:
        name: Sequence name
        num_regs: Number of registers to test
        base_addr: Base address
        pattern: Pattern type ("alternating", "burst", "strobe", "stress")
        data_width: Data width in bits
        randomize_delays: Whether to include random delays

    Returns:
        APBSequence instance
    """
    # Prepare sequence components
    pwrite_seq = []
    addr_seq = []
    data_seq = []
    strb_seq = []
    strb_width = data_width // 8

    if pattern == "alternating":
        # Alternating write-read pattern
        for i in range(num_regs):
            # Write
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(0xA0000000 + i)
            strb_seq.append(2**strb_width - 1)  # All strobe bits set

            # Read
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)

        # Delays between transactions
        delays = [5] * (len(pwrite_seq) - 1) if randomize_delays else [0] * (len(pwrite_seq) - 1)

        return APBSequence(
            name=name,
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays,
            master_randomizer=FlexRandomizer({
                'psel':    ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),
                'penable': ([(0, 0), (1, 3)], [3, 1]),
            })
        )

    elif pattern == "burst":
        # All writes followed by all reads
        # First all writes
        for i in range(num_regs):
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(0xB0000000 + i)
            strb_seq.append(2**strb_width - 1)  # All strobe bits set

        # Then all reads
        for i in range(num_regs):
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)

        # No delays for burst mode
        delays = [0] * (len(pwrite_seq) - 1)

        return APBSequence(
            name=name,
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays,
            # Fast back-to-back transactions
            master_randomizer=FlexRandomizer({
                'psel':    ([(0, 0)], [1]),  # No psel delay
                'penable': ([(0, 0)], [1]),  # No penable delay
            })
        )

    elif pattern == "strobe":
        # Test patterns for strobes
        test_data = [0xFFFFFFFF, 0x12345678, 0xAABBCCDD, 0x99887766, 0x55443322]
        test_strobes = [2**strb_width - 1]  # Start with all bits set

        # Add individual byte enables
        test_strobes.extend(1 << i for i in range(strb_width))
        # Add some combinations (first half, second half, etc.)
        if strb_width >= 2:
            test_strobes.append(0x3)  # First two bytes
        if strb_width >= 4:
            test_strobes.extend((0x5, 0xA))

        # Initial write with all bits set
        pwrite_seq.append(True)
        addr_seq.append(base_addr)
        data_seq.append(0)
        strb_seq.append(2**strb_width - 1)

        # For each test pattern (up to num_regs)
        test_count = min(len(test_data), num_regs)
        for i in range(test_count):
            # Get corresponding strobe pattern
            strb_idx = i % len(test_strobes)

            # Write with specific pattern
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(test_data[i])
            strb_seq.append(test_strobes[strb_idx])

            # Read back
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)

        # Delays between transactions
        delays = [3] * (len(pwrite_seq) - 1) if randomize_delays else [0] * (len(pwrite_seq) - 1)

        return APBSequence(
            name=name,
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays,
            master_randomizer=FlexRandomizer({
                'psel':    ([(0, 0), (1, 2)], [3, 1]),
                'penable': ([(0, 0), (1, 1)], [3, 1]),
            })
        )

    elif pattern == "stress":
        import random

        # Setup address range
        addr_range = [base_addr + i * 4 for i in range(num_regs)]

        # Setup data and strobe ranges
        data_range = [0xC0000000 + i for i in range(20)]
        strobe_range = [
            2**strb_width - 1,  # All bits
            0x1, 0x2, 0x4, 0x8,  # Individual bytes (for 32-bit)
            0x3, 0x5, 0x9, 0x6, 0xA, 0xC  # Various combinations
        ]
        # Trim strobe_range based on actual strb_width
        strobe_range = [s & ((1 << strb_width) - 1) for s in strobe_range]

        # First add some writes to ensure we have data (20% of transaction count)
        num_transactions = num_regs * 5  # Multiple transactions per register
        initial_writes = max(num_regs, num_transactions // 5)
        pwrite_seq.extend([True] * initial_writes)

        # Then add random mix of reads and writes for the rest
        write_probability = 0.7  # 70% writes
        pwrite_seq.extend(
            random.random() < write_probability
            for _ in range(num_transactions - initial_writes)
        )
        # Setup delays
        delay_range = list(range(6)) if randomize_delays else [0]

        return APBSequence(
            name=name,
            pwrite_seq=pwrite_seq,
            addr_seq=addr_range,
            data_seq=data_range,
            strb_seq=strobe_range,
            inter_cycle_delays=delay_range,
            use_random_selection=True,  # Randomly select from sequences
            master_randomizer=FlexRandomizer({
                'psel':    ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),
                'penable': ([(0, 0), (1, 3)], [3, 1]),
            })
        )

    else:
        raise ValueError(f"Unknown pattern type: {pattern}")
