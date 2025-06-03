"""
Enhanced factory functions for creating and configuring APB components
"""
from .apb_components import APBMaster, APBSlave, APBMonitor
from .apb_sequence import APBSequence
from CocoTBFramework.tbclasses.apb.apb_command_handler import APBCommandHandler
from .apb_packet import APBPacket

from ..flex_randomizer import FlexRandomizer
from ..memory_model import MemoryModel
from CocoTBFramework.scoreboards.apb_scoreboard import APBScoreboard
from CocoTBFramework.scoreboards.transformers.apb_gaxi_transformer import APBtoGAXITransformer

import random
import copy

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
            'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
            'penable': ([[0, 0], [1, 3]], [3, 1]),
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
        prefix: Signal prefix
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


def create_apb_command_handler(dut, memory_model, log=None):
    """
    Create an APB Command Handler for APB slave command/response interface.

    Args:
        dut: Device under test
        memory_model: Memory model for storage
        log: Logger instance

    Returns:
        APBCommandHandler instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)

    return APBCommandHandler(dut, memory_model, log)


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
        "s_apb",
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


def create_apb_packet(count=0, pwrite=0, paddr=0, pwdata=0, prdata=0,
                        pstrb=0, pprot=0, pslverr=0, addr_width=32, data_width=32):
    """
    Create an APB packet with the given field values.

    Args:
        count: Transaction count
        pwrite: Write enable (0=Read, 1=Write)
        paddr: Address
        pwdata: Write data (for writes)
        prdata: Read data (for reads)
        pstrb: Write strobes (for writes)
        pprot: Protection control
        pslverr: Slave error
        addr_width: Address width in bits
        data_width: Data width in bits

    Returns:
        APBPacket instance
    """
    return APBPacket(
        count=count,
        pwrite=pwrite,
        paddr=paddr,
        pwdata=pwdata,
        prdata=prdata,
        pstrb=pstrb,
        pprot=pprot,
        pslverr=pslverr,
        addr_width=addr_width,
        data_width=data_width
    )


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
                'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
                'penable': ([[0, 0], [1, 3]], [3, 1]),
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
                'psel':    ([[0, 0]], [1]),  # No psel delay
                'penable': ([[0, 0]], [1]),  # No penable delay
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
                'psel':    ([[0, 0], [1, 2]], [3, 1]),
                'penable': ([[0, 0], [1, 1]], [3, 1]),
            })
        )

    elif pattern == "stress":
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

        # Then add random mix of reads and writes
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
                'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
                'penable': ([[0, 0], [1, 3]], [3, 1]),
            })
        )

    else:
        raise ValueError(f"Unknown pattern type: {pattern}")


#===========================================================================
# Enhanced Register Testing Factory Functions
#===========================================================================

def create_register_test_sequence(reg_map, test_type="walk", options=None):
    """
    Create a test sequence for register testing based on register map information.

    Args:
        reg_map: RegisterMap instance containing register definitions
        test_type: Type of test to generate ("walk", "field", "access", "reset", "stress", "random")
        options: Dictionary of test-specific options

    Returns:
        APBSequence: Configured test sequence
    """
    # Default options
    if options is None:
        options = {}

    # Select test generator based on test type
    if test_type == "walk":
        return _create_walk_test(reg_map, options)
    elif test_type == "field":
        return _create_field_test(reg_map, options)
    elif test_type == "access":
        return _create_access_test(reg_map, options)
    elif test_type == "reset":
        return _create_reset_test(reg_map, options)
    elif test_type == "stress":
        return _create_stress_test(reg_map, options)
    elif test_type == "random":
        return _create_random_test(reg_map, options)
    else:
        raise ValueError(f"Unknown test type: {test_type}")


def _create_walk_test(reg_map, options):
    """
    Create a walking ones/zeros test that writes patterns to each register
    and reads back to verify.

    Options:
        pattern: "walking_ones" or "walking_zeros" or "alternating" (default: "walking_ones")
        delay: Clock cycles between transactions (default: 2)
    """
    pattern = options.get("pattern", "walking_ones")
    delay = options.get("delay", 2)

    # Create sequence container
    sequence = APBSequence(
        name=f"register_walk_{pattern}_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )

    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not writable
        if "w" not in reg_info.get("sw", "").lower():
            continue

        # Get register address and size
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        reg_width = reg_size * 8

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)

            # Generate test patterns
            if pattern == "walking_ones":
                # Walking ones: 0x00000001, 0x00000002, 0x00000004, etc.
                patterns = [1 << i for i in range(min(reg_width, 32))]
            elif pattern == "walking_zeros":
                # Walking zeros: 0xFFFFFFFE, 0xFFFFFFFD, 0xFFFFFFFB, etc.
                patterns = [0xFFFFFFFF ^ (1 << i) for i in range(min(reg_width, 32))]
            elif pattern == "alternating":
                # Alternating patterns: 0x55555555, 0xAAAAAAAA
                patterns = [0x55555555, 0xAAAAAAAA]
            else:
                raise ValueError(f"Unknown pattern: {pattern}")

            # Add test transactions for each pattern
            for pattern_value in patterns:
                # Write pattern
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(pattern_value)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)

                # Read back to verify
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

        elif op == "field_write" and info["fields"]:
            # Pick random field
            field_name = random.choice(list(info["fields"].keys()))
            field = info["fields"][field_name]

            # Skip if not writable
            if "w" not in field["sw_access"]:
                continue

            # Generate random field value
            field_value = random.randint(0, (1 << field["width"]) - 1)
            masked_value = (field_value << field["shift"]) & field["mask"]

            # Read current value
            if "r" in info["sw_access"]:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

            # Write field with read-modify-write
            sequence.pwrite_seq.append(True)
            sequence.addr_seq.append(addr)
            # Note: The data value is a placeholder that will be
            # updated by the test harness using read-modify-write
            sequence.data_seq.append((~field["mask"] & 0xFFFFFFFF, masked_value))
            sequence.strb_seq.append((1 << info["size"]) - 1)  # All bytes
            sequence.inter_cycle_delays.append(delay)

            # Read back to verify
            if "r" in info["sw_access"]:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

    return sequence


#===========================================================================
# Functional Register Test Factory Functions
#===========================================================================

def create_sequence_from_tuples(reg_map, reg_field_values, name="functional_test", options=None):
    """
    Create an APB sequence from a list of (register, field, value) tuples.

    Args:
        reg_map: RegisterMap instance containing register definitions
        reg_field_values: List of (register, field, value) tuples
        name: Name for the sequence
        options: Dictionary of options (delay, verify, etc.)

    Returns:
        APBSequence: Configured test sequence
    """
    # Default options
    if options is None:
        options = {}

    delay = options.get("delay", 2)
    verify = options.get("verify", True)  # Read back to verify by default

    # Create sequence container
    sequence = APBSequence(
        name=name,
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )

    # Process each register/field/value tuple
    for reg_name, field_name, value in reg_field_values:
        # Validate register exists
        if reg_name not in reg_map.registers:
            raise ValueError(f"Register '{reg_name}' not found in register map")

        reg_info = reg_map.registers[reg_name]

        # Validate field exists
        if field_name not in reg_info:
            raise ValueError(f"Field '{field_name}' not found in register '{reg_name}'")

        field_info = reg_info[field_name]
        if not isinstance(field_info, dict) or field_info.get('type') != 'field':
            raise ValueError(f"'{field_name}' in register '{reg_name}' is not a field")

        # Check field is writable
        sw_access = field_info.get("sw", reg_info.get("sw", "rw")).lower()
        if "w" not in sw_access:
            raise ValueError(f"Field '{field_name}' in register '{reg_name}' is not writable")

        # Get register address and size
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))

        # Get field offset and width
        offset = field_info.get("offset", "0")
        if ":" in offset:
            high, low = map(int, offset.split(":"))
            field_width = high - low + 1
            shift = low
        else:
            field_width = 1
            shift = int(offset)

        # Create field mask
        field_mask = ((1 << field_width) - 1) << shift

        # Validate value fits in field
        if value >= (1 << field_width):
            raise ValueError(f"Value 0x{value:X} exceeds field width ({field_width} bits)")

        # Calculate field value
        field_value = (value & ((1 << field_width) - 1)) << shift

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)

            # If register is readable, read current value first
            if "r" in sw_access:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

            # Write field value (with read-modify-write if readable)
            sequence.pwrite_seq.append(True)
            sequence.addr_seq.append(addr)

            # If readable, use read-modify-write tuple
            if "r" in sw_access:
                sequence.data_seq.append((~field_mask & 0xFFFFFFFF, field_value))
            else:
                # Not readable, just write the field value (may affect other fields)
                sequence.data_seq.append(field_value)

            sequence.strb_seq.append((1 << reg_size) - 1)  # All bytes
            sequence.inter_cycle_delays.append(delay)

            # Read back to verify if requested and readable
            if verify and "r" in sw_access:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

    return sequence


async def run_test_sequence(apb_master, sequence, verify_func=None):
    """
    Run a register test sequence through an APB master.

    Args:
        apb_master: APB master driver
        sequence: Test sequence to run
        verify_func: Optional function to verify each transaction

    Returns:
        List of transaction results
    """
    results = []
    read_data = {}  # For read-modify-write operations

    # Execute each transaction in the sequence
    for i in range(len(sequence.pwrite_seq)):
        is_write = sequence.pwrite_seq[i]
        addr = sequence.addr_seq[i]

        if is_write:
            data = sequence.data_seq[i] if i < len(sequence.data_seq) else 0
            strobe = sequence.strb_seq[i] if i < len(sequence.strb_seq) else 0xF

            # Handle read-modify-write tuple
            if isinstance(data, tuple) and len(data) == 2:
                mask, value = data
                if addr in read_data:
                    # Apply mask and value to previous read data
                    data = (read_data[addr] & mask) | value
                else:
                    # No previous read data, use value directly
                    data = value

            # Create and send write transaction
            packet = APBPacket(
                count=i,
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=strobe,
                pprot=0
            )
        else:
            # Create and send read transaction
            packet = APBPacket(
                count=i,
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0,
                pprot=0
            )

        # Send the transaction
        await apb_master.send(packet)
        await apb_master.wait_for_queue_empty()

        # Store read data for potential read-modify-write
        if not is_write and hasattr(packet, 'prdata'):
            read_data[addr] = packet.prdata

        # Add result to list
        results.append(packet)

        # Call verification function if provided
        if verify_func:
            await verify_func(packet, i)

        # Add delay if specified
        if i < len(sequence.inter_cycle_delays):
            delay = sequence.inter_cycle_delays[i]
            if delay > 0:
                await cocotb.triggers.Timer(delay, units="ns")

    return results.append(delay)

    return sequence


def _create_field_test(reg_map, options):
    """
    Create a test that targets specific fields within registers.

    Options:
        fields: List of field names to test (default: all fields)
        values: List of test values (default: [0x0, 0x1, 0xF, 0xFF])
        delay: Clock cycles between transactions (default: 2)
    """
    fields = options.get("fields", None)  # None means all fields
    test_values = options.get("values", [0x0, 0x1, 0xF, 0xFF])
    delay = options.get("delay", 2)

    # Create sequence container
    sequence = APBSequence(
        name="register_field_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )

    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not writable
        if "w" not in reg_info.get("sw", "").lower():
            continue

        # Get register address and size
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        # Process each field in the register
        for field_name, field_info in reg_info.items():
            # Skip non-field entries
            if not isinstance(field_info, dict) or field_info.get("type") != "field":
                continue

            # Skip fields not in the test list (if a list is specified)
            if fields is not None and field_name not in fields:
                continue

            # Skip fields that are not writable
            if "w" not in field_info.get("sw", "").lower():
                continue

            # Get field offset (position)
            offset = field_info.get("offset", "0")
            if ":" in offset:
                high, low = map(int, offset.split(":"))
                field_width = high - low + 1
                shift = low
            else:
                field_width = 1
                shift = int(offset)

            # Create field mask
            field_mask = ((1 << field_width) - 1) << shift

            # Test each register instance
            for idx in range(reg_count):
                # Calculate address for this register instance
                addr = reg_addr + (idx * reg_size)

                # Test each value on this field
                for test_value in test_values:
                    # Truncate test value to field width
                    masked_value = (test_value & ((1 << field_width) - 1)) << shift

                    # Read initial value
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)

                    # Write field with test value (preserving other fields)
                    sequence.pwrite_seq.append(True)
                    sequence.addr_seq.append(addr)
                    # Note: The data value is a placeholder that will be
                    # updated by the test harness using read-modify-write
                    sequence.data_seq.append((~field_mask & 0xFFFFFFFF, masked_value))
                    sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                    sequence.inter_cycle_delays.append(delay)

                    # Read back to verify
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)

    return sequence


def _create_access_test(reg_map, options):
    """
    Create a test that verifies register access rights (R/W, RO, WO, etc.).

    Options:
        delay: Clock cycles between transactions (default: 2)
    """
    delay = options.get("delay", 2)

    # Create sequence container
    sequence = APBSequence(
        name="register_access_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )

    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Get register address and size
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))

        # Get access rights
        sw_access = reg_info.get("sw", "rw").lower()

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        # Test each register instance
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)

            # Test read access
            if "r" in sw_access:
                # Read should succeed
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

            # Test write access
            if "w" in sw_access:
                # Write should succeed - use 0x55555555 pattern
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(0x55555555)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)

                # Read back to verify (if readable)
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)

                # Write inverse pattern - 0xAAAAAAAA
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(0xAAAAAAAA)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)

                # Read back to verify (if readable)
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)

            # Special handling for W1C (write-1-to-clear) registers
            if "w1c" in sw_access:
                # First read to get current value
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)

                # Write all 1s to clear all bits
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(0xFFFFFFFF)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)

                # Read back to verify bits are cleared
                if "r" in sw_access:
                    sequence.pwrite_seq.append(False)
                    sequence.addr_seq.append(addr)
                    sequence.inter_cycle_delays.append(delay)

    return sequence


def _create_reset_test(reg_map, options):
    """
    Create a test that verifies registers return to default values after reset.

    Options:
        delay: Clock cycles between transactions (default: 2)
        reset_type: Type of reset to perform ("hard", "soft") (default: "hard")
    """
    delay = options.get("delay", 2)
    reset_type = options.get("reset_type", "hard")

    # Create sequence container
    sequence = APBSequence(
        name=f"register_reset_{reset_type}_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )

    # Special flag to indicate a reset should be performed
    sequence.reset_points = []

    # For each register
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers with no default value
        if "default" not in reg_info:
            continue

        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        default_value = int(reg_info.get("default", "0"), 16)

        # Get access rights
        sw_access = reg_info.get("sw", "rw").lower()

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        # Test each register instance
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)

            # Only test registers that are readable and writable
            if "r" in sw_access and "w" in sw_access:
                # First, read default value
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

                # Write non-default value (inverse of default)
                sequence.pwrite_seq.append(True)
                sequence.addr_seq.append(addr)
                sequence.data_seq.append(~default_value & 0xFFFFFFFF)
                sequence.strb_seq.append((1 << (reg_size)) - 1)  # All bytes
                sequence.inter_cycle_delays.append(delay)

                # Read back to verify change
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

    # Add reset point after writing all registers
    sequence.reset_points.append(len(sequence.pwrite_seq))

    # After reset, read all registers to verify default values
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers with no default value
        if "default" not in reg_info:
            continue

        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))

        # Get access rights
        sw_access = reg_info.get("sw", "rw").lower()

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        # Test each register instance
        for idx in range(reg_count):
            # Calculate address for this register instance
            addr = reg_addr + (idx * reg_size)

            # Check default value after reset
            if "r" in sw_access:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays.append(delay)

    return sequence


def _create_stress_test(reg_map, options):
    """
    Create a stress test with rapid back-to-back register accesses.

    Options:
        iterations: Number of test iterations (default: 100)
        delay: Clock cycles between transactions (default: 0)
    """
    iterations = options.get("iterations", 100)
    delay = options.get("delay", 0)  # Minimum delay for stress testing

    # Create sequence container
    sequence = APBSequence(
        name="register_stress_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )

    # Collect all writable registers
    writable_regs = []
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not writable
        if "w" not in reg_info.get("sw", "").lower():
            continue

        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        # Add each register instance
        for idx in range(reg_count):
            addr = reg_addr + (idx * reg_size)
            writable_regs.append((addr, reg_size))

    # Collect all readable registers
    readable_regs = []
    for reg_name, reg_info in reg_map.registers.items():
        # Skip registers that are not readable
        if "r" not in reg_info.get("sw", "").lower():
            continue

        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        # Add each register instance
        for idx in range(reg_count):
            addr = reg_addr + (idx * reg_size)
            readable_regs.append(addr)

    # Generate stress test patterns
    patterns = [0xAAAAAAAA, 0x55555555, 0xFFFFFFFF, 0x00000000]

    # Generate the test sequence
    for _ in range(iterations):
        # Pick random action: 0=write, 1=read
        action = random.randint(0, 1)

        if action == 0 and writable_regs:  # Write
            # Pick random register
            addr, size = random.choice(writable_regs)

            # Pick random data pattern
            data = random.choice(patterns)

            # Add write transaction
            sequence.pwrite_seq.append(True)
            sequence.addr_seq.append(addr)
            sequence.data_seq.append(data)
            sequence.strb_seq.append((1 << size) - 1)  # All bytes
            sequence.inter_cycle_delays.append(delay)

        elif readable_regs:  # Read
            # Pick random register
            addr = random.choice(readable_regs)

            # Add read transaction
            sequence.pwrite_seq.append(False)
            sequence.addr_seq.append(addr)
            sequence.inter_cycle_delays.append(delay)

    return sequence


def _create_random_test(reg_map, options):
    """
    Create a randomized test with various register operations.

    Options:
        iterations: Number of test iterations (default: 100)
        seed: Random seed for reproducibility (default: None)
        delay_min: Minimum delay between transactions (default: 1)
        delay_max: Maximum delay between transactions (default: 5)
    """
    iterations = options.get("iterations", 100)
    seed = options.get("seed", None)
    delay_min = options.get("delay_min", 1)
    delay_max = options.get("delay_max", 5)

    # Set random seed if provided
    if seed is not None:
        random.seed(seed)

    # Create sequence container
    sequence = APBSequence(
        name="register_random_test",
        pwrite_seq=[],
        addr_seq=[],
        data_seq=[],
        strb_seq=[],
        inter_cycle_delays=[]
    )

    # Build register information dictionary
    reg_info_dict = {}
    for reg_name, reg_info in reg_map.registers.items():
        # Get register information
        reg_addr = reg_map.start_address + int(reg_info.get("address", "0"), 16)
        reg_size = int(reg_info.get("size", "4"))
        sw_access = reg_info.get("sw", "rw").lower()

        # Get default value if available
        default_value = 0
        if "default" in reg_info:
            default_value = int(reg_info.get("default", "0"), 16)

        # Handle register arrays
        reg_count = int(reg_info.get("count", "1"))

        # Process each register instance
        for idx in range(reg_count):
            addr = reg_addr + (idx * reg_size)
            reg_info_dict[addr] = {
                "size": reg_size,
                "sw_access": sw_access,
                "default": default_value,
                "fields": {}
            }

            # Add field information
            for field_name, field_info in reg_info.items():
                if isinstance(field_info, dict) and field_info.get("type") == "field":
                    offset = field_info.get("offset", "0")
                    field_sw = field_info.get("sw", sw_access).lower()

                    # Process field offset
                    if ":" in offset:
                        high, low = map(int, offset.split(":"))
                        field_width = high - low + 1
                        shift = low
                    else:
                        field_width = 1
                        shift = int(offset)

                    # Add field info
                    reg_info_dict[addr]["fields"][field_name] = {
                        "width": field_width,
                        "shift": shift,
                        "sw_access": field_sw,
                        "mask": ((1 << field_width) - 1) << shift
                    }

    # Generate random test sequence
    for _ in range(iterations):
        # Pick random register
        if not reg_info_dict:
            break
        addr = random.choice(list(reg_info_dict.keys()))
        info = reg_info_dict[addr]

        # Pick random operation
        ops = []
        if "r" in info["sw_access"]:
            ops.append("read")
        if "w" in info["sw_access"]:
            ops.append("write")
            if info["fields"]:
                ops.append("field_write")

        if not ops:
            continue

        op = random.choice(ops)

        # Random delay
        delay = random.randint(delay_min, delay_max)

        if op == "read":
            # Simple register read
            sequence.pwrite_seq.append(False)
            sequence.addr_seq.append(addr)
            sequence.inter_cycle_delays.append(delay)

        elif op == "write":
            # Full register write
            data = random.randint(0, (1 << (info["size"] * 8)) - 1)

            sequence.pwrite_seq.append(True)
            sequence.addr_seq.append(addr)
            sequence.data_seq.append(data)
            sequence.strb_seq.append((1 << info["size"]) - 1)  # All bytes
            sequence.inter_cycle_delays.append(delay)

            # Add read-back verification
            if "r" in info["sw_access"]:
                sequence.pwrite_seq.append(False)
                sequence.addr_seq.append(addr)
                sequence.inter_cycle_delays