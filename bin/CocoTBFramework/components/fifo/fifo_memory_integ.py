"""
Simple Memory Integration Helper for FIFO Components

This module provides lightweight helper functions for integrating with
your existing MemoryModel infrastructure, eliminating the duplicate
EnhancedMemoryModel and FIFOMemoryInteg classes.

All functionality now leverages your existing MemoryModel which already has:
- write_transaction() and read_transaction() methods
- Comprehensive error handling and boundary checking
- Statistics tracking and diagnostics
- Access maps and region management
"""

from typing import Optional, Dict, Any, Tuple


def attach_memory_model(component, memory_model, field_mapping=None):
    """
    Attach a memory model to a FIFO component using existing infrastructure.

    Args:
        component: FIFO component (master/slave/monitor)
        memory_model: Your existing MemoryModel instance
        field_mapping: Optional mapping of memory fields to packet fields

    Returns:
        The component for method chaining
    """
    # Attach memory model directly - no wrapper needed
    component.memory_model = memory_model

    # Set up field mapping if provided
    if field_mapping:
        component.memory_field_mapping = field_mapping
    else:
        # Default mapping
        component.memory_field_mapping = {
            'addr': 'addr',
            'data': 'data',
            'strb': 'strb'
        }

    if hasattr(component, 'log') and component.log:
        component.log.info(f"Attached memory model to {getattr(component, 'title', 'component')}")

    return component


def write_packet_to_memory(memory_model, packet, component_name="Component", log=None):
    """
    Write a packet to memory using existing MemoryModel.write_transaction().

    Args:
        memory_model: Your existing MemoryModel instance
        packet: Packet to write to memory
        component_name: Component name for error messages
        log: Logger instance

    Returns:
        (success, error_message): Tuple with success flag and error message
    """
    if memory_model is None:
        return False, "No memory model available"

    # Use existing MemoryModel.write_transaction() method
    # This already has all the error handling, boundary checking, and statistics
    return memory_model.write_transaction(
        transaction=packet,
        check_required_fields=True,
        component_name=component_name
    )


def read_packet_from_memory(memory_model, packet, component_name="Component", log=None):
    """
    Read data from memory into a packet using existing MemoryModel.read_transaction().

    Args:
        memory_model: Your existing MemoryModel instance
        packet: Packet containing address to read from
        component_name: Component name for error messages
        log: Logger instance

    Returns:
        (success, data, error_message): Tuple with success flag, data, and error message
    """
    if memory_model is None:
        return False, None, "No memory model available"

    # Use existing MemoryModel.read_transaction() method
    # This already has all the error handling, boundary checking, and statistics
    return memory_model.read_transaction(
        transaction=packet,
        update_transaction=True,
        check_required_fields=True,
        component_name=component_name
    )


def get_memory_stats(memory_model):
    """
    Get memory statistics using existing MemoryModel infrastructure.

    Args:
        memory_model: Your existing MemoryModel instance

    Returns:
        Dictionary with memory statistics
    """
    if memory_model is None:
        return {'error': 'No memory model available'}

    # Use existing MemoryModel.get_stats() method
    return memory_model.get_stats()


def create_memory_regions(memory_model, regions_config, log=None):
    """
    Define memory regions using existing MemoryModel infrastructure.

    Args:
        memory_model: Your existing MemoryModel instance
        regions_config: List of (name, start_addr, end_addr, description) tuples
        log: Logger instance

    Returns:
        Memory model for method chaining
    """
    if memory_model is None:
        if log:
            log.error("No memory model available for region definition")
        return None

    # Use existing MemoryModel.define_region() method
    for region_config in regions_config:
        if len(region_config) >= 3:
            name, start_addr, end_addr = region_config[:3]
            description = region_config[3] if len(region_config) > 3 else None
            memory_model.define_region(name, start_addr, end_addr, description)

    return memory_model


def dump_memory_with_access_info(memory_model, include_regions=True):
    """
    Generate memory dump using existing MemoryModel infrastructure.

    Args:
        memory_model: Your existing MemoryModel instance
        include_regions: Whether to include region access information

    Returns:
        String with memory dump
    """
    if memory_model is None:
        return "No memory model available"

    # Use existing MemoryModel.dump() method
    return memory_model.dump(include_access_info=True)


# Convenience functions for FIFO-specific operations
def setup_fifo_memory(memory_model, fifo_capacity=8, base_addr=0x0000, log=None):
    """
    Set up memory regions for FIFO testing using existing infrastructure.

    Args:
        memory_model: Your existing MemoryModel instance
        fifo_capacity: FIFO capacity in entries
        base_addr: Base address for FIFO data
        log: Logger instance

    Returns:
        Memory model for method chaining
    """
    if memory_model is None:
        if log:
            log.error("No memory model available for FIFO setup")
        return None

    # Define FIFO data region using existing infrastructure
    fifo_end_addr = base_addr + (fifo_capacity * memory_model.bytes_per_line) - 1

    regions = [
        ("fifo_data", base_addr, fifo_end_addr, f"FIFO data region ({fifo_capacity} entries)")
    ]

    return create_memory_regions(memory_model, regions, log)


def validate_fifo_transaction(memory_model, packet, operation="write", log=None):
    """
    Validate a FIFO transaction using existing MemoryModel infrastructure.

    Args:
        memory_model: Your existing MemoryModel instance
        packet: Packet to validate
        operation: Operation type ("write" or "read")
        log: Logger instance

    Returns:
        (valid, error_message): Tuple with validation result and error message
    """
    if memory_model is None:
        return False, "No memory model available"

    # Basic validation using existing packet infrastructure
    try:
        # Check if packet has required fields
        if not hasattr(packet, 'addr'):
            return False, "Packet missing address field"

        if operation == "write" and not hasattr(packet, 'data'):
            return False, "Write packet missing data field"

        addr = packet.addr

        # Use existing boundary checking logic
        if addr < 0:
            return False, f"Invalid negative address: {addr}"

        if addr + memory_model.bytes_per_line > memory_model.size:
            return False, f"Address 0x{addr:X} would exceed memory bounds"

        return True, ""

    except Exception as e:
        error_msg = f"Validation error: {str(e)}"
        if log:
            log.error(error_msg)
        return False, error_msg


# Integration with existing component classes
class MemoryModelMixin:
    """
    Mixin to add memory model functionality to FIFO components.

    This leverages your existing MemoryModel infrastructure without duplication.
    """

    def setup_memory_integration(self, memory_model, field_mapping=None):
        """Set up memory integration using existing infrastructure."""
        return attach_memory_model(self, memory_model, field_mapping)

    def write_to_memory(self, packet):
        """Write packet to memory using existing infrastructure."""
        if not hasattr(self, 'memory_model') or self.memory_model is None:
            return False, "No memory model attached"

        component_name = getattr(self, 'title', 'Component')
        log = getattr(self, 'log', None)

        return write_packet_to_memory(self.memory_model, packet, component_name, log)

    def read_from_memory(self, packet):
        """Read data from memory using existing infrastructure."""
        if not hasattr(self, 'memory_model') or self.memory_model is None:
            return False, None, "No memory model attached"

        component_name = getattr(self, 'title', 'Component')
        log = getattr(self, 'log', None)

        return read_packet_from_memory(self.memory_model, packet, component_name, log)

    def get_memory_statistics(self):
        """Get memory statistics using existing infrastructure."""
        if not hasattr(self, 'memory_model') or self.memory_model is None:
            return {'error': 'No memory model attached'}

        return get_memory_stats(self.memory_model)


# Note: This file replaces the entire fifo_memory_integ.py
#
# DELETED CLASSES (no longer needed):
# - EnhancedMemoryModel (duplicate of your MemoryModel)
# - FIFOMemoryInteg (wrapper around functionality your MemoryModel already provides)
#
# BENEFITS:
# - Eliminates ~400 lines of duplicate code
# - Uses your existing optimized MemoryModel infrastructure
# - Maintains all functionality through lightweight helpers
# - Consistent error handling and statistics across all components
# - Better integration with your existing caching and performance optimizations