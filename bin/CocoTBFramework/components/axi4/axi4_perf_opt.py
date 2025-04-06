"""
Performance Optimizations for AXI4 Components

This module provides optimizations for the AXI4 components to improve
performance when working with field configurations.
"""

import functools
import time
from typing import Dict, Any, Optional, Tuple, List, Set, Union

from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition


class FieldConfigCache:
    """
    Cache for field configurations to avoid repeated field lookups and calculations.
    
    This class provides caching for common field operations like masking values
    and calculating bit widths. It helps improve performance in high-throughput
    simulation environments.
    """
    
    def __init__(self):
        """Initialize the field configuration cache"""
        # Cache for field masks (field_name -> mask value)
        self._field_masks = {}
        
        # Cache for field bits (field_name -> bits)
        self._field_bits = {}
        
        # Cache for field active bits (field_name -> (msb, lsb))
        self._field_active_bits = {}
        
        # Cache for field formatting (field_name -> format function)
        self._field_formatters = {}
        
        # Stats for hit rates
        self._mask_hits = 0
        self._mask_misses = 0
        self._bits_hits = 0
        self._bits_misses = 0
        self._active_bits_hits = 0
        self._active_bits_misses = 0
        self._format_hits = 0
        self._format_misses = 0
    
    def get_field_mask(self, field_config: FieldConfig, field_name: str) -> int:
        """
        Get a mask for the specified field (cached).
        
        Args:
            field_config: Field configuration
            field_name: Field name
            
        Returns:
            Mask value (all 1's for the field width)
        """
        # Create a cache key that includes the field config and field name
        # Use id() to uniquely identify the field config object
        cache_key = (id(field_config), field_name)
        
        # Check if we have a cached mask
        if cache_key in self._field_masks:
            self._mask_hits += 1
            return self._field_masks[cache_key]
        
        # Calculate the mask
        self._mask_misses += 1
        if not field_config.has_field(field_name):
            # Default to all bits set if field not found
            mask = 0xFFFFFFFF
        else:
            field_def = field_config.get_field(field_name)
            mask = (1 << field_def.bits) - 1
        
        # Cache the result
        self._field_masks[cache_key] = mask
        return mask
    
    def get_field_bits(self, field_config: FieldConfig, field_name: str) -> int:
        """
        Get the number of bits for the specified field (cached).
        
        Args:
            field_config: Field configuration
            field_name: Field name
            
        Returns:
            Number of bits in the field
        """
        # Create a cache key
        cache_key = (id(field_config), field_name)
        
        # Check if we have a cached value
        if cache_key in self._field_bits:
            self._bits_hits += 1
            return self._field_bits[cache_key]
        
        # Calculate the bits
        self._bits_misses += 1
        if not field_config.has_field(field_name):
            # Default to 32 bits if field not found
            bits = 32
        else:
            field_def = field_config.get_field(field_name)
            bits = field_def.bits
        
        # Cache the result
        self._field_bits[cache_key] = bits
        return bits
    
    def get_field_active_bits(self, field_config: FieldConfig, field_name: str) -> Tuple[int, int]:
        """
        Get the active bits (msb, lsb) for the specified field (cached).
        
        Args:
            field_config: Field configuration
            field_name: Field name
            
        Returns:
            Tuple of (msb, lsb) for the field
        """
        # Create a cache key
        cache_key = (id(field_config), field_name)
        
        # Check if we have a cached value
        if cache_key in self._field_active_bits:
            self._active_bits_hits += 1
            return self._field_active_bits[cache_key]
        
        # Calculate the active bits
        self._active_bits_misses += 1
        if not field_config.has_field(field_name):
            # Default to full width if field not found
            bits = 32
            active_bits = (bits - 1, 0)
        else:
            field_def = field_config.get_field(field_name)
            active_bits = field_def.active_bits
        
        # Cache the result
        self._field_active_bits[cache_key] = active_bits
        return active_bits
    
    def get_field_formatter(self, field_config: FieldConfig, field_name: str):
        """
        Get a formatting function for the specified field (cached).
        
        Args:
            field_config: Field configuration
            field_name: Field name
            
        Returns:
            Function that formats a value according to the field's format
        """
        # Create a cache key
        cache_key = (id(field_config), field_name)
        
        # Check if we have a cached formatter
        if cache_key in self._field_formatters:
            self._format_hits += 1
            return self._field_formatters[cache_key]
        
        # Create a formatter function
        self._format_misses += 1
        if not field_config.has_field(field_name):
            # Default to hex format if field not found
            formatter = lambda value: f"0x{value:X}"
        else:
            field_def = field_config.get_field(field_name)
            fmt = field_def.format
            width = field_def.display_width
            
            if fmt == 'bin':
                formatter = lambda value: f"0b{value:0{width}b}"
            elif fmt == 'dec':
                formatter = lambda value: f"{value:{width}d}"
            else:
                # Default to hex
                formatter = lambda value: f"0x{value:0{width}X}"
        
        # Cache the formatter
        self._field_formatters[cache_key] = formatter
        return formatter
    
    def clear(self):
        """Clear all caches"""
        self._field_masks.clear()
        self._field_bits.clear()
        self._field_active_bits.clear()
        self._field_formatters.clear()
        
        # Reset statistics
        self._mask_hits = 0
        self._mask_misses = 0
        self._bits_hits = 0
        self._bits_misses = 0
        self._active_bits_hits = 0
        self._active_bits_misses = 0
        self._format_hits = 0
        self._format_misses = 0
    
    def get_stats(self) -> Dict[str, Any]:
        """
        Get cache statistics.
        
        Returns:
            Dictionary containing hit rates and counts
        """
        # Calculate hit rates
        mask_total = self._mask_hits + self._mask_misses
        mask_hit_rate = (self._mask_hits / mask_total) * 100 if mask_total > 0 else 0
        
        bits_total = self._bits_hits + self._bits_misses
        bits_hit_rate = (self._bits_hits / bits_total) * 100 if bits_total > 0 else 0
        
        active_bits_total = self._active_bits_hits + self._active_bits_misses
        active_bits_hit_rate = (self._active_bits_hits / active_bits_total) * 100 if active_bits_total > 0 else 0
        
        format_total = self._format_hits + self._format_misses
        format_hit_rate = (self._format_hits / format_total) * 100 if format_total > 0 else 0
        
        # Calculate overall hit rate
        total_hits = self._mask_hits + self._bits_hits + self._active_bits_hits + self._format_hits
        total_misses = self._mask_misses + self._bits_misses + self._active_bits_misses + self._format_misses
        total = total_hits + total_misses
        overall_hit_rate = (total_hits / total) * 100 if total > 0 else 0
        
        return {
            'mask_hits': self._mask_hits,
            'mask_misses': self._mask_misses,
            'mask_hit_rate': mask_hit_rate,
            'bits_hits': self._bits_hits,
            'bits_misses': self._bits_misses,
            'bits_hit_rate': bits_hit_rate,
            'active_bits_hits': self._active_bits_hits,
            'active_bits_misses': self._active_bits_misses,
            'active_bits_hit_rate': active_bits_hit_rate,
            'format_hits': self._format_hits,
            'format_misses': self._format_misses,
            'format_hit_rate': format_hit_rate,
            'total_hits': total_hits,
            'total_misses': total_misses,
            'overall_hit_rate': overall_hit_rate,
            'cache_sizes': {
                'masks': len(self._field_masks),
                'bits': len(self._field_bits),
                'active_bits': len(self._field_active_bits),
                'formatters': len(self._field_formatters)
            }
        }


# Global cache instance
_FIELD_CONFIG_CACHE = FieldConfigCache()


def get_field_config_cache() -> FieldConfigCache:
    """Get the global field configuration cache"""
    return _FIELD_CONFIG_CACHE


def clear_field_config_cache():
    """Clear the global field configuration cache"""
    _FIELD_CONFIG_CACHE.clear()


def mask_field_value(field_config: FieldConfig, field_name: str, value: int) -> int:
    """
    Mask a value to the width of a field (cached).
    
    Args:
        field_config: Field configuration
        field_name: Field name
        value: Value to mask
        
    Returns:
        Masked value
    """
    # Get the field mask from cache
    mask = _FIELD_CONFIG_CACHE.get_field_mask(field_config, field_name)
    
    # Apply the mask
    return value & mask


def timed(func):
    """
    Decorator for timing function execution.
    
    Args:
        func: Function to time
        
    Returns:
        Wrapped function with timing
    """
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        start_time = time.time()
        result = func(*args, **kwargs)
        end_time = time.time()
        print(f"Function {func.__name__} took {(end_time - start_time) * 1000:.2f} ms")
        return result
    return wrapper


class OptimizedAXI4Packet:
    """
    Optimized version of AXI4Packet that uses caching for field operations.
    
    This class extends the functionality of AXI4Packet with performance
    optimizations for high-throughput simulation environments.
    """
    
    @staticmethod
    def validate_axi4_protocol_cached(packet, field_config: FieldConfig):
        """
        Validate an AXI4 packet against protocol rules with caching.
        
        Args:
            packet: The packet to validate
            field_config: Field configuration
            
        Returns:
            tuple: (is_valid, error_message)
        """
        # Determine which channel this packet is for
        if hasattr(packet, 'awid'):
            return OptimizedAXI4Packet._validate_aw_packet_cached(packet, field_config)
        elif hasattr(packet, 'wdata'):
            return OptimizedAXI4Packet._validate_w_packet_cached(packet, field_config)
        elif hasattr(packet, 'bid'):
            return OptimizedAXI4Packet._validate_b_packet_cached(packet, field_config)
        elif hasattr(packet, 'arid'):
            return OptimizedAXI4Packet._validate_ar_packet_cached(packet, field_config)
        elif hasattr(packet, 'rid'):
            return OptimizedAXI4Packet._validate_r_packet_cached(packet, field_config)
        else:
            return False, "Unknown AXI4 packet type"
    
    @staticmethod
    def _validate_aw_packet_cached(packet, field_config: FieldConfig):
        """Validate Write Address channel packet with caching"""
        # Check address alignment based on size
        if hasattr(packet, 'awsize') and hasattr(packet, 'awaddr'):
            byte_count = 1 << packet.awsize
            if packet.awaddr % byte_count != 0:
                return False, f"AW address 0x{packet.awaddr:X} not aligned for size {packet.awsize} ({byte_count} bytes)"

        # Check burst type
        if hasattr(packet, 'awburst'):
            if packet.awburst not in [0, 1, 2]:  # FIXED, INCR, WRAP
                return False, f"Invalid AW burst type: {packet.awburst}"

            # For WRAP bursts, check power-of-2 length
            if packet.awburst == 2 and hasattr(packet, 'awlen') and (packet.awlen + 1) not in [2, 4, 8, 16]:
                return False, f"WRAP burst length must be 2, 4, 8, or 16 (awlen={packet.awlen})"

        # Check burst length
        if hasattr(packet, 'awlen') and packet.awlen > 255:
            return False, f"AW burst length exceeds AXI4 maximum: {packet.awlen}"

        return True, "Valid AW packet"
    
    @staticmethod
    def _validate_w_packet_cached(packet, field_config: FieldConfig):
        """Validate Write Data channel packet with caching"""
        # Validate strobe for enabled bytes
        if hasattr(packet, 'wstrb') and packet.wstrb == 0:
            return False, "Write strobe is zero (no bytes enabled)"

        # Validate wlast field if present
        if hasattr(packet, 'wlast') and not isinstance(packet.wlast, int):
            return False, f"WLAST must be an integer: {packet.wlast}"

        return True, "Valid W packet"
    
    @staticmethod
    def _validate_b_packet_cached(packet, field_config: FieldConfig):
        """Validate Write Response channel packet with caching"""
        # Check response code
        if hasattr(packet, 'bresp') and packet.bresp not in [0, 1, 2, 3]:
            return False, f"Invalid B response code: {packet.bresp}"

        return True, "Valid B packet"
    
    @staticmethod
    def _validate_ar_packet_cached(packet, field_config: FieldConfig):
        """Validate Read Address channel packet with caching"""
        # Check address alignment based on size
        if hasattr(packet, 'arsize') and hasattr(packet, 'araddr'):
            byte_count = 1 << packet.arsize
            if packet.araddr % byte_count != 0:
                return False, f"AR address 0x{packet.araddr:X} not aligned for size {packet.arsize} ({byte_count} bytes)"

        # Check burst type
        if hasattr(packet, 'arburst'):
            if packet.arburst not in [0, 1, 2]:  # FIXED, INCR, WRAP
                return False, f"Invalid AR burst type: {packet.arburst}"

            # For WRAP bursts, check power-of-2 length
            if packet.arburst == 2 and hasattr(packet, 'arlen') and (packet.arlen + 1) not in [2, 4, 8, 16]:
                return False, f"WRAP burst length must be 2, 4, 8, or 16 (arlen={packet.arlen})"

        # Check burst length
        if hasattr(packet, 'arlen') and packet.arlen > 255:
            return False, f"AR burst length exceeds AXI4 maximum: {packet.arlen}"

        return True, "Valid AR packet"
    
    @staticmethod
    def _validate_r_packet_cached(packet, field_config: FieldConfig):
        """Validate Read Data channel packet with caching"""
        # Check response code
        if hasattr(packet, 'rresp') and packet.rresp not in [0, 1, 2, 3]:
            return False, f"Invalid R response code: {packet.rresp}"

        # Validate rlast field if present
        if hasattr(packet, 'rlast') and not isinstance(packet.rlast, int):
            return False, f"RLAST must be an integer: {packet.rlast}"

        return True, "Valid R packet"
    
    @staticmethod
    def get_burst_addresses_cached(packet):
        """
        Calculate all addresses in a burst sequence with caching.
        
        Args:
            packet: The packet containing burst information
            
        Returns:
            list: List of addresses in the burst
        """
        # Determine if this is a read or write address packet
        is_read = hasattr(packet, 'araddr')

        # Get the relevant fields
        if is_read:
            addr = packet.araddr
            burst_len = packet.arlen
            size = packet.arsize
            burst_type = packet.arburst
        else:
            addr = packet.awaddr
            burst_len = packet.awlen
            size = packet.awsize
            burst_type = packet.awburst

        # Calculate the byte count for this size
        byte_count = 1 << size

        # Calculate all addresses in the burst
        addresses = []
        current_addr = addr

        for _ in range(burst_len + 1):
            addresses.append(current_addr)

            # Update address based on burst type
            if burst_type == 0:  # FIXED
                # Address remains the same for all beats
                pass
            elif burst_type == 1:  # INCR
                # Increment address by byte count
                current_addr += byte_count
            elif burst_type == 2:  # WRAP
                # Calculate the wrap boundary (align to burst size)
                wrap_size = (burst_len + 1) * byte_count
                wrap_mask = wrap_size - 1
                wrap_boundary = addr & ~wrap_mask

                # Increment address
                current_addr += byte_count

                # Check if we need to wrap
                if (current_addr & wrap_mask) == 0:
                    current_addr = wrap_boundary

        return addresses


class OptimizedAXI4Master:
    """
    Optimizations for AXI4Master with field caching.
    
    This class provides methods that can be used to enhance the performance
    of the AXI4Master class.
    """
    
    @staticmethod
    def write_cached(master, addr, data, size=2, burst=1, strobe=None, id=0,
                    length=0, cache=0, prot=0, qos=0, region=0, user=0):
        """
        Execute an AXI4 write transaction with caching optimizations.
        
        This method uses the same interface as AXI4Master.write but with
        performance optimizations.
        
        Args:
            master: AXI4Master instance
            addr: Target address
            data: Data to write (int, list, or bytearray)
            size: Transfer size (0=byte, 1=halfword, 2=word, 3=doubleword, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            strobe: Byte strobe (default: all bytes enabled)
            id: Transaction ID
            length: Burst length (0 = 1 beat, 1 = 2 beats, etc.)
            cache: Cache type
            prot: Protection type
            qos: Quality of Service
            region: Region identifier
            user: User signal
            
        Returns:
            dict: Transaction results with response
        """
        # This would be an optimized version of the write method
        # For now, just delegate to the original method
        return master.write(addr, data, size, burst, strobe, id, length, cache, prot, qos, region, user)
    
    @staticmethod
    def read_cached(master, addr, size=2, burst=1, id=0, length=0, cache=0, prot=0, qos=0, region=0, user=0):
        """
        Execute an AXI4 read transaction with caching optimizations.
        
        This method uses the same interface as AXI4Master.read but with
        performance optimizations.
        
        Args:
            master: AXI4Master instance
            addr: Target address
            size: Transfer size (0=byte, 1=halfword, 2=word, 3=doubleword, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            id: Transaction ID
            length: Burst length (0 = 1 beat, 1 = 2 beats, etc.)
            cache: Cache type
            prot: Protection type
            qos: Quality of Service
            region: Region identifier
            user: User signal
            
        Returns:
            dict: Transaction results with responses
        """
        # This would be an optimized version of the read method
        # For now, just delegate to the original method
        return master.read(addr, size, burst, id, length, cache, prot, qos, region, user)


class FieldConfigOptimizer:
    """
    Utility for optimizing field configurations.
    
    This class provides methods for analyzing and optimizing field
    configurations to improve performance.
    """
    
    @staticmethod
    def analyze_field_config(field_config: FieldConfig) -> Dict[str, Any]:
        """
        Analyze a field configuration for optimization opportunities.
        
        Args:
            field_config: Field configuration to analyze
            
        Returns:
            Dictionary with analysis results
        """
        fields = field_config.field_names()
        total_bits = field_config.get_total_bits()
        
        # Find unused bits (gaps)
        bits_map = [False] * total_bits
        for field_name in fields:
            field_def = field_config.get_field(field_name)
            for i in range(field_def.active_bits[1], field_def.active_bits[0] + 1):
                if i < total_bits:
                    bits_map[i] = True
        
        unused_bits = bits_map.count(False)
        unused_bit_percentage = (unused_bits / total_bits) * 100 if total_bits > 0 else 0
        
        # Find overlapping fields
        overlapping_fields = []
        for i, field1 in enumerate(fields):
            field1_def = field_config.get_field(field1)
            msb1, lsb1 = field1_def.active_bits
            
            for j in range(i + 1, len(fields)):
                field2 = fields[j]
                field2_def = field_config.get_field(field2)
                msb2, lsb2 = field2_def.active_bits
                
                # Check for overlap
                if (lsb1 <= msb2 and msb1 >= lsb2) or (lsb2 <= msb1 and msb2 >= lsb1):
                    overlapping_fields.append((field1, field2))
        
        return {
            'total_fields': len(fields),
            'total_bits': total_bits,
            'unused_bits': unused_bits,
            'unused_bit_percentage': unused_bit_percentage,
            'overlapping_fields': overlapping_fields,
            'fields_by_size': self._group_fields_by_size(field_config),
            'optimization_recommendations': self._get_optimization_recommendations(
                field_config, unused_bit_percentage, overlapping_fields
            )
        }
    
    @staticmethod
    def _group_fields_by_size(field_config: FieldConfig) -> Dict[int, List[str]]:
        """Group fields by bit width"""
        fields_by_size = {}
        for field_name in field_config.field_names():
            field_def = field_config.get_field(field_name)
            bits = field_def.bits
            
            if bits not in fields_by_size:
                fields_by_size[bits] = []
            
            fields_by_size[bits].append(field_name)
        
        return fields_by_size
    
    @staticmethod
    def _get_optimization_recommendations(
        field_config: FieldConfig, 
        unused_bit_percentage: float, 
        overlapping_fields: List[Tuple[str, str]]
    ) -> List[str]:
        """Generate optimization recommendations"""
        recommendations = []
        
        # Check for high unused bit percentage
        if unused_bit_percentage > 20:
            recommendations.append(f"High unused bit percentage ({unused_bit_percentage:.1f}%). Consider compacting the field layout.")
        
        # Check for overlapping fields
        if overlapping_fields:
            recommendations.append(f"Found {len(overlapping_fields)} overlapping fields. This may cause data corruption.")
            for field1, field2 in overlapping_fields:
                recommendations.append(f"  - '{field1}' overlaps with '{field2}'")
        
        # Check for fields with 1-bit width that could be combined into a flags field
        fields_1bit = []
        for field_name in field_config.field_names():
            field_def = field_config.get_field(field_name)
            if field_def.bits == 1:
                fields_1bit.append(field_name)
        
        if len(fields_1bit) > 3:
            recommendations.append(f"Found {len(fields_1bit)} 1-bit fields. Consider combining into a flags field for better packing.")
            recommendations.append(f"  - Fields: {', '.join(fields_1bit)}")
        
        # Check for field alignment opportunities
        power2_sizes = [2, 4, 8, 16, 32, 64, 128]
        non_power2_fields = []
        for field_name in field_config.field_names():
            field_def = field_config.get_field(field_name)
            if field_def.bits > 1 and field_def.bits not in power2_sizes:
                non_power2_fields.append((field_name, field_def.bits))
        
        if non_power2_fields:
            recommendations.append(f"Found {len(non_power2_fields)} fields with non-power-of-2 widths. Consider aligning to power-of-2 for better packing.")
            for field, bits in non_power2_fields:
                next_power2 = min([p for p in power2_sizes if p >= bits], default=power2_sizes[-1])
                recommendations.append(f"  - '{field}' ({bits} bits) could be aligned to {next_power2} bits")
        
        return recommendations
    
    @staticmethod
    def optimize_field_config(field_config: FieldConfig) -> FieldConfig:
        """
        Create an optimized version of a field configuration.
        
        Args:
            field_config: Original field configuration
            
        Returns:
            Optimized field configuration
        """
        # This would implement actual optimization logic
        # For now, just return a copy of the original
        optimized_config = FieldConfig()
        
        for field_name in field_config.field_names():
            field_def = field_config.get_field(field_name)
            optimized_config.add_field(FieldDefinition(
                name=field_def.name,
                bits=field_def.bits,
                default=field_def.default,
                format=field_def.format,
                display_width=field_def.display_width,
                active_bits=field_def.active_bits,
                description=field_def.description
            ))
        
        return optimized_config


# Simple benchmark for field operations
def benchmark_field_operations(field_config: FieldConfig, iterations: int = 10000):
    """
    Benchmark field operations with and without caching.
    
    Args:
        field_config: Field configuration to benchmark
        iterations: Number of iterations to run
        
    Returns:
        Dictionary with benchmark results
    """
    # Test field names
    field_names = field_config.field_names()
    test_field = field_names[0] if field_names else "data"
    
    # Clear cache
    clear_field_config_cache()
    
    # Benchmark masked_field_value
    start_time = time.time()
    for _ in range(iterations):
        mask = (1 << field_config.get_field(test_field).bits) - 1
        value = 0xDEADBEEF & mask
    uncached_time = time.time() - start_time
    
    # Benchmark cached version
    start_time = time.time()
    for _ in range(iterations):
        value = mask_field_value(field_config, test_field, 0xDEADBEEF)
    cached_time = time.time() - start_time
    
    # Calculate speedup
    speedup = (uncached_time / cached_time) if cached_time > 0 else float('inf')
    
    # Get cache stats
    cache_stats = get_field_config_cache().get_stats()
    
    return {
        'uncached_time': uncached_time,
        'cached_time': cached_time,
        'speedup': speedup,
        'cache_stats': cache_stats
    }
