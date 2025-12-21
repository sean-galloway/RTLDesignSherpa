# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5RandomizationConfig
# Purpose: AXI5 Randomization Config with support for AXI5-specific features.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Randomization Config - Enhanced randomization for AXI5 protocol verification.

This module provides AXI5-specific randomization that includes support for:
- Atomic operations (ATOP)
- Memory Tagging Extension (MTE)
- MPAM and MECID contexts
- Security (NSAID)
- Chunked transfers
- Poison indicators

Includes industry-specific profiles optimized for different use cases.
"""

from typing import Dict, List, Optional, Union, Any, Tuple
import random
import logging
from dataclasses import dataclass, field
from enum import Enum

from .axi5_field_configs import get_axi5_field_configs


class AXI5RandomizationProfile(Enum):
    """Predefined randomization profiles for different use cases."""
    BASIC = "basic"
    COMPLIANCE = "compliance"
    PERFORMANCE = "performance"
    STRESS = "stress"
    ATOMIC = "atomic"
    MTE = "mte"
    SECURITY = "security"
    AUTOMOTIVE = "automotive"
    DATACENTER = "datacenter"
    MOBILE = "mobile"
    CUSTOM = "custom"


class AXI5ProtocolMode(Enum):
    """AXI5 protocol operation modes."""
    STANDARD = "standard"
    EXCLUSIVE_ACCESS = "exclusive_access"
    ATOMIC_OPERATIONS = "atomic_operations"
    MEMORY_TAGGING = "memory_tagging"
    SECURE_ACCESS = "secure_access"
    CACHE_COHERENT = "cache_coherent"
    LOW_POWER = "low_power"
    HIGH_PERFORMANCE = "high_performance"


@dataclass
class AXI5ConstraintSet:
    """Enhanced constraint set for AXI5 randomization."""
    # Address constraints
    addr_min: int = 0x1000
    addr_max: int = 0xFFFF000
    addr_alignment: int = 4
    addr_ranges: Optional[List[Tuple[int, int]]] = None

    # Burst constraints
    burst_len_min: int = 1
    burst_len_max: int = 16
    burst_len_weights: Optional[Dict[int, float]] = None
    burst_types: List[int] = field(default_factory=lambda: [0, 1, 2])  # FIXED, INCR, WRAP
    burst_size_max: int = 3  # Up to 8 bytes

    # ID constraints
    id_min: int = 0
    id_max: int = 15
    id_weights: Optional[Dict[int, float]] = None

    # Protocol constraints
    exclusive_access_rate: float = 0.0
    error_injection_rate: float = 0.0

    # AXI5-specific: Atomic operations
    atomic_rate: float = 0.0
    atomic_types: List[int] = field(default_factory=lambda: [0x10, 0x20, 0x30, 0x31])

    # AXI5-specific: Memory Tagging Extension
    mte_rate: float = 0.0
    tag_operations: List[int] = field(default_factory=lambda: [0, 1, 2, 3])
    tag_value_range: Tuple[int, int] = (0, 15)

    # AXI5-specific: Security context
    security_rate: float = 0.0
    nsaid_range: Tuple[int, int] = (0, 15)
    mpam_range: Tuple[int, int] = (0, 2047)
    mecid_range: Tuple[int, int] = (0, 65535)

    # AXI5-specific: Tracing
    trace_rate: float = 0.0

    # AXI5-specific: Chunking
    chunking_rate: float = 0.0
    chunk_num_range: Tuple[int, int] = (0, 15)

    # AXI5-specific: Poison
    poison_rate: float = 0.0

    # AXI5-specific: Unique access
    unique_rate: float = 0.0

    # Performance constraints
    data_patterns: List[str] = field(default_factory=lambda: ['random', 'incremental', 'pattern'])
    strobe_patterns: List[str] = field(default_factory=lambda: ['all', 'partial', 'sparse'])

    # Timing constraints
    min_delay_cycles: int = 0
    max_delay_cycles: int = 10
    ready_probability: float = 0.8


class AXI5RandomizationConfig:
    """
    Enhanced AXI5 randomization configuration.

    Provides sophisticated protocol-aware randomization with:
    - Support for all AXI5-specific features
    - Industry-specific randomization profiles
    - Advanced constraint management
    """

    def __init__(self, profile: AXI5RandomizationProfile = AXI5RandomizationProfile.BASIC,
                 data_width: int = 32, id_width: int = 8, addr_width: int = 32,
                 user_width: int = 1, nsaid_width: int = 4, mpam_width: int = 11,
                 mecid_width: int = 16, log: Optional[logging.Logger] = None):
        """
        Initialize AXI5 randomization configuration.

        Args:
            profile: Predefined randomization profile
            data_width: Data width in bits
            id_width: ID width in bits
            addr_width: Address width in bits
            user_width: User signal width in bits
            nsaid_width: NSAID width in bits
            mpam_width: MPAM width in bits
            mecid_width: MECID width in bits
            log: Logger instance
        """
        self.profile = profile
        self.data_width = data_width
        self.id_width = id_width
        self.addr_width = addr_width
        self.user_width = user_width
        self.nsaid_width = nsaid_width
        self.mpam_width = mpam_width
        self.mecid_width = mecid_width
        self.log = log or logging.getLogger("AXI5RandomizationConfig")

        # Get unified field configurations
        self.field_configs = get_axi5_field_configs(
            id_width, addr_width, data_width, user_width,
            nsaid_width, mpam_width, mecid_width
        )

        # Initialize constraints based on profile
        self.constraints = self._create_profile_constraints(profile)

        # Protocol mode and features
        self.protocol_mode = AXI5ProtocolMode.STANDARD
        self.enabled_features = set()
        self.master_mode = True

        # Statistics
        self.stats = {
            'randomizations_performed': 0,
            'fields_randomized': 0,
            'constraint_violations': 0,
            'profile_switches': 0,
            'atomic_operations': 0,
            'mte_operations': 0,
            'security_operations': 0
        }

        # Caching for performance
        self._cached_ranges = {}
        self._cached_weights = {}

        self.log.info(f"Initialized AXI5 randomization with profile: {profile.value}")

    def _create_profile_constraints(self, profile: AXI5RandomizationProfile) -> AXI5ConstraintSet:
        """Create constraint set based on profile."""
        if profile == AXI5RandomizationProfile.BASIC:
            return AXI5ConstraintSet()

        elif profile == AXI5RandomizationProfile.COMPLIANCE:
            return AXI5ConstraintSet(
                burst_len_max=16,
                burst_types=[1],  # Only INCR for compliance
                error_injection_rate=0.0,
                exclusive_access_rate=0.0,
                data_patterns=['incremental', 'pattern'],
                ready_probability=0.9
            )

        elif profile == AXI5RandomizationProfile.PERFORMANCE:
            return AXI5ConstraintSet(
                burst_len_min=4,
                burst_len_max=256,
                burst_len_weights={16: 0.3, 32: 0.3, 64: 0.2, 128: 0.1, 256: 0.1},
                burst_types=[1],  # INCR for performance
                data_patterns=['random'],
                min_delay_cycles=0,
                max_delay_cycles=2,
                ready_probability=0.95
            )

        elif profile == AXI5RandomizationProfile.STRESS:
            return AXI5ConstraintSet(
                burst_len_min=1,
                burst_len_max=256,
                burst_types=[0, 1, 2],
                error_injection_rate=0.02,
                exclusive_access_rate=0.1,
                atomic_rate=0.1,
                mte_rate=0.1,
                security_rate=0.1,
                trace_rate=0.1,
                poison_rate=0.02,
                data_patterns=['random', 'incremental', 'pattern'],
                min_delay_cycles=0,
                max_delay_cycles=20,
                ready_probability=0.6
            )

        elif profile == AXI5RandomizationProfile.ATOMIC:
            return AXI5ConstraintSet(
                burst_len_max=1,  # Atomic operations are single-beat
                burst_types=[1],
                atomic_rate=1.0,  # Always generate atomic operations
                atomic_types=[0x10, 0x20, 0x30, 0x31],
                data_patterns=['random'],
                ready_probability=0.8
            )

        elif profile == AXI5RandomizationProfile.MTE:
            return AXI5ConstraintSet(
                mte_rate=1.0,  # Always use MTE
                tag_operations=[1, 2, 3],  # Transfer, Update, Match
                tag_value_range=(0, 15),
                data_patterns=['random', 'pattern'],
                ready_probability=0.8
            )

        elif profile == AXI5RandomizationProfile.SECURITY:
            return AXI5ConstraintSet(
                security_rate=1.0,  # Always use security context
                nsaid_range=(0, 15),
                mpam_range=(0, 2047),
                mecid_range=(0, 65535),
                trace_rate=0.5,  # 50% tracing for security audit
                data_patterns=['random', 'pattern'],
                ready_probability=0.85
            )

        elif profile == AXI5RandomizationProfile.AUTOMOTIVE:
            return AXI5ConstraintSet(
                burst_len_max=16,
                burst_types=[1],
                error_injection_rate=0.001,
                exclusive_access_rate=0.0,
                atomic_rate=0.0,  # Minimize complexity
                mte_rate=0.0,
                poison_rate=0.0,
                data_patterns=['incremental', 'pattern'],
                ready_probability=0.95,
                addr_alignment=8
            )

        elif profile == AXI5RandomizationProfile.DATACENTER:
            return AXI5ConstraintSet(
                burst_len_min=8,
                burst_len_max=256,
                burst_len_weights={64: 0.4, 128: 0.3, 256: 0.3},
                burst_types=[1],
                atomic_rate=0.05,  # Some atomic for synchronization
                security_rate=0.5,  # Security context often used
                data_patterns=['random'],
                min_delay_cycles=0,
                max_delay_cycles=1,
                ready_probability=0.98,
                addr_alignment=64
            )

        elif profile == AXI5RandomizationProfile.MOBILE:
            return AXI5ConstraintSet(
                burst_len_max=32,
                burst_len_weights={1: 0.3, 2: 0.2, 4: 0.2, 8: 0.2, 16: 0.1},
                burst_types=[1],
                mte_rate=0.1,  # Some MTE for memory safety
                data_patterns=['pattern'],
                min_delay_cycles=1,
                max_delay_cycles=5,
                ready_probability=0.8,
                addr_alignment=4
            )

        else:  # CUSTOM
            return AXI5ConstraintSet()

    def randomize_fields(self, field_requests: Dict[str, Any]) -> Dict[str, Any]:
        """
        Randomize AXI5 fields according to constraints and protocol rules.
        """
        self.stats['randomizations_performed'] += 1
        randomized = {}

        for field_name, constraints in field_requests.items():
            if field_name in self._get_supported_fields():
                value = self._randomize_single_field(field_name, constraints)
                randomized[field_name] = value
                self.stats['fields_randomized'] += 1
            else:
                self.log.warning(f"Unsupported field for randomization: {field_name}")

        # Apply cross-field constraints and protocol rules
        randomized = self._apply_protocol_constraints(randomized)

        # Apply AXI5-specific constraints
        randomized = self._apply_axi5_constraints(randomized)

        return randomized

    def _randomize_single_field(self, field_name: str, constraints: Any) -> Any:
        """Randomize a single field with AXI5-specific intelligence."""
        field_lower = field_name.lower()

        if 'addr' in field_lower:
            return self._randomize_address_field(field_name, constraints)
        elif 'data' in field_lower:
            return self._randomize_data_field(field_name, constraints)
        elif 'id' in field_lower and 'nsaid' not in field_lower and 'mecid' not in field_lower:
            return self._randomize_id_field(field_name, constraints)
        elif 'len' in field_lower:
            return self._randomize_length_field(field_name, constraints)
        elif 'size' in field_lower:
            return self._randomize_size_field(field_name, constraints)
        elif 'burst' in field_lower:
            return self._randomize_burst_field(field_name, constraints)
        elif 'atop' in field_lower:
            return self._randomize_atop_field(field_name, constraints)
        elif 'tagop' in field_lower:
            return self._randomize_tagop_field(field_name, constraints)
        elif 'tag' in field_lower and 'tagop' not in field_lower and 'tagmatch' not in field_lower:
            return self._randomize_tag_field(field_name, constraints)
        elif 'nsaid' in field_lower:
            return self._randomize_nsaid_field(field_name, constraints)
        elif 'mpam' in field_lower:
            return self._randomize_mpam_field(field_name, constraints)
        elif 'mecid' in field_lower:
            return self._randomize_mecid_field(field_name, constraints)
        elif 'resp' in field_lower:
            return self._randomize_response_field(field_name, constraints)
        elif 'poison' in field_lower:
            return self._randomize_poison_field(field_name, constraints)
        elif 'trace' in field_lower:
            return self._randomize_trace_field(field_name, constraints)
        elif 'unique' in field_lower:
            return self._randomize_unique_field(field_name, constraints)
        elif 'chunk' in field_lower:
            return self._randomize_chunk_field(field_name, constraints)
        else:
            return self._randomize_generic_field(field_name, constraints)

    def _randomize_address_field(self, field_name: str, constraints: Any) -> int:
        """Randomize address fields with alignment and range constraints."""
        if isinstance(constraints, dict):
            min_addr = constraints.get('min', self.constraints.addr_min)
            max_addr = constraints.get('max', self.constraints.addr_max)
            alignment = constraints.get('align', self.constraints.addr_alignment)
        else:
            min_addr = self.constraints.addr_min
            max_addr = self.constraints.addr_max
            alignment = self.constraints.addr_alignment

        # Ensure alignment
        min_addr = (min_addr + alignment - 1) // alignment * alignment
        max_addr = max_addr // alignment * alignment

        if min_addr > max_addr:
            return self.constraints.addr_min

        # Generate aligned address
        aligned_range = (max_addr - min_addr) // alignment
        if aligned_range <= 0:
            return min_addr

        return min_addr + random.randint(0, aligned_range) * alignment

    def _randomize_data_field(self, field_name: str, constraints: Any) -> int:
        """Randomize data fields with pattern support."""
        if isinstance(constraints, dict):
            width = constraints.get('width', self.data_width)
            pattern = constraints.get('pattern', 'random')
        else:
            width = self.data_width
            pattern = random.choice(self.constraints.data_patterns)

        max_value = (1 << width) - 1
        return self._generate_data_value(pattern, width, max_value)

    def _generate_data_value(self, pattern: str, width: int, max_value: int, index: int = 0) -> int:
        """Generate data value based on pattern."""
        if pattern == 'random':
            return random.randint(0, max_value)
        elif pattern == 'incremental':
            base = random.randint(0, max_value - 256) if max_value > 256 else 0
            return (base + index) & max_value
        elif pattern == 'pattern':
            patterns = [0x55555555, 0xAAAAAAAA, 0x33333333, 0xCCCCCCCC]
            return patterns[index % len(patterns)] & max_value
        else:
            return random.randint(0, max_value)

    def _randomize_response_field(self, field_name: str, constraints: Any) -> int:
        """Randomize response fields with error injection support."""
        if random.random() < self.constraints.error_injection_rate:
            return random.choice([2, 3])  # SLVERR or DECERR
        else:
            if self.protocol_mode == AXI5ProtocolMode.EXCLUSIVE_ACCESS:
                return random.choice([0, 1])  # OKAY or EXOKAY
            else:
                return 0  # OKAY

    def _randomize_id_field(self, field_name: str, constraints: Any) -> int:
        """Randomize ID fields with weighting support."""
        max_id = (1 << self.id_width) - 1

        if isinstance(constraints, dict):
            min_id = constraints.get('min', self.constraints.id_min)
            max_id = min(constraints.get('max', max_id), max_id)
        else:
            min_id = self.constraints.id_min
            max_id = min(self.constraints.id_max, max_id)

        return random.randint(min_id, max_id)

    def _randomize_length_field(self, field_name: str, constraints: Any) -> int:
        """Randomize burst length."""
        if isinstance(constraints, dict):
            min_len = constraints.get('min', self.constraints.burst_len_min)
            max_len = constraints.get('max', self.constraints.burst_len_max)
        else:
            min_len = self.constraints.burst_len_min
            max_len = self.constraints.burst_len_max

        if self.constraints.burst_len_weights:
            valid_lengths = [length for length in self.constraints.burst_len_weights.keys()
                            if min_len <= length <= max_len]
            if valid_lengths:
                weights = [self.constraints.burst_len_weights[length] for length in valid_lengths]
                return random.choices(valid_lengths, weights=weights)[0] - 1

        return random.randint(min_len, max_len) - 1

    def _randomize_size_field(self, field_name: str, constraints: Any) -> int:
        """Randomize transfer size field."""
        max_size = self.constraints.burst_size_max
        data_width_size = (self.data_width // 8).bit_length() - 1
        max_size = min(max_size, data_width_size)
        return random.randint(0, max_size)

    def _randomize_burst_field(self, field_name: str, constraints: Any) -> int:
        """Randomize burst type field."""
        return random.choice(self.constraints.burst_types)

    def _randomize_atop_field(self, field_name: str, constraints: Any) -> int:
        """Randomize atomic operation type."""
        if random.random() < self.constraints.atomic_rate:
            self.stats['atomic_operations'] += 1
            return random.choice(self.constraints.atomic_types)
        return 0

    def _randomize_tagop_field(self, field_name: str, constraints: Any) -> int:
        """Randomize tag operation."""
        if random.random() < self.constraints.mte_rate:
            self.stats['mte_operations'] += 1
            return random.choice(self.constraints.tag_operations)
        return 0

    def _randomize_tag_field(self, field_name: str, constraints: Any) -> int:
        """Randomize memory tag value."""
        tag_min, tag_max = self.constraints.tag_value_range
        return random.randint(tag_min, tag_max)

    def _randomize_nsaid_field(self, field_name: str, constraints: Any) -> int:
        """Randomize NSAID."""
        if random.random() < self.constraints.security_rate:
            self.stats['security_operations'] += 1
            nsaid_min, nsaid_max = self.constraints.nsaid_range
            return random.randint(nsaid_min, nsaid_max)
        return 0

    def _randomize_mpam_field(self, field_name: str, constraints: Any) -> int:
        """Randomize MPAM."""
        if random.random() < self.constraints.security_rate:
            mpam_min, mpam_max = self.constraints.mpam_range
            return random.randint(mpam_min, mpam_max)
        return 0

    def _randomize_mecid_field(self, field_name: str, constraints: Any) -> int:
        """Randomize MECID."""
        if random.random() < self.constraints.security_rate:
            mecid_min, mecid_max = self.constraints.mecid_range
            return random.randint(mecid_min, mecid_max)
        return 0

    def _randomize_poison_field(self, field_name: str, constraints: Any) -> int:
        """Randomize poison indicator."""
        return 1 if random.random() < self.constraints.poison_rate else 0

    def _randomize_trace_field(self, field_name: str, constraints: Any) -> int:
        """Randomize trace indicator."""
        return 1 if random.random() < self.constraints.trace_rate else 0

    def _randomize_unique_field(self, field_name: str, constraints: Any) -> int:
        """Randomize unique access indicator."""
        return 1 if random.random() < self.constraints.unique_rate else 0

    def _randomize_chunk_field(self, field_name: str, constraints: Any) -> int:
        """Randomize chunk-related fields."""
        if 'chunken' in field_name.lower():
            return 1 if random.random() < self.constraints.chunking_rate else 0
        elif 'chunknum' in field_name.lower():
            chunk_min, chunk_max = self.constraints.chunk_num_range
            return random.randint(chunk_min, chunk_max)
        elif 'chunkv' in field_name.lower():
            return 1 if random.random() < self.constraints.chunking_rate else 0
        elif 'chunkstrb' in field_name.lower():
            num_chunks = max(1, self.data_width // 128)
            return (1 << num_chunks) - 1
        return 0

    def _randomize_generic_field(self, field_name: str, constraints: Any) -> int:
        """Generic field randomization."""
        if isinstance(constraints, dict):
            min_val = constraints.get('min', 0)
            max_val = constraints.get('max', 255)
            return random.randint(min_val, max_val)
        return 0

    def _apply_protocol_constraints(self, randomized: Dict[str, Any]) -> Dict[str, Any]:
        """Apply AXI5 protocol constraints."""
        # Address and size alignment
        if 'awaddr' in randomized and 'awsize' in randomized:
            alignment = 1 << randomized['awsize']
            randomized['awaddr'] = (randomized['awaddr'] // alignment) * alignment

        if 'araddr' in randomized and 'arsize' in randomized:
            alignment = 1 << randomized['arsize']
            randomized['araddr'] = (randomized['araddr'] // alignment) * alignment

        return randomized

    def _apply_axi5_constraints(self, randomized: Dict[str, Any]) -> Dict[str, Any]:
        """Apply AXI5-specific constraints."""
        # Atomic operations require single-beat transfers
        if randomized.get('atop', 0) != 0:
            if 'awlen' in randomized:
                randomized['awlen'] = 0  # Single beat for atomic

        # Chunking requires data width >= 128 bits
        if self.data_width < 128:
            if 'chunken' in randomized:
                randomized['chunken'] = 0
            if 'chunkv' in randomized:
                randomized['chunkv'] = 0

        return randomized

    def _get_supported_fields(self) -> List[str]:
        """Get list of supported randomization fields."""
        return list(self.field_configs.keys())

    # Configuration methods

    def set_profile(self, profile: AXI5RandomizationProfile):
        """Change randomization profile."""
        if profile != self.profile:
            self.profile = profile
            self.constraints = self._create_profile_constraints(profile)
            self.stats['profile_switches'] += 1
            self.log.info(f"Switched to profile: {profile.value}")

    def set_data_width(self, width: int):
        """Update data width and reconfigure fields."""
        self.data_width = width
        self.field_configs = get_axi5_field_configs(
            self.id_width, self.addr_width, width, self.user_width,
            self.nsaid_width, self.mpam_width, self.mecid_width
        )

    def set_master_mode(self, is_master: bool):
        """Configure for master or slave operation."""
        self.master_mode = is_master
        if is_master:
            self.constraints.error_injection_rate = 0.0
        else:
            if self.constraints.error_injection_rate == 0.0:
                self.constraints.error_injection_rate = 0.01

    def set_error_injection_rate(self, rate: float):
        """Set error injection rate (0.0 to 1.0)."""
        self.constraints.error_injection_rate = max(0.0, min(1.0, rate))

    def set_atomic_rate(self, rate: float):
        """Set atomic operation rate (0.0 to 1.0)."""
        self.constraints.atomic_rate = max(0.0, min(1.0, rate))

    def set_mte_rate(self, rate: float):
        """Set Memory Tagging Extension rate (0.0 to 1.0)."""
        self.constraints.mte_rate = max(0.0, min(1.0, rate))

    def set_security_rate(self, rate: float):
        """Set security context rate (0.0 to 1.0)."""
        self.constraints.security_rate = max(0.0, min(1.0, rate))

    def set_trace_rate(self, rate: float):
        """Set transaction trace rate (0.0 to 1.0)."""
        self.constraints.trace_rate = max(0.0, min(1.0, rate))

    def enable_atomic_operations(self, types: Optional[List[int]] = None):
        """Enable atomic operations."""
        self.protocol_mode = AXI5ProtocolMode.ATOMIC_OPERATIONS
        self.constraints.atomic_rate = 0.5
        if types:
            self.constraints.atomic_types = types

    def enable_memory_tagging(self, operations: Optional[List[int]] = None):
        """Enable Memory Tagging Extension."""
        self.protocol_mode = AXI5ProtocolMode.MEMORY_TAGGING
        self.constraints.mte_rate = 0.5
        if operations:
            self.constraints.tag_operations = operations

    def enable_secure_access(self):
        """Enable security context generation."""
        self.protocol_mode = AXI5ProtocolMode.SECURE_ACCESS
        self.constraints.security_rate = 1.0
        self.constraints.trace_rate = 0.5

    def get_statistics(self) -> Dict[str, Any]:
        """Get comprehensive randomization statistics."""
        stats = self.stats.copy()
        stats['profile'] = self.profile.value
        stats['protocol_mode'] = self.protocol_mode.value
        stats['data_width'] = self.data_width
        stats['enabled_features'] = list(self.enabled_features)

        if stats['randomizations_performed'] > 0:
            stats['fields_per_randomization'] = stats['fields_randomized'] / stats['randomizations_performed']
        else:
            stats['fields_per_randomization'] = 0.0

        return stats

    def reset_statistics(self):
        """Reset all statistics counters."""
        self.stats = {key: 0 for key in self.stats}
        self._cached_ranges.clear()
        self._cached_weights.clear()


# Factory functions

def create_atomic_randomization_config(data_width: int = 32) -> AXI5RandomizationConfig:
    """Create randomization config for atomic operations testing."""
    config = AXI5RandomizationConfig(
        profile=AXI5RandomizationProfile.ATOMIC,
        data_width=data_width
    )
    config.enable_atomic_operations()
    return config


def create_mte_randomization_config(data_width: int = 32) -> AXI5RandomizationConfig:
    """Create randomization config for Memory Tagging Extension testing."""
    config = AXI5RandomizationConfig(
        profile=AXI5RandomizationProfile.MTE,
        data_width=data_width
    )
    config.enable_memory_tagging()
    return config


def create_security_randomization_config(data_width: int = 32) -> AXI5RandomizationConfig:
    """Create randomization config for security testing."""
    config = AXI5RandomizationConfig(
        profile=AXI5RandomizationProfile.SECURITY,
        data_width=data_width
    )
    config.enable_secure_access()
    return config


def create_compliance_randomization_config(data_width: int = 32) -> AXI5RandomizationConfig:
    """Create randomization config for AXI5 compliance testing."""
    return AXI5RandomizationConfig(
        profile=AXI5RandomizationProfile.COMPLIANCE,
        data_width=data_width
    )
