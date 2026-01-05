<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# gaxi_buffer_seq.py

Extended GAXI buffer sequence classes with FlexConfigGen integration. This module provides comprehensive sequence generation capabilities for GAXI buffer testing, supporting multiple randomization profiles and sophisticated pattern generation.

## Overview

The `GAXIBufferSequence` class extends the base `GAXISequence` to provide specialized pattern generation suitable for GAXI buffer component testing. It has been refactored to use FlexConfigGen exclusively for all randomization needs, eliminating manual FlexRandomizer instantiation and providing consistent randomization architecture.

### Key Features
- **FlexConfigGen-only randomization** - Eliminated manual FlexRandomizer instantiation
- **Multiple field support** (addr, ctrl, data0, data1)
- **Comprehensive pattern generation** methods
- **Profile-based randomization** with predefined and custom profiles
- **Enhanced sequence capabilities** for buffer testing
- **Dependency tracking** and constraint management
- **Incremental and burst patterns** support

### Supported Field Configurations
- Multi-field packets with addr, ctrl, data0, data1
- Configurable field widths and constraints
- Independent field randomization profiles
- Cross-field dependency validation

## Class Definition

```python
class GAXIBufferSequence(GAXISequence):
    """
    Extended sequence generator for GAXI buffer tests using FlexConfigGen only.
    
    This class expands on the base GAXISequence to add specific patterns and
    sequences suitable for testing GAXI buffer components with multiple fields
    (addr, ctrl, data0, data1).
    
    Refactored to use FlexConfigGen for all randomization needs.
    """
    
    def __init__(self, name, field_config, packet_class=GAXIPacket):
```

## Initialization and Configuration

### Constructor Parameters

```python
def __init__(self, name, field_config, packet_class=GAXIPacket):
    """
    Initialize the GAXI buffer sequence with FlexConfigGen integration.
    
    Parameters:
    - name: Sequence name for identification
    - field_config: FieldConfig object defining packet structure
    - packet_class: Packet class to use (default: GAXIPacket)
    """
    
    super().__init__(name, field_config, packet_class)
    
    # Initialize FlexConfigGen for randomization
    self.flex_config_gen = FlexConfigGen()
    self.randomization_profiles = {}
    
    # Create default randomization profiles
    self._create_default_profiles()
    
    # Sequence tracking
    self.generated_sequences = []
    self.sequence_statistics = {}
```

### Default Randomization Profiles

The sequence class creates comprehensive default profiles:

```python
def _create_default_profiles(self):
    """Create default randomization profiles for GAXI buffer testing"""
    
    # Get field constraints from field config
    field_constraints = self._extract_field_constraints()
    
    # Define profiles with different characteristics
    profile_definitions = {
        'uniform': {
            'description': 'Uniform distribution across all field ranges',
            'constraints': self._create_uniform_constraints(field_constraints)
        },
        'weighted': {
            'description': 'Weighted distribution favoring common values',
            'constraints': self._create_weighted_constraints(field_constraints)
        },
        'corner': {
            'description': 'Corner cases and boundary values',
            'constraints': self._create_corner_constraints(field_constraints)
        },
        'burst': {
            'description': 'Burst patterns with incremental values',
            'constraints': self._create_burst_constraints(field_constraints)
        },
        'sparse': {
            'description': 'Sparse patterns with mostly zero/minimum values',
            'constraints': self._create_sparse_constraints(field_constraints)
        },
        'constrained': {
            'description': 'Constrained patterns with specific relationships',
            'constraints': self._create_constrained_constraints(field_constraints)
        }
    }
    
    # Create randomizers for each profile
    for profile_name, profile_def in profile_definitions.items():
        try:
            randomizer = self.flex_config_gen.create_randomizer(profile_def['constraints'])
            self.randomization_profiles[profile_name] = {
                'randomizer': randomizer,
                'description': profile_def['description'],
                'constraints': profile_def['constraints']
            }
            self.log.debug(f"Created randomization profile: {profile_name}")
        except Exception as e:
            self.log.error(f"Failed to create profile {profile_name}: {e}")

def _extract_field_constraints(self):
    """Extract field constraints from field configuration"""
    constraints = {}
    
    for field_name in ['addr', 'ctrl', 'data0', 'data1']:
        field_def = self.field_config.get_field(field_name)
        if field_def:
            max_value = (1 << field_def.bits) - 1
            constraints[field_name] = {
                'min': 0,
                'max': max_value,
                'bits': field_def.bits,
                'default': field_def.default
            }
    
    return constraints

def _create_uniform_constraints(self, field_constraints):
    """Create uniform distribution constraints"""
    constraints = {}
    
    for field_name, field_info in field_constraints.items():
        constraints[f'{field_name}_constraint'] = {
            'uniform': (field_info['min'], field_info['max'])
        }
    
    return constraints

def _create_weighted_constraints(self, field_constraints):
    """Create weighted distribution constraints"""
    constraints = {}
    
    for field_name, field_info in field_constraints.items():
        max_val = field_info['max']
        
        if field_name == 'addr':
            # Address: favor aligned addresses
            constraints[f'{field_name}_constraint'] = {
                'weighted': ([(0, max_val//4), (max_val//4, max_val)], [0.7, 0.3])
            }
        elif field_name == 'ctrl':
            # Control: favor common command values
            if max_val >= 7:
                constraints[f'{field_name}_constraint'] = {
                    'weighted': ([(0, 3), (4, max_val)], [0.8, 0.2])
                }
            else:
                constraints[f'{field_name}_constraint'] = {
                    'uniform': (0, max_val)
                }
        else:
            # Data: weighted toward middle values
            constraints[f'{field_name}_constraint'] = {
                'weighted': ([(0, max_val//3), (max_val//3, max_val)], [0.4, 0.6])
            }
    
    return constraints

def _create_corner_constraints(self, field_constraints):
    """Create corner case constraints"""
    constraints = {}
    
    for field_name, field_info in field_constraints.items():
        max_val = field_info['max']
        
        # Define corner values
        corner_values = [0, 1]
        if max_val > 1:
            corner_values.extend([max_val//2, max_val-1, max_val])
        
        # Equal probability for corner cases
        probabilities = [1.0/len(corner_values)] * len(corner_values)
        
        constraints[f'{field_name}_constraint'] = {
            'corner': (corner_values, probabilities)
        }
    
    return constraints

def _create_burst_constraints(self, field_constraints):
    """Create burst pattern constraints"""
    constraints = {}
    
    for field_name, field_info in field_constraints.items():
        if field_name in ['data0', 'data1']:
            # Data fields use incremental patterns
            constraints[f'{field_name}_constraint'] = {
                'pattern': 'incremental'
            }
        elif field_name == 'addr':
            # Address increments by 4 for alignment
            constraints[f'{field_name}_constraint'] = {
                'pattern': 'incremental_aligned_4'
            }
        else:
            # Control fields cycle through small values
            constraints[f'{field_name}_constraint'] = {
                'pattern': 'cycle_0_to_7'
            }
    
    return constraints
```

## Core Sequence Generation Methods

### Basic Random Patterns

```python
def add_random_pattern(self, length, profile='uniform'):
    """
    Add random pattern using specified profile
    
    Parameters:
    - length: Number of packets to generate
    - profile: Randomization profile to use
    
    Returns: Generated packet sequence
    """
    
    if profile not in self.randomization_profiles:
        self.log.error(f"Unknown randomization profile: {profile}")
        return []
    
    randomizer = self.randomization_profiles[profile]['randomizer']
    packets = []
    
    for i in range(length):
        packet = self.packet_class(self.field_config)
        
        # Generate values for each field using profile
        for field_name in ['addr', 'ctrl', 'data0', 'data1']:
            constraint_name = f'{field_name}_constraint'
            if hasattr(randomizer, 'generate'):
                value = randomizer.generate(constraint_name)
                setattr(packet, field_name, value)
        
        # Add packet metadata
        packet.sequence_id = len(self.generated_sequences)
        packet.packet_id = i
        packet.profile = profile
        
        packets.append(packet)
    
    # Track generated sequence
    sequence_info = {
        'name': f'{self.name}_random_{profile}_{len(self.generated_sequences)}',
        'type': 'random',
        'profile': profile,
        'length': length,
        'packets': packets
    }
    
    self.generated_sequences.append(sequence_info)
    self._update_statistics('random', profile, length)
    
    self.log.info(f"Generated random pattern: {length} packets using {profile} profile")
    return packets

def add_weighted_random_pattern(self, length, field_weights=None):
    """
    Add weighted random pattern with custom field weights
    
    Parameters:
    - length: Number of packets to generate
    - field_weights: Custom weights for field value distributions
    
    Returns: Generated packet sequence
    """
    
    # Use default weighted profile or create custom
    if field_weights:
        custom_constraints = self._create_custom_weighted_constraints(field_weights)
        custom_randomizer = self.flex_config_gen.create_randomizer(custom_constraints)
        randomizer = custom_randomizer
        profile_name = 'custom_weighted'
    else:
        randomizer = self.randomization_profiles['weighted']['randomizer']
        profile_name = 'weighted'
    
    packets = []
    
    for i in range(length):
        packet = self.packet_class(self.field_config)
        
        # Generate weighted values
        for field_name in ['addr', 'ctrl', 'data0', 'data1']:
            constraint_name = f'{field_name}_constraint'
            value = randomizer.generate(constraint_name)
            setattr(packet, field_name, value)
        
        packet.sequence_id = len(self.generated_sequences)
        packet.packet_id = i
        packet.profile = profile_name
        
        packets.append(packet)
    
    sequence_info = {
        'name': f'{self.name}_weighted_{len(self.generated_sequences)}',
        'type': 'weighted_random',
        'profile': profile_name,
        'length': length,
        'packets': packets,
        'custom_weights': field_weights
    }
    
    self.generated_sequences.append(sequence_info)
    self._update_statistics('weighted_random', profile_name, length)
    
    return packets
```

### Specialized Pattern Generation

```python
def add_corner_case_pattern(self):
    """
    Add comprehensive corner case pattern
    
    Returns: Corner case packet sequence
    """
    
    corner_packets = []
    corner_randomizer = self.randomization_profiles['corner']['randomizer']
    
    # Generate all corner case combinations
    field_names = ['addr', 'ctrl', 'data0', 'data1']
    
    # Individual field corner cases
    for field_name in field_names:
        field_def = self.field_config.get_field(field_name)
        if field_def:
            max_val = (1 << field_def.bits) - 1
            corner_values = [0, 1, max_val//2, max_val-1, max_val]
            
            for corner_val in corner_values:
                packet = self.packet_class(self.field_config)
                
                # Set corner value for target field, random for others
                for other_field in field_names:
                    if other_field == field_name:
                        setattr(packet, other_field, corner_val)
                    else:
                        constraint_name = f'{other_field}_constraint'
                        random_val = corner_randomizer.generate(constraint_name)
                        setattr(packet, other_field, random_val)
                
                packet.sequence_id = len(self.generated_sequences)
                packet.packet_id = len(corner_packets)
                packet.profile = 'corner'
                packet.corner_field = field_name
                packet.corner_value = corner_val
                
                corner_packets.append(packet)
    
    # All-maximum and all-minimum cases
    for extreme_case in ['all_min', 'all_max']:
        packet = self.packet_class(self.field_config)
        
        for field_name in field_names:
            field_def = self.field_config.get_field(field_name)
            if field_def:
                if extreme_case == 'all_min':
                    setattr(packet, field_name, 0)
                else:
                    max_val = (1 << field_def.bits) - 1
                    setattr(packet, field_name, max_val)
        
        packet.sequence_id = len(self.generated_sequences)
        packet.packet_id = len(corner_packets)
        packet.profile = 'corner'
        packet.extreme_case = extreme_case
        
        corner_packets.append(packet)
    
    sequence_info = {
        'name': f'{self.name}_corner_{len(self.generated_sequences)}',
        'type': 'corner_case',
        'profile': 'corner',
        'length': len(corner_packets),
        'packets': corner_packets
    }
    
    self.generated_sequences.append(sequence_info)
    self._update_statistics('corner_case', 'corner', len(corner_packets))
    
    self.log.info(f"Generated corner case pattern: {len(corner_packets)} packets")
    return corner_packets

def add_burst_pattern(self, burst_size, num_bursts, base_addr=0x1000):
    """
    Add burst pattern with incremental addressing
    
    Parameters:
    - burst_size: Number of packets per burst
    - num_bursts: Number of burst sequences
    - base_addr: Starting address for bursts
    
    Returns: Burst packet sequence
    """
    
    burst_packets = []
    burst_randomizer = self.randomization_profiles['burst']['randomizer']
    
    current_addr = base_addr
    
    for burst_num in range(num_bursts):
        # Generate burst sequence
        for packet_in_burst in range(burst_size):
            packet = self.packet_class(self.field_config)
            
            # Incremental addressing within burst
            packet.addr = current_addr + (packet_in_burst * 4)  # 4-byte aligned
            
            # Control field indicates burst info
            packet.ctrl = (burst_num << 4) | (packet_in_burst & 0xF)
            
            # Data fields with patterns
            packet.data0 = (burst_num << 16) | packet_in_burst
            packet.data1 = (~packet.data0) & ((1 << self.field_config.get_field('data1').bits) - 1)
            
            packet.sequence_id = len(self.generated_sequences)
            packet.packet_id = len(burst_packets)
            packet.profile = 'burst'
            packet.burst_number = burst_num
            packet.burst_position = packet_in_burst
            
            burst_packets.append(packet)
        
        # Move to next burst address space
        current_addr += burst_size * 16  # Leave space between bursts
    
    sequence_info = {
        'name': f'{self.name}_burst_{len(self.generated_sequences)}',
        'type': 'burst',
        'profile': 'burst',
        'length': len(burst_packets),
        'burst_size': burst_size,
        'num_bursts': num_bursts,
        'packets': burst_packets
    }
    
    self.generated_sequences.append(sequence_info)
    self._update_statistics('burst', 'burst', len(burst_packets))
    
    self.log.info(f"Generated burst pattern: {num_bursts} bursts of {burst_size} packets")
    return burst_packets

def add_incremental_pattern(self, length, start_values=None):
    """
    Add incremental pattern with configurable starting values
    
    Parameters:
    - length: Number of packets to generate
    - start_values: Dictionary of starting values for each field
    
    Returns: Incremental packet sequence
    """
    
    # Default starting values
    if start_values is None:
        start_values = {
            'addr': 0x1000,
            'ctrl': 0,
            'data0': 0x10000000,
            'data1': 0x20000000
        }
    
    incremental_packets = []
    
    for i in range(length):
        packet = self.packet_class(self.field_config)
        
        # Calculate incremental values with wraparound
        for field_name, start_val in start_values.items():
            field_def = self.field_config.get_field(field_name)
            if field_def:
                max_val = (1 << field_def.bits) - 1
                
                if field_name == 'addr':
                    # Address increments by 4 (word aligned)
                    value = (start_val + (i * 4)) & max_val
                elif field_name == 'ctrl':
                    # Control cycles through small values
                    value = (start_val + i) % min(8, max_val + 1)
                else:
                    # Data increments linearly with wraparound
                    value = (start_val + i) & max_val
                
                setattr(packet, field_name, value)
        
        packet.sequence_id = len(self.generated_sequences)
        packet.packet_id = i
        packet.profile = 'incremental'
        packet.start_values = start_values.copy()
        
        incremental_packets.append(packet)
    
    sequence_info = {
        'name': f'{self.name}_incremental_{len(self.generated_sequences)}',
        'type': 'incremental',
        'profile': 'incremental',
        'length': length,
        'start_values': start_values,
        'packets': incremental_packets
    }
    
    self.generated_sequences.append(sequence_info)
    self._update_statistics('incremental', 'incremental', length)
    
    self.log.info(f"Generated incremental pattern: {length} packets")
    return incremental_packets
```

## Advanced Pattern Generation

### Dependency-Based Patterns

```python
def add_dependency_pattern(self, length, dependencies):
    """
    Add pattern with field dependencies
    
    Parameters:
    - length: Number of packets to generate
    - dependencies: Dictionary defining field dependencies
    
    Example dependencies:
    {
        'data1': lambda addr, ctrl, data0: (addr + data0) & 0xFFFF,
        'ctrl': lambda addr: 2 if addr > 0x8000 else 1
    }
    
    Returns: Dependency-based packet sequence
    """
    
    dependency_packets = []
    base_randomizer = self.randomization_profiles['uniform']['randomizer']
    
    for i in range(length):
        packet = self.packet_class(self.field_config)
        
        # Generate independent fields first
        independent_fields = ['addr', 'ctrl', 'data0', 'data1']
        for dep_field in dependencies.keys():
            if dep_field in independent_fields:
                independent_fields.remove(dep_field)
        
        # Generate values for independent fields
        for field_name in independent_fields:
            constraint_name = f'{field_name}_constraint'
            value = base_randomizer.generate(constraint_name)
            setattr(packet, field_name, value)
        
        # Apply dependencies
        for dependent_field, dependency_func in dependencies.items():
            # Get current field values for dependency calculation
            field_values = {}
            for field_name in ['addr', 'ctrl', 'data0', 'data1']:
                if hasattr(packet, field_name):
                    field_values[field_name] = getattr(packet, field_name)
            
            try:
                # Calculate dependent value
                import inspect
                sig = inspect.signature(dependency_func)
                params = list(sig.parameters.keys())
                
                # Extract required parameters
                args = []
                for param in params:
                    if param in field_values:
                        args.append(field_values[param])
                
                # Calculate and clamp dependent value
                dependent_value = dependency_func(*args)
                field_def = self.field_config.get_field(dependent_field)
                if field_def:
                    max_val = (1 << field_def.bits) - 1
                    dependent_value = dependent_value & max_val
                
                setattr(packet, dependent_field, dependent_value)
                
            except Exception as e:
                self.log.error(f"Dependency calculation failed for {dependent_field}: {e}")
                # Fallback to random value
                constraint_name = f'{dependent_field}_constraint'
                value = base_randomizer.generate(constraint_name)
                setattr(packet, dependent_field, value)
        
        packet.sequence_id = len(self.generated_sequences)
        packet.packet_id = i
        packet.profile = 'dependency'
        packet.dependencies = dependencies
        
        dependency_packets.append(packet)
    
    sequence_info = {
        'name': f'{self.name}_dependency_{len(self.generated_sequences)}',
        'type': 'dependency',
        'profile': 'dependency',
        'length': length,
        'dependencies': dependencies,
        'packets': dependency_packets
    }
    
    self.generated_sequences.append(sequence_info)
    self._update_statistics('dependency', 'dependency', length)
    
    self.log.info(f"Generated dependency pattern: {length} packets")
    return dependency_packets

def add_constrained_pattern(self, length, constraints):
    """
    Add pattern with custom constraints
    
    Parameters:
    - length: Number of packets to generate
    - constraints: Dictionary of field constraints
    
    Example constraints:
    {
        'addr': lambda x: x % 4 == 0,  # Must be 4-byte aligned
        'ctrl': lambda x: x < 8,       # Must be less than 8
        'data0': lambda x: x != 0      # Must be non-zero
    }
    
    Returns: Constrained packet sequence
    """
    
    constrained_packets = []
    base_randomizer = self.randomization_profiles['uniform']['randomizer']
    
    for i in range(length):
        packet = self.packet_class(self.field_config)
        
        # Generate values that satisfy constraints
        for field_name in ['addr', 'ctrl', 'data0', 'data1']:
            field_def = self.field_config.get_field(field_name)
            if field_def:
                max_val = (1 << field_def.bits) - 1
                constraint_func = constraints.get(field_name)
                
                if constraint_func:
                    # Try to find value that satisfies constraint
                    attempts = 0
                    max_attempts = 100
                    
                    while attempts < max_attempts:
                        constraint_name = f'{field_name}_constraint'
                        candidate_value = base_randomizer.generate(constraint_name)
                        
                        if constraint_func(candidate_value):
                            setattr(packet, field_name, candidate_value)
                            break
                        
                        attempts += 1
                    
                    if attempts >= max_attempts:
                        # Fallback: use a known good value
                        if field_name == 'addr' and constraint_func == (lambda x: x % 4 == 0):
                            value = (i * 4) & max_val
                        else:
                            value = 0
                        
                        setattr(packet, field_name, value)
                        self.log.warning(f"Constraint satisfaction failed for {field_name}, using fallback value {value}")
                else:
                    # No constraint, use random value
                    constraint_name = f'{field_name}_constraint'
                    value = base_randomizer.generate(constraint_name)
                    setattr(packet, field_name, value)
        
        packet.sequence_id = len(self.generated_sequences)
        packet.packet_id = i
        packet.profile = 'constrained'
        packet.constraints = constraints
        
        constrained_packets.append(packet)
    
    sequence_info = {
        'name': f'{self.name}_constrained_{len(self.generated_sequences)}',
        'type': 'constrained',
        'profile': 'constrained',
        'length': length,
        'constraints': constraints,
        'packets': constrained_packets
    }
    
    self.generated_sequences.append(sequence_info)
    self._update_statistics('constrained', 'constrained', length)
    
    self.log.info(f"Generated constrained pattern: {length} packets")
    return constrained_packets
```

## Sequence Management and Analysis

### Sequence Statistics

```python
def _update_statistics(self, sequence_type, profile, length):
    """Update sequence generation statistics"""
    
    if sequence_type not in self.sequence_statistics:
        self.sequence_statistics[sequence_type] = {}
    
    if profile not in self.sequence_statistics[sequence_type]:
        self.sequence_statistics[sequence_type][profile] = {
            'count': 0,
            'total_packets': 0,
            'avg_length': 0
        }
    
    stats = self.sequence_statistics[sequence_type][profile]
    stats['count'] += 1
    stats['total_packets'] += length
    stats['avg_length'] = stats['total_packets'] / stats['count']

def get_sequence_statistics(self):
    """Get comprehensive sequence generation statistics"""
    
    total_sequences = len(self.generated_sequences)
    total_packets = sum(seq['length'] for seq in self.generated_sequences)
    
    stats = {
        'total_sequences': total_sequences,
        'total_packets': total_packets,
        'avg_sequence_length': total_packets / max(1, total_sequences),
        'sequence_types': self.sequence_statistics.copy(),
        'profiles_used': set(),
        'sequence_breakdown': {}
    }
    
    # Analyze sequence breakdown
    for sequence in self.generated_sequences:
        seq_type = sequence['type']
        profile = sequence['profile']
        
        stats['profiles_used'].add(profile)
        
        if seq_type not in stats['sequence_breakdown']:
            stats['sequence_breakdown'][seq_type] = 0
        stats['sequence_breakdown'][seq_type] += 1
    
    stats['profiles_used'] = list(stats['profiles_used'])
    
    return stats

def generate_sequence_report(self):
    """Generate comprehensive sequence generation report"""
    
    stats = self.get_sequence_statistics()
    
    report = []
    report.append("=" * 80)
    report.append("GAXI Buffer Sequence Generation Report")
    report.append("=" * 80)
    
    # Summary
    report.append(f"Sequence Name: {self.name}")
    report.append(f"Total Sequences Generated: {stats['total_sequences']}")
    report.append(f"Total Packets Generated: {stats['total_packets']}")
    report.append(f"Average Sequence Length: {stats['avg_sequence_length']:.1f}")
    report.append("")
    
    # Sequence type breakdown
    report.append("Sequence Type Breakdown:")
    report.append("-" * 40)
    for seq_type, count in stats['sequence_breakdown'].items():
        percentage = (count / stats['total_sequences']) * 100
        report.append(f"{seq_type:>15}: {count:>3} sequences ({percentage:5.1f}%)")
    report.append("")
    
    # Profile usage
    report.append("Randomization Profiles Used:")
    report.append("-" * 40)
    for profile in sorted(stats['profiles_used']):
        profile_info = self.randomization_profiles.get(profile, {})
        description = profile_info.get('description', 'Custom profile')
        report.append(f"{profile:>15}: {description}")
    report.append("")
    
    # Detailed statistics by type and profile
    report.append("Detailed Statistics:")
    report.append("-" * 40)
    for seq_type, type_stats in stats['sequence_types'].items():
        report.append(f"{seq_type}:")
        for profile, profile_stats in type_stats.items():
            report.append(f"  {profile}:")
            report.append(f"    Count: {profile_stats['count']}")
            report.append(f"    Total Packets: {profile_stats['total_packets']}")
            report.append(f"    Avg Length: {profile_stats['avg_length']:.1f}")
    
    return "\n".join(report)
```

### Sequence Validation

```python
def validate_sequence(self, packets):
    """
    Validate generated packet sequence for consistency
    
    Parameters:
    - packets: List of packets to validate
    
    Returns: (is_valid: bool, errors: list)
    """
    
    errors = []
    
    if not packets:
        errors.append("Empty packet sequence")
        return False, errors
    
    # Validate each packet
    for i, packet in enumerate(packets):
        packet_errors = self._validate_packet(packet, i)
        errors.extend(packet_errors)
    
    # Validate sequence-level properties
    sequence_errors = self._validate_sequence_properties(packets)
    errors.extend(sequence_errors)
    
    is_valid = len(errors) == 0
    
    if is_valid:
        self.log.debug(f"Sequence validation PASSED: {len(packets)} packets")
    else:
        self.log.error(f"Sequence validation FAILED: {len(errors)} errors in {len(packets)} packets")
    
    return is_valid, errors

def _validate_packet(self, packet, packet_index):
    """Validate individual packet"""
    
    errors = []
    
    # Check required fields
    required_fields = ['addr', 'ctrl', 'data0', 'data1']
    for field_name in required_fields:
        if not hasattr(packet, field_name):
            errors.append(f"Packet {packet_index}: Missing field '{field_name}'")
            continue
        
        # Check field value range
        field_def = self.field_config.get_field(field_name)
        if field_def:
            value = getattr(packet, field_name)
            max_val = (1 << field_def.bits) - 1
            
            if value < 0 or value > max_val:
                errors.append(f"Packet {packet_index}: Field '{field_name}' value {value} out of range [0, {max_val}]")
    
    return errors

def _validate_sequence_properties(self, packets):
    """Validate sequence-level properties"""
    
    errors = []
    
    # Check for duplicate sequence IDs
    sequence_ids = [getattr(p, 'sequence_id', None) for p in packets]
    if len(set(sequence_ids)) != len(sequence_ids):
        errors.append("Duplicate sequence IDs detected")
    
    # Check packet ID ordering
    packet_ids = [getattr(p, 'packet_id', -1) for p in packets]
    expected_ids = list(range(len(packets)))
    if packet_ids != expected_ids:
        errors.append("Packet IDs not in expected sequence")
    
    # Check profile consistency (if specified)
    profiles = [getattr(p, 'profile', None) for p in packets]
    if None not in profiles and len(set(profiles)) > 1:
        # Multiple profiles in sequence - log as info, not error
        self.log.info(f"Sequence contains multiple profiles: {set(profiles)}")
    
    return errors
```

## Usage Examples

### Basic Sequence Generation

```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_seq import GAXIBufferSequence
from CocoTBFramework.components.shared.field_config import FieldConfig

# Create field configuration
field_config = FieldConfig()
# ... add field definitions

# Create sequence generator
seq_gen = GAXIBufferSequence("test_sequence", field_config)

# Generate various patterns
random_packets = seq_gen.add_random_pattern(length=50, profile='uniform')
corner_packets = seq_gen.add_corner_case_pattern()
burst_packets = seq_gen.add_burst_pattern(burst_size=8, num_bursts=4)

# Get statistics
stats = seq_gen.get_sequence_statistics()
print(f"Generated {stats['total_packets']} packets in {stats['total_sequences']} sequences")
```

### Advanced Pattern Generation

```python
# Custom dependency pattern
dependencies = {
    'data1': lambda addr, data0: (addr + data0) & 0xFFFFFFFF,
    'ctrl': lambda addr: 2 if addr > 0x8000 else 1
}
dep_packets = seq_gen.add_dependency_pattern(length=30, dependencies=dependencies)

# Custom constraints
constraints = {
    'addr': lambda x: x % 4 == 0,  # 4-byte aligned
    'ctrl': lambda x: x < 8,       # Valid command range
    'data0': lambda x: x != 0      # Non-zero data
}
constrained_packets = seq_gen.add_constrained_pattern(length=40, constraints=constraints)

# Custom weighted pattern
weights = {
    'addr': ([(0, 0x1000), (0x1000, 0x8000)], [0.8, 0.2]),
    'ctrl': ([0, 1, 2, 3], [0.4, 0.3, 0.2, 0.1])
}
weighted_packets = seq_gen.add_weighted_random_pattern(length=25, field_weights=weights)
```

### Sequence Validation and Reporting

```python
# Validate generated sequences
for sequence_info in seq_gen.generated_sequences:
    packets = sequence_info['packets']
    is_valid, errors = seq_gen.validate_sequence(packets)
    
    if not is_valid:
        print(f"Validation failed for {sequence_info['name']}: {errors}")

# Generate comprehensive report
report = seq_gen.generate_sequence_report()
print(report)

# Get specific statistics
stats = seq_gen.get_sequence_statistics()
print(f"Profiles used: {stats['profiles_used']}")
print(f"Sequence breakdown: {stats['sequence_breakdown']}")
```

The `gaxi_buffer_seq.py` module provides comprehensive sequence generation capabilities with modern FlexConfigGen integration, supporting sophisticated pattern generation, dependency tracking, and comprehensive validation for thorough GAXI buffer testing.