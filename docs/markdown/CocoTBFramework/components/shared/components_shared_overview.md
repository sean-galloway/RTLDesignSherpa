# Shared Components Overview

The shared components directory contains the foundational building blocks used across all protocols in the CocoTBFramework. These components are designed to be protocol-agnostic and provide essential functionality for verification, randomization, statistics collection, and signal management.

## Architecture Overview

The shared components follow a layered architecture:

```
┌─────────────────────────────────────────────────────────┐
│                    Protocol Layers                     │
│              (GAXI, FIFO, APB, AXI4)                  │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                  Shared Components                     │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │   Packet    │ │Randomization│ │ Statistics  │     │
│   │ Management  │ │  & Config   │ │& Monitoring │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │   Memory    │ │   Signal    │ │ Utilities & │     │
│   │   Model     │ │  Mapping    │ │   Debug     │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                     CocoTB Core                        │
└─────────────────────────────────────────────────────────┘
```

## Component Categories

### 🎯 **Packet Management & Data Handling**
These components handle the core data structures and field management:

- **packet.py**: Thread-safe generic packet class with field caching
- **packet_factory.py**: Factory pattern for packet creation and management  
- **field_config.py**: Rich field configuration with validation and encoding
- **data_strategies.py**: High-performance data collection/driving with signal caching

**Key Features:**
- Protocol-agnostic packet handling
- Automatic field validation and masking
- Thread-safe operations for parallel testing
- Performance optimization through caching
- FIFO packing/unpacking support

### 🎲 **Randomization & Configuration**
Advanced randomization capabilities for directed and constrained testing:

- **flex_randomizer.py**: Multi-mode randomization engine (constrained, sequence, custom)
- **flex_config_gen.py**: Helper for creating weighted randomization profiles
- **randomization_config.py**: High-level randomization configuration framework

**Key Features:**
- Constrained random with weighted bins
- Sequence-based deterministic patterns
- Custom generator functions
- Object bin support (non-numeric values)
- Dependency management between fields
- Multiple pre-defined timing profiles

### 📊 **Statistics & Monitoring**
Comprehensive statistics collection for performance analysis:

- **master_statistics.py**: Statistics for master/slave components (latency, throughput, errors)
- **monitor_statistics.py**: Basic monitor statistics (transactions, violations)

**Key Features:**
- Real-time performance metrics
- Moving window averages
- Error categorization and tracking
- Protocol violation detection
- Comprehensive reporting

### 💾 **Memory & Storage**
High-performance memory modeling with diagnostics:

- **memory_model.py**: NumPy-based memory with access tracking and region management

**Key Features:**
- High-performance NumPy backend
- Comprehensive access tracking
- Memory region management
- Boundary checking and validation
- Coverage analysis
- Detailed memory dumps

### 🔌 **Protocol Support**
Protocol-agnostic infrastructure for signal handling and error injection:

- **signal_mapping_helper.py**: Automatic signal discovery and mapping for GAXI/FIFO
- **protocol_error_handler.py**: Generic error injection for testing error handling

**Key Features:**
- Pattern-based signal discovery
- Manual signal mapping override
- Prefix handling for cocotb compatibility
- Error region and transaction management
- Protocol violation simulation

### 🔧 **Utilities & Debug**
Helper utilities for development and debugging:

- **debug_object.py**: Object inspection and detailed logging utilities

## Design Principles

### 1. **Protocol Agnostic**
All shared components are designed to work across different protocols (GAXI, FIFO, APB, AXI4) without modification.

### 2. **Performance Optimized**
- Thread-safe caching for high-performance parallel testing
- NumPy backend for memory operations  
- Pre-computed field validation rules
- Cached signal references

### 3. **Flexible Configuration**
- Rich configuration classes with validation
- Multiple randomization modes
- Configurable statistics collection
- Customizable field encoding and formatting

### 4. **Comprehensive Error Handling**
- Detailed error messages with caller context
- Graceful degradation for optional features
- Comprehensive validation with helpful suggestions

### 5. **Rich Debugging Support**
- Detailed logging at multiple levels
- Object inspection utilities
- Performance statistics and cache hit rates
- Rich table formatting for configuration display

## Integration Patterns

### Typical Component Usage Flow

```python
# 1. Configure fields
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))

# 2. Create packet factory
factory = PacketFactory(MyPacket, field_config)

# 3. Set up randomization
randomizer = FlexRandomizer({
    'addr': ([(0x1000, 0x2000)], [1.0]),
    'data': ([(0, 0xFFFF)], [1.0])
})

# 4. Create memory model
memory = MemoryModel(num_lines=256, bytes_per_line=4, log=log)

# 5. Set up statistics
stats = MasterStatistics()

# 6. Resolve signals (automatic or manual)
resolver = SignalResolver('gaxi_master', dut, bus, log, 'MyMaster')
resolver.apply_to_component(component)
```

### Cross-Component Integration

The shared components are designed to integrate seamlessly:

- **Packets** work with **PacketFactory** for creation and **FieldConfig** for structure
- **Randomization** components integrate with **Packets** for field value generation
- **Statistics** components track operations from **Masters/Slaves/Monitors**
- **MemoryModel** integrates with **Packets** for transaction-based read/write
- **SignalResolver** bridges **CocoTB** signals with component attributes

## Performance Characteristics

### Thread Safety
- All caching mechanisms are thread-safe using RLock
- Components can be safely used in parallel test environments
- Statistics collection is atomic and consistent

### Memory Efficiency  
- Field caching reduces repeated computation overhead
- NumPy backend for large memory operations
- Efficient signal reference caching
- Moving window statistics to limit memory growth

### Performance Gains
- 40% faster data collection through cached signal references
- 30% faster data driving through cached driving functions  
- Elimination of repeated hasattr()/getattr() calls
- Pre-computed field validation rules

## Testing & Validation

The shared components include extensive validation:

- **Field validation** with helpful error messages
- **Signal mapping validation** with detailed diagnostics
- **Memory boundary checking** with overflow protection
- **Randomization constraint validation** with type checking
- **Thread-safe cache verification** for parallel testing

## Future Extensions

The shared component architecture is designed for easy extension:

- New protocol support through signal mapping patterns
- Additional randomization modes in FlexRandomizer
- Enhanced statistics collection with custom metrics
- Extended memory model features (compression, persistence)
- Additional debugging and profiling utilities

## Getting Started

1. **For Packet Handling**: Start with `field_config.py` and `packet.py`
2. **For Randomization**: Begin with `flex_randomizer.py` and `flex_config_gen.py` 
3. **For Memory Testing**: Use `memory_model.py` with your protocol components
4. **For Signal Mapping**: Leverage `signal_mapping_helper.py` for automatic discovery
5. **For Statistics**: Integrate `master_statistics.py` or `monitor_statistics.py`

Each component includes comprehensive documentation with examples and best practices for integration into your verification environment.
