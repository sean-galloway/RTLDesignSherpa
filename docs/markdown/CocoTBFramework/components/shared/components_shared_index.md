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

# Shared Components Index

This directory contains the core shared components used across all protocols in the CocoTBFramework. These components provide essential functionality for packet handling, randomization, statistics, memory modeling, and signal mapping.

## Overview
- [**Overview**](components_shared_overview.md) - Complete overview of the shared components directory

## Core Components

### Data Handling & Packet Management
- [**data_strategies.py**](components_shared_data_strategies.md) - High-performance data collection and driving strategies with caching
- [**packet.py**](components_shared_packet.md) - Generic packet class with thread-safe performance optimizations  
- [**packet_factory.py**](components_shared_packet_factory.md) - Generic packet factory for creating and managing packets
- [**field_config.py**](components_shared_field_config.md) - Field configuration classes for defining packet structures

### Randomization & Configuration
- [**flex_randomizer.py**](components_shared_flex_randomizer.md) - Constrained randomization engine with multiple constraint types
- [**flex_config_gen.py**](components_shared_flex_config_gen.md) - Helper for creating FlexRandomizer configurations with weighted bins
- [**randomization_config.py**](components_shared_randomization_config.md) - Randomization configuration framework using FlexRandomizer

### Statistics & Monitoring  
- [**master_statistics.py**](components_shared_master_statistics.md) - Statistics tracking for master and slave components
- [**monitor_statistics.py**](components_shared_monitor_statistics.md) - Statistics class for monitor components

### Memory & Storage
- [**memory_model.py**](components_shared_memory_model.md) - High-performance memory model with diagnostics and access tracking

### Protocol Support
- [**signal_mapping_helper.py**](components_shared_signal_mapping_helper.md) - Signal mapping helper for GAXI/FIFO protocols  
- [**protocol_error_handler.py**](components_shared_protocol_error_handler.md) - Generic error handler for protocol transactions

### Utilities
- [**debug_object.py**](components_shared_debug_object.md) - Simple debugging utilities for object inspection

## Navigation
- [**Back to CocoTBFramework**](../components_index.md) - Return to main framework index
