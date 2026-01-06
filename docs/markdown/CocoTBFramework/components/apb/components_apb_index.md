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

# APB Components Index

This directory contains the APB (Advanced Peripheral Bus) protocol components for the CocoTBFramework. These components provide comprehensive support for APB protocol verification with masters, slaves, monitors, and testing utilities.

## Overview
- [**Overview**](components_apb_overview.md) - Complete overview of the APB components directory

## Core Components

### Protocol Implementation
- [**apb_components.py**](components_apb_apb_components.md) - APB Monitor, Master, and Slave implementations
- [**apb_packet.py**](components_apb_apb_packet.md) - APB packet and transaction classes with randomization
- [**apb_sequence.py**](components_apb_apb_sequence.md) - APB test sequence generation and management

### Factory Functions & Utilities
- **apb_factories.py** - Factory functions for creating and configuring APB components *(documentation planned)*

## Navigation
- [**Back to Components**](../components_index.md) - Return to main components index
- [**Back to CocoTBFramework**](../components_index.md) - Return to main framework index