# reset_sync

## Overview

The `reset_sync` module is a parameterized reset synchronizer written in SystemVerilog. This module is designed to mitigate metastability issues that may arise when a reset signal crosses clock domain boundaries. It achieves this by ensuring the reset signal is synchronized to the clock domain of the logic it is controlling.

## Parameters

- **N**: This is a parameter that defines the depth of the synchronization register chain. The default value is 3, meaning a chain of three flip-flops will be used to synchronize the reset signal.

## Ports

- **i_clk**: The input clock signal. This clock drives the synchronization process.
- **i_rst_n**: The active-low asynchronous reset input. When this signal is low, the reset synchronizer will activate.
- **o_sync_rst_n**: The synchronized reset output, which is also active-low. This signal can be used reliably within the `i_clk` domain.

## Signals

- **r_sync_reg**: This internal signal is an array of flip-flops used to synchronize the reset signal. The width of the array is determined by the parameter `N`.

## Functionality

The reset synchronizer works by passing the asynchronous reset signal (`i_rst_n`) through a chain of flip-flops. This chain ensures that the reset signal is properly synchronized with the `i_clk` clock domain, thereby reducing the risk of metastability.

### Operation

1. **Asynchronous Reset Assertion**: When `i_rst_n` is driven low, the chain of flip-flops (`r_sync_reg`) is asynchronously cleared to `0`.
2. **Reset Release & Synchronization**: When `i_rst_n` is released (driven high), the module begins synchronizing the reset signal. The chain of flip-flops captures the released reset signal and propagates it through the chain with each clock cycle until the reset signal can be considered stable and safely synchronized.
3. **Output Generation**: The synchronized reset (`o_sync_rst_n`) is taken from the last stage of the flip-flop chain. This ensures that `o_sync_rst_n` reflects the properly synchronized reset state.

## Usage

The reset synchronizer can be instantiated in a design to ensure that reset signals properly align with the clock domain of the logic they are intended to reset. By parameterizing the depth of the synchronization chain (`N`), the designer can balance between synchronization depth and latency based on the specific requirements of the design.

## Key Points

- **Metastability Mitigation**: The primary function of the reset synchronizer is to mitigate metastability issues when a reset signal crosses clock domains.
- **Parameterization**: The depth of the synchronization chain is parameterizable, allowing for flexibility in design.
- **Active-Low Reset**: Both the input and output reset signals are active-low, which is a common design practice for reset signals in digital designs.

This reset synchronizer module is a fundamental building block in ensuring reliable operation across different clock domains, making it indispensable in digital design practices.

---

[Return to Index](index.md)

---
