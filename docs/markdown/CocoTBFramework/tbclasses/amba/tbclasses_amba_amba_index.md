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

# CocoTBFramework/tbclasses/amba Directory Index

This directory contains AMBA (Advanced Microcontroller Bus Architecture) testbench classes that provide specialized functionality for AMBA protocol verification within the CocoTBFramework. These components handle clock gating control and randomization configurations for AMBA-based protocols.

## Directory Structure

```
CocoTBFramework/tbclasses/amba/
├── __init__.py
├── amba_cg_ctrl.py
├── amba_random_configs.py
└── cdc_handshake.py
```

## Overview
- [**Overview**](overview.md) - Complete overview of the AMBA testbench utilities

## Component Documentation

### Clock Gating Management
- [**amba_cg_ctrl.py**](amba_cg_ctrl.md) - AXI Clock Gate Controller for managing clock gating based on protocol activity

### Randomization Configuration
- [**amba_random_configs.py**](amba_random_configs.md) - Predefined randomization configurations for APB, AXI, and other AMBA protocols

### Clock Domain Crossing Verification
- [**cdc_handshake.py**](cdc_handshake.md) - CDC Handshake Testbench for cross-domain protocol verification with sophisticated randomization

## Quick Start

### Basic Clock Gate Controller Setup
```python
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl

# Create clock gate controller
clock_gate = AxiClockGateCtrl(
    dut,
    instance_path="i_amba_clock_gate_ctrl",
    clock_signal_name="clk_in",
    user_valid_signals=["s_axi_arvalid", "s_axi_awvalid"],
    axi_valid_signals=["m_axi_arvalid", "m_axi_awvalid"]
)

# Configure clock gating
clock_gate.enable_clock_gating(True)
clock_gate.set_idle_count(8)

# Monitor activity
stats = await clock_gate.monitor_activity(1000, 'ns')
print(f"Active: {stats['active_percent']}%, Gated: {stats['gated_percent']}%")
```

### Basic CDC Testbench Setup
```python
from CocoTBFramework.tbclasses.amba.cdc_handshake import CDCHandshakeTB

# Create CDC testbench with dual clock domains
@cocotb.test()
async def test_cdc_basic(dut):
    tb = CDCHandshakeTB(dut)
    await tb.initialize()
    
    # Run basic CDC verification
    success = await tb.run_simple_incremental_test(count=50)
    assert success, "CDC handshake test failed"
    
    # Get comprehensive statistics
    stats = tb.get_comprehensive_statistics()
    print(f"CDC latency: {stats.get('avg_cdc_latency_ns', 0):.2f}ns")
```

### Using Randomization Configurations
```python
from CocoTBFramework.tbclasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)

# Apply APB master configuration
randomizer.load_config(APB_MASTER_RANDOMIZER_CONFIGS['constrained'])

# Apply AXI configuration for high throughput
randomizer.load_config(AXI_RANDOMIZER_CONFIGS['high_throughput'])

# Apply slow consumer configuration
randomizer.load_config(APB_SLAVE_RANDOMIZER_CONFIGS['slow_consumer'])
```

## Integration Patterns

### Complete AMBA Testbench with CDC
```python
import cocotb
from cocotb.triggers import Timer
from CocoTBFramework.tbclasses.misc.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl
from CocoTBFramework.tbclasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from CocoTBFramework.tbclasses.amba.cdc_handshake import CDCHandshakeTB

class ComprehensiveAmbaTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut, "ComprehensiveAmbaTest")
        
        # Set up CDC testbench
        self.cdc_tb = CDCHandshakeTB(dut)
        
        # Set up clock gate controller
        self.clock_gate = AxiClockGateCtrl(
            dut,
            instance_path="dut.clock_gate",
            user_valid_signals=["user_req_valid"],
            axi_valid_signals=["axi_ar_valid", "axi_aw_valid"]
        )
        
        # Configure for testing
        self.setup_clock_gating()
    
    def setup_clock_gating(self):
        self.clock_gate.enable_clock_gating(True)
        self.clock_gate.set_idle_count(10)
    
    async def run_cdc_power_test(self):
        """Test CDC functionality with power monitoring"""
        
        # Configure randomization for CDC testing
        cdc_config = 'cdc_mixed_freq'  # Use CDC-specific randomization
        
        # Start power monitoring
        power_task = cocotb.start_soon(
            self.clock_gate.monitor_activity(10000, 'ns')
        )
        
        # Run CDC test
        cdc_task = cocotb.start_soon(
            self.cdc_tb.run_simple_incremental_test(100, cdc_config)
        )
        
        # Wait for completion
        cdc_success = await cdc_task
        power_stats = await power_task
        
        # Validate results
        assert cdc_success, "CDC test failed"
        assert power_stats['gated_percent'] > 15, "Insufficient power savings"
        
        self.log.info(f"CDC test passed with {power_stats['gated_percent']:.1f}% power savings")
        return {'cdc_success': cdc_success, 'power_stats': power_stats}

@cocotb.test()
async def test_comprehensive_amba(dut):
    tb = ComprehensiveAmbaTestbench(dut)
    await tb.initialize()
    
    results = await tb.run_cdc_power_test()
    
    tb.log.info("Comprehensive AMBA test completed successfully")
```

## Configuration Examples

### Clock Gating Scenarios
```python
# Scenario 1: High performance, minimal gating
clock_gate.set_idle_count(2)  # Gate after 2 idle cycles
clock_gate.enable_clock_gating(True)

# Scenario 2: Power optimization, aggressive gating  
clock_gate.set_idle_count(16) # Gate after 16 idle cycles
clock_gate.enable_clock_gating(True)

# Scenario 3: Debug mode, no gating
clock_gate.enable_clock_gating(False)
```

### Randomization Combinations
```python
# High throughput AXI with fast APB
axi_config = AXI_RANDOMIZER_CONFIGS['high_throughput']
apb_config = APB_MASTER_RANDOMIZER_CONFIGS['fast']

# Error injection with slow consumers
axi_config = AXI_RANDOMIZER_CONFIGS['constrained'] 
apb_config = APB_SLAVE_RANDOMIZER_CONFIGS['error_injection']

# Power testing with CDC and burst patterns
axi_config = AXI_RANDOMIZER_CONFIGS['burst_pause']
apb_config = APB_MASTER_RANDOMIZER_CONFIGS['burst_pause']
cdc_config = 'cdc_burst_stress'  # CDC-specific configuration

# CDC timing verification with slow domains
cdc_config = 'cdc_slow_domain'  # Test slow clock domain crossing
power_config = {'idle_count': 4}  # Aggressive power gating
```

## Navigation
- [**Back to tbclasses**](../index.md) - Return to main tbclasses index
- [**Back to CocoTBFramework**](../../index.md) - Return to main framework index