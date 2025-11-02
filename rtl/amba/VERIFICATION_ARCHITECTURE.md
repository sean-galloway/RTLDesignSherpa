# AMBA Verification Architecture - MANDATORY Requirements

**Last Updated:** 2025-10-02
**Status:** 🔴 CRITICAL - HARD REQUIREMENT

---

## ⚠️ CRITICAL RULE: Testbench Reusability

**NEVER embed testbench classes inside test runner files!**

This code will be instantiated in **DOZENS** of places. Embedding TB logic in test files makes it **COMPLETELY WORTHLESS** for reuse.

---

## Required File Structure

```
bin/CocoTBFramework/tbclasses/
├── axi4/
│   ├── axi4_master_read_tb.py      ← REUSABLE TB CLASS
│   ├── axi4_master_write_tb.py     ← REUSABLE TB CLASS
│   ├── axi4_slave_read_tb.py       ← REUSABLE TB CLASS
│   ├── axi4_slave_write_tb.py      ← REUSABLE TB CLASS
│   └── monitor/
│       └── axi_monitor_config_tb.py ← REUSABLE TB CLASS
├── apb/
│   └── apb_tb.py                    ← REUSABLE TB CLASS
├── apb_monitor/
│   ├── apb_monitor_core_tb.py      ← REUSABLE TB CLASS
│   ├── apb_monitor_scoreboard.py   ← REUSABLE SCOREBOARD
│   └── apb_monitor_packets.py      ← REUSABLE PACKET TYPES
├── axis4/
│   ├── axis_master_tb.py            ← REUSABLE TB CLASS
│   └── axis_slave_tb.py             ← REUSABLE TB CLASS
└── [new_protocol]/
    └── [module]_tb.py               ← YOUR NEW TB CLASS GOES HERE

val/amba/
├── test_axi4_master_rd.py          ← TEST RUNNER ONLY
├── test_axi4_master_wr.py          ← TEST RUNNER ONLY
├── test_apb_monitor.py             ← TEST RUNNER ONLY
└── test_[your_module].py           ← YOUR TEST RUNNER GOES HERE
```

---

## Responsibilities Separation

### Test Runner (val/amba/test_*.py) - ONLY DOES:

1. ✅ Import testbench class from `bin/CocoTBFramework/tbclasses/`
2. ✅ Define pytest parameter matrix
3. ✅ Configure RTL sources list
4. ✅ Set RTL parameters
5. ✅ Call `cocotb_test.simulator.run()`

**THAT'S IT. NOTHING ELSE.**

### Testbench Class (bin/CocoTBFramework/tbclasses/) - DOES:

1. ✅ DUT signal initialization
2. ✅ Clock and reset management
3. ✅ Transaction generation
4. ✅ Packet monitoring
5. ✅ Scoreboarding and verification
6. ✅ Reusable test sequences
7. ✅ Configuration management

---

## Example - CORRECT Implementation

### Testbench Class (REUSABLE)

```python
# bin/CocoTBFramework/tbclasses/axi4/axi4_master_read_tb.py

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from cocotb.triggers import RisingEdge
import os

class AXI4MasterReadTB(TBBase):
    """Reusable testbench for AXI4 master read validation

    Can be imported by:
    - Unit tests (val/amba/)
    - Integration tests (val/system/)
    - System tests (val/soc/)
    - External user projects
    """

    def __init__(self, dut, **kwargs):
        super().__init__(dut)

        # Read parameters from environment
        self.AW = int(os.environ.get('TEST_AW', '32'))
        self.DW = int(os.environ.get('TEST_DW', '64'))
        self.IW = int(os.environ.get('TEST_IW', '8'))

        # Test state
        self.packets = []
        self.transactions = []

    async def setup_clocks_and_reset(self):
        """Setup clock and reset sequence"""
        await self.start_clock('aclk', 10, 'ns')
        self.dut.aresetn.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        await self.initialize_inputs()

    async def initialize_inputs(self):
        """Initialize all DUT inputs to safe values"""
        self.dut.s_axi_arvalid.value = 0
        self.dut.s_axi_rready.value = 1
        # ... more initializations

    async def run_basic_test(self):
        """Basic transaction test - reusable sequence"""
        for i in range(5):
            await self.send_transaction(addr=0x1000 + i*0x10)

        for _ in range(20):
            await RisingEdge(self.dut.aclk)

        assert len(self.packets) >= 5, "Expected at least 5 packets"

    async def send_transaction(self, addr, txn_id=None, length=0):
        """Send AXI read transaction"""
        # Transaction generation logic
        pass
```

### Test Runner (IMPORTS TB)

```python
# val/amba/test_axi4_master_rd.py

import pytest
import cocotb
from cocotb_test.simulator import run

# IMPORT THE REUSABLE TB CLASS
from CocoTBFramework.tbclasses.axi4.axi4_master_read_tb import AXI4MasterReadTB

@cocotb.test()
async def axi4_master_read_test(dut):
    """Test function - uses imported TB"""
    tb = AXI4MasterReadTB(dut)  # ← Create instance of TB class
    await tb.setup_clocks_and_reset()
    await tb.run_basic_test()

@pytest.mark.parametrize("aw, dw, iw", [
    (32, 64, 8),
    (32, 128, 4),
    (64, 64, 16),
])
def test_axi4_master_read(request, aw, dw, iw):
    """Pytest runner - only configures and runs"""

    # RTL sources
    verilog_sources = [
        "rtl/amba/axi4/axi4_master_rd.sv",
        # ... more sources
    ]

    # RTL parameters
    rtl_parameters = {
        'ADDR_WIDTH': str(aw),
        'DATA_WIDTH': str(dw),
        'ID_WIDTH': str(iw),
    }

    # Environment for TB
    extra_env = {
        'TEST_AW': str(aw),
        'TEST_DW': str(dw),
        'TEST_IW': str(iw),
    }

    # Run simulation
    run(
        verilog_sources=verilog_sources,
        toplevel="axi4_master_rd",
        module="test_axi4_master_rd",  # This file
        parameters=rtl_parameters,
        extra_env=extra_env,
    )
```

---

## Example - WRONG Implementation ❌

### DON'T DO THIS:

```python
# val/amba/test_axi4_monitor.py - WRONG!

import pytest
import cocotb

# ❌ WRONG: TB class defined in test file
class AXI4MonitorTB(TBBase):
    """This TB is TRAPPED in this file and CANNOT be reused!"""

    def __init__(self, dut):
        super().__init__(dut)
        # 500 lines of TB logic...

    async def run_test(self):
        # More TB logic...

@cocotb.test()
async def axi4_monitor_test(dut):
    tb = AXI4MonitorTB(dut)  # ← Can't import this from anywhere else!
    await tb.run_test()

# This test is WORTHLESS for reuse because:
# - Integration tests can't import AXI4MonitorTB
# - System tests can't import AXI4MonitorTB
# - User projects can't import AXI4MonitorTB
# - You'll have to COPY-PASTE this 500-line TB to every test file!
```

---

## Why This Architecture Matters

### Reuse Scenarios:

1. **Unit Testing** (`val/amba/test_*.py`)
   ```python
   from CocoTBFramework.tbclasses.axi4.axi4_master_read_tb import AXI4MasterReadTB
   tb = AXI4MasterReadTB(dut)
   ```

2. **Integration Testing** (`val/system/test_interconnect.py`)
   ```python
   from CocoTBFramework.tbclasses.axi4.axi4_master_read_tb import AXI4MasterReadTB
   master_tb = AXI4MasterReadTB(dut.master0)
   ```

3. **System Testing** (`val/soc/test_full_soc.py`)
   ```python
   from CocoTBFramework.tbclasses.axi4.axi4_master_read_tb import AXI4MasterReadTB
   cpu_master = AXI4MasterReadTB(dut.soc.cpu.m_axi)
   ```

4. **Composition** (Extending TBs)
   ```python
   from CocoTBFramework.tbclasses.axi4.axi4_master_read_tb import AXI4MasterReadTB

   class AXI4MasterReadCGTB(AXI4MasterReadTB):
       """Adds clock gating support to base TB"""
       def __init__(self, dut):
           super().__init__(dut)
           self.cg_ctrl = ClockGateController(dut)
   ```

5. **External Projects**
   ```python
   # User's project imports your TB
   from rtldesignsherpa.CocoTBFramework.tbclasses.axi4 import AXI4MasterReadTB
   ```

**If TB is in test file, NONE of these work!**

---

## Verification Checklist

Before ANY test submission:

- [ ] Testbench class exists in `bin/CocoTBFramework/tbclasses/[protocol]/`
- [ ] Test file imports TB (not defines it inline)
- [ ] TB class inherits from `TBBase`
- [ ] TB has no test-specific hardcoded parameters
- [ ] TB reads config from environment variables or kwargs
- [ ] Test runner only has pytest params and `run()` call
- [ ] TB can be imported: `from CocoTBFramework.tbclasses... import ...`

---

## Reference Examples (CORRECT)

**Working examples to copy:**

- `bin/CocoTBFramework/tbclasses/axi4/axi4_master_read_tb.py`
- `bin/CocoTBFramework/tbclasses/axi4/axi4_master_write_tb.py`
- `bin/CocoTBFramework/tbclasses/apb_monitor/apb_monitor_core_tb.py`
- `bin/CocoTBFramework/tbclasses/axi4/monitor/axi_monitor_config_tb.py`

**Working test runners:**

- `val/amba/test_axi4_master_rd.py`
- `val/amba/test_axi4_master_rd_cg.py`
- `val/amba/test_apb_monitor.py`

---

## Migration Guide

**If you have embedded TB in test file:**

1. Create new file: `bin/CocoTBFramework/tbclasses/[protocol]/[module]_tb.py`
2. Move TB class to new file
3. Add `__init__.py` if needed
4. Update test file to import TB: `from CocoTBFramework.tbclasses... import ...`
5. Remove old TB class definition from test file
6. Test import works: `python -c "from CocoTBFramework.tbclasses... import ..."`
7. Run tests to verify

---

## Non-Compliance Consequences

If testbench is embedded in test file:

- ❌ Cannot reuse in integration tests
- ❌ Cannot reuse in system tests
- ❌ Cannot compose/extend TB classes
- ❌ Must copy-paste 100s of lines between tests
- ❌ Bugs must be fixed in multiple places
- ❌ External users cannot import TB
- ❌ Code review will be rejected

**This is not a suggestion. This is MANDATORY.**

---

## Questions?

See:
- `CLAUDE.md` Rule #0 - AI assistance guidance
- `PRD.md` Section 6.1 - Verification architecture requirements
- Working examples in `bin/CocoTBFramework/tbclasses/`

**No exceptions to this rule.**

---

**Last Updated:** 2025-10-02
**Enforcement:** MANDATORY for all AMBA tests
