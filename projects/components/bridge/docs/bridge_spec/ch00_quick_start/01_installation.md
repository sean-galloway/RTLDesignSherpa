### Quick Start - Installation

#### Prerequisites

Before using the Bridge generator, ensure you have the following tools installed:

**Required Tools:**
- **Python 3.8+** - Generator runtime
- **Verilator 4.0+** - RTL simulation and linting
- **CocoTB** - Python-based verification framework
- **GNU Make** - Build automation

**Optional Tools:**
- **Vivado/Quartus** - FPGA synthesis (if targeting FPGAs)
- **WaveDrom CLI** - Waveform diagram generation
- **GraphViz** - Block diagram generation

---

#### Python Environment Setup

**1. Create Virtual Environment (Recommended)**
```bash
cd ~/github/rtldesignsherpa
python3 -m venv venv
source venv/bin/activate
```

**2. Install Python Dependencies**
```bash
pip install -r requirements.txt
```

**Key Python Packages:**
- `cocotb` - Verification framework
- `pytest` - Test runner
- `Jinja2` - Template engine (used by generator)
- `toml` - TOML configuration parser

---

#### Verilator Installation

**Ubuntu/Debian:**
```bash
sudo apt-get update
sudo apt-get install verilator
```

**From Source (for latest version):**
```bash
git clone https://github.com/verilator/verilator
cd verilator
autoconf
./configure
make -j$(nproc)
sudo make install
```

**Verify Installation:**
```bash
verilator --version
# Should show: Verilator 4.0 or higher
```

---

#### CocoTB Installation

**Via pip (Recommended):**
```bash
pip install cocotb pytest-xdist
```

**Verify Installation:**
```bash
python -c "import cocotb; print(cocotb.__version__)"
```

---

#### Bridge Generator Installation

**The Bridge generator is already included in this repository.**

**Verify Generator Installation:**
```bash
cd ~/github/rtldesignsherpa
python projects/components/bridge/bin/bridge_generator.py --help
```

**Expected Output:**
```
usage: bridge_generator.py [-h] [--config CONFIG] [--bulk BULK]
                           [--generate-tests] [--verbose]
...
```

---

#### Directory Structure Overview

```
rtldesignsherpa/
├── projects/components/bridge/
│   ├── bin/
│   │   ├── bridge_generator.py      ← Main generator script
│   │   ├── bridge_pkg/              ← Generator Python package
│   │   └── test_configs/            ← Example configurations
│   ├── rtl/                         ← Generated RTL output
│   ├── dv/tests/                    ← Test suite
│   └── docs/bridge_spec/            ← This documentation
```

---

#### Quick Verification

**Run a quick test to verify everything is working:**

```bash
cd projects/components/bridge/dv/tests
pytest test_bridge_2x2_rw.py::test_basic_read -v
```

**Expected Result:**
- Test compiles RTL
- Simulation runs
- Test PASSES ✅

**If the test fails:**
- Check Verilator installation: `verilator --version`
- Check Python packages: `pip list | grep cocotb`
- Check you're in virtual environment: `which python`

---

#### Troubleshooting

**Problem: `ModuleNotFoundError: No module named 'cocotb'`**

**Solution:**
```bash
pip install cocotb pytest-xdist
```

**Problem: `verilator: command not found`**

**Solution:**
```bash
sudo apt-get install verilator
# or compile from source (see above)
```

**Problem: `Permission denied` when running generator**

**Solution:**
```bash
chmod +x projects/components/bridge/bin/bridge_generator.py
```

**Problem: Tests hang or timeout**

**Solution:**
- Don't use parallel execution with waves: `pytest test_name.py` (not `-n 48`)
- See Chapter 5: Verification for safe test execution

---

#### Next Steps

Once installation is complete:
- **[02_first_bridge.md](02_first_bridge.md)** - Generate your first bridge
- **[03_simulation.md](03_simulation.md)** - Run simulations
- **[04_integration.md](04_integration.md)** - Integrate into your design

---

**Installation Complete!** ✅

You're now ready to generate your first AXI4 crossbar bridge.
