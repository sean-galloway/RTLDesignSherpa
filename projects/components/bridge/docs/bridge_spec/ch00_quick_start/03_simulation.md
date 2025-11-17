### Quick Start - Simulation

#### Overview

Now that you've generated your first bridge, let's test it with **CocoTB simulations** to verify correct operation.

**What You'll Do:**
- Run basic read/write tests
- Verify address decoding
- Check arbitration
- View waveforms (optional)

**Time Required:** 10-15 minutes

---

#### Pre-Generated Test Suite

The Bridge component includes a comprehensive test suite in `dv/tests/`. For your `my_first_bridge`, there may not be a pre-generated test, so we'll use an existing test as reference or create a simple one.

**Available Pre-Generated Tests:**
```bash
cd ~/github/rtldesignsherpa/projects/components/bridge/dv/tests
ls test_bridge_*.py
```

**Output:**
```
test_bridge_1x2_rd.py
test_bridge_1x2_wr.py
test_bridge_2x2_rw.py     ← Similar to our bridge!
test_bridge_5x3_channels.py
```

---

#### Quick Test: Use Existing 2x2 Bridge

**Let's test the pre-generated `bridge_2x2_rw` which is similar to your bridge:**

```bash
cd ~/github/rtldesignsherpa/projects/components/bridge/dv/tests

# Run basic read test (sequential, no waves)
pytest test_bridge_2x2_rw.py::test_basic_read -v
```

**Expected Output:**
```
=================== test session starts ===================
platform linux -- Python 3.x
collected 1 item

test_bridge_2x2_rw.py::test_basic_read PASSED     [100%]

================= 1 passed in 15.23s =================
```

**What Just Happened:**
1. Verilator compiled the bridge RTL (~1GB model)
2. CocoTB ran simulation
3. Test sent read transaction from master
4. Verified correct data returned
5. Test PASSED ✅

---

#### Understanding Test Output

**During test execution, you'll see:**

```
     0.00ns INFO     cocotb.gpi                         gpi_embed.cpp:76   in set_program_name_in_venv       Did not detect Python virtual environment
...
   100.00ns INFO     cocotb.bridge_2x2_rw_tb            Starting test_basic_read
   150.00ns INFO     cocotb.bridge_2x2_rw_tb            Master 0 initiating read to 0x00001000
   200.00ns INFO     cocotb.bridge_2x2_rw_tb            Address decoded to slave 0 (DDR)
   250.00ns INFO     cocotb.bridge_2x2_rw_tb            Transaction complete - data: 0xDEADBEEF
...
```

**Key Events:**
- **Address decode**: Which slave was selected
- **Transaction timing**: How many cycles
- **Data verification**: Expected vs actual

---

#### Run More Tests

**Basic Test Suite:**

```bash
# Test basic write
pytest test_bridge_2x2_rw.py::test_basic_write -v

# Test address decode (verifies correct slave selection)
pytest test_bridge_2x2_rw.py::test_address_decode -v

# Test arbitration (both masters, same slave)
pytest test_bridge_2x2_rw.py::test_arbitration -v
```

**Run All Tests for One Bridge:**
```bash
pytest test_bridge_2x2_rw.py -v
```

**Expected Results:**
- All basic tests should PASS
- Total time: 2-5 minutes depending on test count

---

#### ⚠️ CRITICAL: Safe Test Execution

**❌ DANGEROUS - Can Crash Your System:**
```bash
# DON'T DO THIS!
pytest test_bridge_2x2_rw.py -n 48 --waves
```

**Why?**
- Each test compiles ~1GB Verilator model
- `-n 48` spawns 48 parallel workers
- 48 × 1GB = 48GB+ memory usage
- Can cause system reboot even with 256GB RAM!

**✅ SAFE - Sequential Execution:**
```bash
# Run tests one at a time
pytest test_bridge_2x2_rw.py -v

# Or run single test
pytest test_bridge_2x2_rw.py::test_name -v
```

**See Chapter 5: Verification** for detailed test execution safety guidelines.

---

#### Viewing Waveforms (Optional)

**Generate VCD waveform file:**

```bash
pytest test_bridge_2x2_rw.py::test_basic_read -v --waves
```

**This creates:**
- `dv/tests/test_bridge_2x2_rw/sim_build/dump.vcd`
- Large file (~100MB-1GB depending on test duration)

**View with GTKWave:**
```bash
gtkwave dv/tests/test_bridge_2x2_rw/sim_build/dump.vcd
```

**Key Signals to Observe:**
- `cpu_m_axi_ar*` - Master read address channel
- `ddr_s_axi_ar*` - Slave read address channel
- `*_arvalid`, `*_arready` - Handshake signals
- `bridge_2x2_rw.u_cpu_master_adapter.slave_select_ar` - Address decode

**Waveform demonstrates:**
- Address decode logic
- Crossbar routing
- Arbitration decisions
- Data flow through bridge

---

#### Creating a Custom Test (Advanced)

If you want to test your `my_first_bridge` specifically:

**1. Generate Test Template:**
```bash
cd ~/github/rtldesignsherpa/projects/components/bridge/bin

python bridge_generator.py \
    --config ../my_bridges/my_first_bridge.toml \
    --connectivity ../my_bridges/my_first_bridge_connectivity.csv \
    --output ../rtl/generated/ \
    --generate-tests
```

**This creates:**
- `dv/tbclasses/my_first_bridge_tb.py` - Testbench class
- `dv/tests/test_my_first_bridge.py` - Test file

**2. Run Your Custom Test:**
```bash
cd ~/github/rtldesignsherpa/projects/components/bridge/dv/tests
pytest test_my_first_bridge.py::test_basic_read -v
```

---

#### Interpreting Test Results

**✅ Test PASSED:**
```
test_bridge_2x2_rw.py::test_basic_read PASSED
```
- Bridge correctly routed transactions
- Address decode worked
- Data integrity verified
- Ready for next step!

**❌ Test FAILED:**
```
test_bridge_2x2_rw.py::test_basic_read FAILED
FAILED test_bridge_2x2_rw.py::test_basic_read - AssertionError: Expected 0xDEADBEEF, got 0x00000000
```

**Common Failure Causes:**
1. **Address decode error** - Check base_addr/size in TOML
2. **Width mismatch** - Verify data_width consistency
3. **Timing issue** - Check for setup/hold violations in waveform
4. **Generator bug** - Report to maintainers

---

#### Performance Verification

**Check transaction latency:**

```bash
pytest test_bridge_2x2_rw.py::test_latency -v
```

**Expected Results:**
- **Single-beat read**: 2-3 cycles
- **Single-beat write**: 2-3 cycles
- **Burst transfer**: ~1 cycle/beat after address phase

**Meets Specification:**
- Latency ≤ 3 cycles for single transactions
- Burst efficiency > 95%

---

#### Troubleshooting Simulation Issues

**Problem: `ModuleNotFoundError: No module named 'cocotb'`**

**Solution:**
```bash
pip install cocotb pytest-xdist
```

**Problem: `Verilator: Can't find file: bridge_2x2_rw.sv`**

**Solution:**
```bash
# Regenerate the bridge
cd ~/github/rtldesignsherpa/projects/components/bridge
make -C dv/tests test  # Regenerates all bridges
```

**Problem: `Test timeout after 120 seconds`**

**Solution:**
- Check you're not running `-n 48` parallel
- Increase timeout: `pytest --timeout=300`
- See Chapter 5: Known Issues

**Problem: `Permission denied: dump.vcd`**

**Solution:**
```bash
# Clean old simulation artifacts
cd dv/tests
make clean-all
# Re-run test
pytest test_bridge_2x2_rw.py::test_basic_read --waves
```

---

#### Test Suite Summary

The Bridge test suite includes:

| Test Category | Tests | Purpose |
|---------------|-------|---------|
| **Basic** | 4-5 | Read, write, enable/disable |
| **Address Decode** | 3-4 | Correct slave selection |
| **Arbitration** | 2-3 | Fair access, no starvation |
| **Burst** | 2-3 | Multiple-beat transactions |
| **Edge Cases** | 3-4 | Back-to-back, overlapping |
| **Stress** | 1-2 | All masters, high traffic |

**Total per bridge configuration: ~15-20 tests**

---

#### Next Steps

**Simulations passing?** ✅

You're ready to integrate!

- **[04_integration.md](04_integration.md)** - Integrate bridge into your SoC design

**Additional Resources:**
- **Chapter 2: Blocks** - Understand internal architecture
- **Chapter 5: Verification** - Full test suite documentation
- **Chapter 7: Troubleshooting** - Debug failed tests

---

**Simulation Complete!** 🎉

Your bridge has been verified in simulation. The generated RTL is functionally correct and ready for integration or synthesis.

**Key Takeaways:**
- CocoTB provides Python-based verification
- Tests verify address decode, arbitration, data integrity
- Sequential execution is CRITICAL (no `-n 48` with waves!)
- Waveforms help debug issues
- ~15-20 tests per bridge configuration
