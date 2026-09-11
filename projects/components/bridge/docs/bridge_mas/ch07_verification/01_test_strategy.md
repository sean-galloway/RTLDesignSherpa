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

# Test Strategy

## Overview

Bridge verification is CocoTB-based and parameterized: the same infrastructure covers every bridge topology and protocol combination.

## Related Modules

- [Debug Guide](02_debug_guide.md) - Debugging failed tests
- [Signal Naming](../ch06_generated_rtl/02_signal_naming.md) - Pattern matching for BFMs

## Testing

### Test Categories

#### Unit Tests

Per-block verification:

```
Unit Test Coverage:
├── Master Adapter Tests
│   ├── bridge_id sideband tagging (IDs pass through unchanged)
│   ├── Channel routing
│   └── Backpressure handling
├── Address Decoder Tests
│   ├── Address mapping
│   ├── Multi-region support
│   └── Default slave routing
├── Arbiter Tests
│   ├── Round-robin fairness
│   ├── Grant/lock behavior
│   └── Multi-master contention
└── Converter Tests
    ├── Width up/down sizing
    ├── APB protocol conversion
    └── Burst handling
```

#### Integration Tests

Full bridge verification:

```
Integration Test Matrix:
├── 2x2 Configuration
│   ├── Basic read/write
│   ├── Concurrent transactions
│   └── Same-ID aliasing across masters (bridge_id keeps them apart)
├── 4x4 Configuration
│   ├── Full arbitration coverage
│   ├── Width conversion paths
│   └── Mixed protocol targets
└── NxM Configurations
    ├── Asymmetric topologies
    ├── Channel-specific masters
    └── Protocol mixing
```

### Test Parameterization

#### Configuration Matrix

Which parameters get swept, and why:

| Parameter | Test Values | Purpose |
|-----------|-------------|---------|
| NUM_MASTERS | 2, 4, 8 | Scalability |
| NUM_SLAVES | 2, 3, 4 | Routing coverage |
| DATA_WIDTH | 32, 64, 128, 256 | Width paths |
| ID_WIDTH | 4, 6, 8 | ID space |
| OUTSTANDING | 4, 8, 16 | Depth stress |

: Table 7.1: Test Parameter Matrix

#### Protocol Combinations

```python
# Test protocol matrix
PROTOCOL_COMBOS = [
    {"masters": ["axi4"], "slaves": ["axi4"]},
    {"masters": ["axi4"], "slaves": ["axi4", "apb"]},
    {"masters": ["axi4", "axil"], "slaves": ["axi4", "apb"]},
    {"masters": ["axi5"], "slaves": ["axi4", "axi5"]},         # interop + native
    {"masters": ["axi5", "axi5"], "slaves": ["axi4", "axi5"]}, # sideband through the arbiter
]
```

The AMBA5 fixtures in `bin/test_configs/`, each generated with its own
tests and TB class:

| Fixture | Shape | What it exercises |
|---|---|---|
| `bridge_1x2_{rd,wr}_axi5` | AXI5 master, AXI4 slaves | interop boundary; sideband terminates |
| `bridge_1x2_rd_axi5s` | AXI4 master, one AXI5 slave | AXI5 slave ports |
| `bridge_1x2_{rd,wr}_axi5n` | AXI5 both ends | native sideband values, poison (wr) |
| `bridge_1x2_wr_axi5a` | AXI5 both ends, `atomic`, write-only | store-class forwards; load/swap/compare DECERR at the filter |
| `bridge_1x2_rw_axi5a` | AXI5 both ends, `atomic`, rw | read-return atomics native: R data routed back by ID |
| `bridge_1x2_rw_axil5`, `bridge_1x2_rw_apb5` | AXI4 master, AXI5-Lite / APB5 slave | the Lite and APB5 shims |
| `bridge_2x2_axi5` | two AXI5 masters, AXI5 + AXI4 slaves | sideband through arbitration |
| `bridge_1x2_rd_axi5w` | AXI5 32b master, 64b AXI4 + 32b AXI5 slaves | sideband across a width converter |
| `bridge_2x2_lite_req` | AXI4-Lite + AXI5-Lite masters, 64b AXI4 + AXI5-Lite slaves | Lite requesters (BRIDGE-014): sideband forwarding, the aligner, ID-less masters sharing a slave |
| `bridge_2x3_apb_req` | APB4 + APB5 masters, AXI4 + AXI5-Lite + APB4 slaves | APB requesters (BRIDGE-014): `apb{4,5}_to_axi4`, PSLVERR folding, APB in / APB out |

: Table 7.1a: AMBA5 Fixtures

### Protocol-BFM-Only Testing with Memory-Backed Slaves

Modern bridge tests use **protocol BFMs only** (no direct DUT signal manipulation) with **memory-backed slave models**. If you find yourself poking a DUT signal in a test, stop — drive the protocol and check the memory instead. That includes AMBA5 sideband and atomics: the AXI5 BFMs take `nsaid`/`trace`/`unique`/`poison`/`atop` as transaction keyword arguments (`write_transaction`, `read_transaction`, `atomic_operation`), and the generated TB returns the echoed `trace` in the BFM's result.

The generated TB picks the BFM family from each port's protocol: AXI4 ports get the AXI4 BFMs, `axi5` ports the AXI5 BFMs (which declare every AMBA5 sideband field as optional, so one BFM binds to any feature subset), `axil5` ports the AXIL5 BFMs (`AXIL5Master*` on a master port), `apb5` slave ports `APB5Slave` and `apb`/`apb5` master ports `APBMaster`/`APB5Master`, all at the generator's 1-bit USER widths. Every AXI5 master port also gets an `AXI5ComplianceChecker` on the same prefix, armed in `setup_clocks_and_reset` and read by `tb.assert_compliance()`, which every generated test calls before it declares PASSED -- a protocol violation on the AXI5 boundary fails the test that caused it even when the data still round-tripped.

Slave memory models are capped at 64 KB per slave (`SLAVE_MEM_CAP_BYTES`). A probe past the model is answered by the one out-of-range contract every slave BFM follows (RDS-DV `shared/memory_model.py`): SLVERR, nothing written, `0xDEADDEAD` read data, one warning. The boundary probe swallows that error only for probes past the seeded region -- the error coming back from the slave the address decodes to is the routing evidence -- and `master_write` raises on any error response, so a SLVERR write never passes through a helper unnoticed. The model's limit is not the design's: an address the bridge does not decode at all is the subtractive slave's DECERR.

#### BFM Instantiation and Slave Models

```python
from CocoTBFramework.components.axi4 import AXI4Master, AXI4Slave
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.memory_model import MemoryModel

class BridgeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Create masters using protocol BFMs
        self.masters = []
        for i in range(NUM_MASTERS):
            prefix = f"m{i}_axi_"
            master = AXI4Master(
                dut=dut,
                prefix=prefix,
                clock=dut.aclk,
                reset=dut.aresetn
            )
            self.masters.append(master)

        # Create slave memory models (NOT direct signal manipulation)
        self.slaves = []
        for i in range(NUM_SLAVES):
            prefix = f"s{i}_axi_"
            slave = MemoryModel(
                dut=dut,
                prefix=prefix,
                clock=dut.aclk,
                reset=dut.aresetn,
                size=0x100000  # 1 MB memory per slave
            )
            self.slaves.append(slave)
```

#### Transaction Generation and Assertion

```python
async def cocotb_test_concurrent_writes(dut):
    """Test multiple masters writing simultaneously."""
    tb = BridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Generate transactions via BFMs only
    tasks = []
    for i, master in enumerate(tb.masters):
        addr = 0x1000 + (i * 0x100)
        data = 0xDEAD0000 + i
        # Drive via protocol BFM (no DUT signal poke)
        task = cocotb.start_soon(
            master.write(addr=addr, data=data, size=2)
        )
        tasks.append(task)

    # Wait for all writes to complete
    for task in tasks:
        await task

    # Verify via memory readback (not via routing logic check)
    for i, master in enumerate(tb.masters):
        addr = 0x1000 + (i * 0x100)
        readback = await master.read(addr=addr)
        assert readback == 0xDEAD0000 + i, \
            f"Master {i} readback mismatch at {addr:#x}"
```

#### Boundary Probe Testing

Address-window boundary probes catch address-decode errors at slave page edges:

```python
async def test_boundary_probes(self):
    """Probe top, middle, bottom of each slave's address window."""
    
    for slave_idx, (base_addr, window_size) in enumerate(self.slave_windows):
        # Payloads carry the slave index and the probe position, so a readback
        # mismatch says BOTH which probe failed and whether the write landed on
        # the wrong slave -- the failure a boundary probe is actually hunting.
        bottom, middle, top = (0xB0000000 | (slave_idx << 8) | pos
                               for pos in (0x0, 0x1, 0x2))

        # Probe bottom (base address)
        await self.masters[0].write(base_addr + 0x000, data=bottom)

        # Probe middle (arbitrary offset)
        await self.masters[0].write(base_addr + window_size // 2, data=middle)

        # Probe top (last valid address)
        await self.masters[0].write(base_addr + window_size - 1, data=top)

        # Verify via readback
        rb_bottom = await self.masters[0].read(base_addr + 0x000)
        rb_middle = await self.masters[0].read(base_addr + window_size // 2)
        rb_top = await self.masters[0].read(base_addr + window_size - 1)

        assert rb_bottom == bottom
        assert rb_middle == middle
        assert rb_top == top
```

### Coverage Goals

#### Functional Coverage

```
Coverage Targets:
├── Protocol Coverage
│   ├── All burst types (FIXED, INCR, WRAP)
│   ├── All sizes (1, 2, 4, 8, ... bytes)
│   └── All response types
├── Routing Coverage
│   ├── Every master to every slave path
│   ├── Default slave routing
│   └── Error response paths
├── Arbitration Coverage
│   ├── All grant combinations
│   ├── Priority scenarios
│   └── Lock sequences
└── Corner Cases
    ├── Maximum outstanding
    ├── ID exhaustion
    └── Backpressure saturation
```

#### Code Coverage

```
Code Coverage Targets:
├── Line Coverage: >95%
├── Branch Coverage: >90%
├── FSM State Coverage: 100%
└── Toggle Coverage: >85%
```

### Test Execution

#### Running the Suite

The bridge runs through the same four-line Makefile every val area uses
(`make/tests.mk`): always a clean build first, then one of three levels.

```bash
cd projects/components/bridge/dv/tests
make clean-all && make run-all-gate-parallel        # smoke: 72 cells
make clean-all && make run-all-func-parallel        # development: 144 cells
make clean-all && make run-all-full-parallel        # sign-off: 216 cells
make clean-all && make run-all-full-parallel-waves  # same, with dump.fst per cell
make run-bridge_2x2_rw-gate-parallel               # one file, by its glob stem
```

`REG_LEVEL` (set by the target) selects the grid in each wrapper: GATE runs
one `gate` cell per test, FUNC `gate`+`func`, FULL `gate`+`func`+`full`.
Each cell exports `TEST_LEVEL` and a `SEED` (pinned per test node, so a
rerun replays the same run) and the TB scales its work from the level
profile in `dv/tbclasses/bridge_levels.py`. Sibling cells of one test log
different `TEST_LEVEL=<x>` banners and different wall-clock -- that is the
evidence the grid is real. A raw `pytest` run works but is the FUNC subset
with no clean, and a sub-second "passed" on a stale build is a fiction.

#### Test Naming Convention

Cocotb test functions follow the pattern: `cocotb_test_{N}x{M}_{variant}_{scenario}`

```python
# Example: test_bridge_4x4_mon_capture.py
@cocotb.test()
async def cocotb_test_4x4_mon_capture(dut):
    """Monitor packet capture on 4x4 bridge with monitor enabled."""
    ...

# Pytest wrapper function
def test_bridge_4x4_mon_capture(request):
    """Wrapper to invoke cocotb_test_4x4_mon_capture."""
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel="bridge_4x4_mon",
        module=module,
        testcase="cocotb_test_4x4_mon_capture",
        ...
    )
```

#### Test Levels

What each depth does, per the profile in `bridge_levels.py`. Every count in
the suite is read from here; nothing hardcodes one.

| Level | Connectivity | Boundary probe | Arbitration | Monitor stress | Slaves |
|-------|--------------|----------------|-------------|----------------|--------|
| gate | 1 offset/pair | boundary pages, low offset only | 4 txn/master | 128 reads/phase | prompt |
| func | 4 offsets/pair | boundary pages, low/mid/high | 8 txn/master | 256 reads/phase | prompt |
| full | 16 offsets/pair | every seeded page, low/mid/high | 24 txn/master | 512 reads/phase | 24-cycle response delay |

: Table 7.2: Test Level Depth Profile

Measured on the 4x4 boundary probe: 4 s, 5 s and 40 s per cell. The FULL
run's monitor stress count of 128 at gate is deliberate -- the monbus err
FIFO is 64 deep and the ERR_BP phase asserts it saturates, which at exactly
64 reads was a race against the drain pump.

**Monitor Tests** (when `variants` includes `"mon"`):
- `test_bridge_1x2_rd_monitor_smoke`: Basic packet emission
- `test_bridge_1x2_rd_monitor_capture`: Packet parsing and verification
- `test_bridge_1x2_rd_monitor_error_inject`: SLVERR packet collection
- `test_bridge_1x2_rd_monitor_irq`: IRQ assertion on error FIFO
