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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# DV Suite

Bridge uses a cocotb/pytest DV suite in `dv/tests/`. Test classes live in `dv/tbclasses/`; runners live in `dv/tests/`.

## Test structure

```
dv/
├── tbclasses/
│   ├── bridge2x2_rw_tb.py          # per-config TB class
│   ├── bridge_mix_e_tb.py
│   └── ...
└── tests/
    ├── conftest.py
    ├── test_bridge_2x2_rw.py       # generated
    ├── test_bridge_mix_e.py        # generated
    ├── test_bridge_2x2_rw_tracking.py   # hand-written
    ├── test_bridge_1x2_rw_axi5a_atomics.py
    └── ...
```

## Running tests

Use the area Makefile, not bare pytest:

```bash
cd projects/components/fabric-gen-ip/bridge/dv/tests

# Specific test, gate level
make run-bridge_2x2_rw-gate

# All functional tests
make clean-all && make run-all-func

# Full regression
make clean-all && make run-all-full
```

Bridge tests run serially because each test consumes approximately 1 GB of memory.

## Test levels

Each generated wrapper exports `REG_LEVEL` cells:

| Level | Cells | Description |
|-------|-------|-------------|
| GATE | 72 | Smoke / gate-level depth |
| FUNC | 144 | Functional depth |
| FULL | 216 | Stress depth |

The TB reads the depth profile from `dv/tbclasses/bridge_levels.py`.

## Verification coverage

The DV suite covers:

- Basic read/write connectivity per master-slave pair.
- Boundary probe (address decode miss and subtractive catch-all).
- Arbitration fairness and multi-master contention.
- Burst transfers and packet atomicity.
- Width conversion paths.
- APB/AXI-Lite/AXI3/Wishbone slave conversions.
- AXI5 sideband propagation and atomics.
- Monitor stress (`*_mon_monitor.py`) and cfg regblock programming.

## When generator changes affect DV

After any generator change that affects the generated port list, width, or filelist, regenerate the tests and run `make clean-all && make run-all-func` before declaring the change safe.
