# Formal Verification

Formal verification for RTL Design Sherpa using [SymbiYosys](https://github.com/YosysHQ/sby) (open-source formal verification framework).

## Quick Start

```bash
# Check tools are installed
make -C formal check-tools

# Quick proof (counter_bin, ~5 seconds)
make -C formal formal-quick

# All building block proofs (~30 seconds)
make -C formal formal-common

# Everything
make -C formal formal
```

## Directory Structure

```
formal/
├── common/                          Building block proofs (counters, arbiters, FIFOs)
├── amba/                            AMBA infrastructure (APB, AXI4 monitors, monbus)
├── apb_xbar/                        APB crossbar proofs
├── converters/                      Width/protocol converter proofs
├── bridge/                          Bridge AXI4 protocol verification
│   └── axi4_protocol/               Uses SVA-AXI4-FVIP for protocol checking
├── stream/                          STREAM DMA blocks (dmas/stream RTL)
├── rapids/                          RAPIDS DMA blocks (dmas/rapids *_beats RTL)
└── ext/                             External formal verification IP
    └── SVA-AXI4-FVIP/               YosysHQ AXI4 protocol checker (git submodule)
```

Per-block proofs are run from their directory, e.g. `cd formal/rapids/scheduler_beats && sby -f scheduler_beats.sby prove`. Each block's Makefile flattens the current RTL via sv2v (`make <block>_flat.v`) before `sby` reads the plain Verilog.

## What Gets Proved

### arbiter_round_robin_simple
- Grant output is always one-hot
- Only requesting agents receive grants
- No spurious grants when idle
- Fair scheduling: every requester served within N cycles

### counter_bin
- Reset initializes to zero
- Normal increment works correctly
- Wraparound: MSB flips, lower bits clear (FIFO pointer behavior)
- Hold behavior when disabled
- Lower bits always in valid range [0, MAX-1]

### fifo_sync
- Empty/full flags match actual occupancy
- Count never exceeds depth
- Write increments, read decrements, simultaneous preserves count
- Cannot be both full and empty
- Fill-then-drain reachability

## Prerequisites

- **yosys** (already installed)
- **sby** (SymbiYosys): `pip install sby`
- **boolector** (SMT solver): build from https://github.com/Boolector/boolector

## Adding New Proofs

1. Create directory: `formal/common/{module_name}/`
2. Write SVA properties: `formal_{module_name}.sv`
3. Write SymbiYosys config: `{module_name}.sby`
4. Add targets to `formal/common/Makefile`
5. Run: `cd formal/common/{module_name} && sby -f {module_name}.sby`

The old `docs/FORMAL_VERIFICATION_GUIDE.md` was removed; the per-testcase
READMEs and `.sby` files under `formal/` are the working reference.
