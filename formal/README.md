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
├── common/                          Building block proofs
│   ├── arbiter_round_robin_simple/  Round-robin arbiter (safety + fairness)
│   ├── counter_bin/                 Binary counter (wraparound correctness)
│   └── fifo_sync/                   Synchronous FIFO (pointer/flag correctness)
├── bridge/                          Bridge AXI4 protocol verification
│   └── axi4_protocol/              Uses SVA-AXI4-FVIP for protocol checking
└── ext/                             External formal verification IP
    └── SVA-AXI4-FVIP/              YosysHQ AXI4 protocol checker (git submodule)
```

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
- **boolector** (SMT solver): see docs/FORMAL_VERIFICATION_GUIDE.md

## Adding New Proofs

1. Create directory: `formal/common/{module_name}/`
2. Write SVA properties: `formal_{module_name}.sv`
3. Write SymbiYosys config: `{module_name}.sby`
4. Add targets to `formal/common/Makefile`
5. Run: `cd formal/common/{module_name} && sby -f {module_name}.sby`

See `docs/FORMAL_VERIFICATION_GUIDE.md` for detailed guide.
