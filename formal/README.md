# Formal Verification

Formal verification for RTL Design Sherpa using [SymbiYosys](https://github.com/YosysHQ/sby) (open-source formal verification framework).

## Quick Start

```bash
# Check tools are installed
make -C formal check-tools

# Quick proof (counter_bin, ~5 seconds)
make -C formal formal-quick

# One area. common alone is 222 task directories, so this is minutes, not
# seconds -- the "~30 seconds" this README used to claim was written when the
# hand-maintained list ran 34 of them.
make -C formal formal-common

# Everything whose RTL lives in repo-root rtl/
make -C formal formal-rtl

# Everything, including the project areas
make -C formal formal

# What is there, and what each area's flow is
make -C formal/amba list
make -C formal/common list
```

Status is MEASURED rather than typed. `FORMAL_PRIORITY.md`'s Status column was
wrong in both directions until 2026-09-11 -- PASSING for directories holding no
proof, PASSING for proofs that could not open their own include file, and zero
errors for an area where sixteen tasks could not elaborate:

```bash
python3 bin/formal_status.py --areas amba cdc common integ_common --markdown
python3 bin/formal_status.py --inventory     # what exists, runs nothing
python3 bin/formal_audit_stimulus.py         # harnesses pinning a DUT input
```

## Directory Structure

```
formal/
├── common/                          Building blocks AND rtl/math (counters, arbiters, FIFOs, float)
├── cdc/                             rtl/cdc: async FIFOs, Gray/Johnson, handshakes
├── amba/                            AMBA infrastructure (APB, AXI4/AXIS monitors, monbus, wb4)
├── integ_common/                    Integration-level common proofs
├── apb_xbar/                        APB crossbar proofs (legacy naming)
├── apbx_xbar/                       APB crossbar proofs
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
4. Nothing to register. Since 2026-09-11 the area Makefiles DISCOVER their
   task set from the tree (`$(wildcard */*.sby)`), so a new directory with a
   `.sby` in it is picked up by `make prove-all` automatically. The old
   hand-maintained lists ran 34 of common's 222 proofs and nobody noticed,
   because a missing entry looks exactly like a passing run.
5. Run: `cd formal/<area>/{module_name} && sby -f {module_name}.sby`, or
   `make -C formal/<area> prove-<module_name>`.

If yosys cannot read your RTL -- package-typed ports, casts, unpacked array
ports, a non-constant parameter width -- do NOT fork the module or stub the
package. Give the task its own Makefile and flatten with sv2v first; see
`formal/amba/wb4_slave_cdc_cg/Makefile` for the current shape.

Status is MEASURED, not typed: `python3 bin/formal_status.py --markdown`.
`python3 bin/formal_audit_stimulus.py` finds harnesses that pin a DUT input
at a constant.

The old `docs/FORMAL_VERIFICATION_GUIDE.md` was removed; the per-testcase
READMEs and `.sby` files under `formal/` are the working reference, and the
method lives in `vault/handbook/dv/formal.md`.
