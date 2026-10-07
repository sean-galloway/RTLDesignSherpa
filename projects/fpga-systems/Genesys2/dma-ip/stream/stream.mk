#==============================================================================
# Genesys 2 stream -- settings shared by EVERY build in this component.
#
# build-mon and build-perf are the same design at different parameters, so a
# value that is a property of the DESIGN belongs here and a value that is a
# property of one BUILD belongs in that build's Makefile. Include this before
# make/fpga_flow.mk.
#==============================================================================

# Verilator's unroll budget for the lint gate, read from the one source the
# cocotb tests already read -- dv/stream_cfg.py::verilator_unroll_args().
#
# The monitor's per-slot loops do delayed array assignment over a CAM sized
# MAX(16, NUM_CHANNELS * Ax_MAX_OUTSTANDING + MON_TRANS_MARGIN); at the
# package's 8x8 that is 72 slots, past the stock budget. Verilator then emits
# BLKLOOPINIT and refuses to elaborate.
#
# Derived, never retyped. That docstring exists because the number had been
# copy-pasted into seven run() calls and raising it in only some of them broke
# build-perf's ext_* tests. `make lint` was the eighth consumer and the one that
# never got it: build-mon's gate exited 22 BLKLOOPINIT errors against RTL every
# cocotb test compiled clean. A gate that cannot elaborate the design is not
# checking the design.
#
# build-perf lints clean today (USE_AXI_MONITORS=0 removes the deep loops). It
# is set for both anyway -- the split is a parameter, and `make lint
# USE_AXI_MONITORS=1` there is a supported cross-check.
#
# On failure this resolves to a literal that Verilator rejects by name, rather
# than to empty. An empty budget would fail as 22 BLKLOOPINIT errors pointing
# at the monitor -- blaming the RTL for a broken derivation.
# Plain `python3`, not $(PYTHON): this file is included BEFORE fpga_flow.mk (it
# has to be, so its `LINT_UNROLL ?=` sees a value), and $(PYTHON) is defined
# there. Naming it here would read as respecting a setting it cannot see yet.
_STREAM_CFG_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))/dv
LINT_UNROLL := $(shell PYTHONPATH=$(_STREAM_CFG_DIR) python3 -c \
    "from stream_cfg import verilator_unroll_args as v; print(' '.join(v()))" 2>/dev/null \
    || echo --STREAM-LINT-UNROLL-DERIVATION-FAILED-see-stream.mk)
