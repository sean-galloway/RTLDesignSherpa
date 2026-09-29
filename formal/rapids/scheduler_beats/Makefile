# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler_beats (RAPIDS fub_beats variant)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/includes

# Package files (order matters: dependencies first)
# NOTE: monitor_pkg.sv re-exports create_monitor_packet from monitor_common_pkg,
# causing sv2v ambiguity. We use a local empty stub (monitor_pkg_stub.sv) instead,
# which satisfies the import without re-exporting duplicate symbols.
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(CURDIR)/monitor_pkg_stub.sv \
        $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/includes/rapids_pkg.sv

# RTL dependencies: the extended-addressing generators and the FIFO stack they use
# The extended-addressing generators (rapids TASK-015 port of STREAM TASK-101)
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/projects/components/misc/rtl/dma_address_gen.sv \
        $(REPO_ROOT)/projects/components/misc/rtl/stream_run_addr_gen.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/fub_beats/scheduler_beats.sv

.PHONY: prove cover clean

prove: scheduler_beats_flat.v
	sby -f scheduler_beats.sby prove

cover: scheduler_beats_flat.v
	sby -f scheduler_beats.sby cover

scheduler_beats_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
