# SPDX-License-Identifier: MIT
# Formal verification Makefile for ctrlwr_engine (RAPIDS control engine, Phase 2)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Modelled on descriptor_engine_beats: the engine imports the monitor packages
# through rapids_imports.svh, so the same package list and monitor_pkg stub apply.
REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/dmas/rapids/rtl/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(CURDIR)/monitor_pkg_stub.sv \
        $(REPO_ROOT)/projects/components/dmas/rapids/rtl/includes/rapids_pkg.sv

DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv

DUT := $(REPO_ROOT)/projects/components/dmas/rapids/rtl/fub/ctrlwr_engine.sv

.PHONY: prove cover clean
prove: ctrlwr_engine_flat.v
	sby -f ctrlwr_engine.sby prove
cover: ctrlwr_engine_flat.v
	sby -f ctrlwr_engine.sby cover
ctrlwr_engine_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v *_prove *_cover
