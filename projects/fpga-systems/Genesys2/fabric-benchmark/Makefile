# ==============================================================================
# Genesys 2 fabric benchmark -- generation and the Vivado fabric flows
# ==============================================================================
# The board build (harness top, bitstream, program, run) lands with K0/K1 and
# will include make/fpga_flow.mk. Until then this file carries the steps that
# exist: regenerate every leg, build the Vivado IP, and compare the legs out of
# context.
#
#   make regen            every generated file from the TOML (bin/regen.sh)
#   make vendor-ip        fb_xbar, fb_sc (SmartConnect BD), fb_mig -> fpga/ip/build
#   make check-xbar       prove the leg B1 HDL wrapper == the IP-catalog crossbar
#   make ooc LEG=sc PERIOD=4.0   one leg out of context -> reports/ooc/<leg>/<p>ns
#   make ooc-all          every leg at 10.0 ns (board target) and 4.0 ns (Fmax)
#   make mig-example      place and route MIG's example design -> reports/mig_example
#   make ooc-report       reports/ooc/README.md from every finished build
#   make sim              the cocotb tests (dv/tests)
#
# One Vivado per output directory: each recipe takes a flock on what it writes
# (two runs in one project tree corrupt each other and look like a hang).
# ==============================================================================
SHELL     := /bin/bash
AREA      := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
export REPO_ROOT ?= $(shell git -C $(AREA) rev-parse --show-toplevel)
export XILINX_VIVADO ?= /tools/Xilinx/2025.1/Vivado
VIVADO    ?= $(XILINX_VIVADO)/bin/vivado -mode batch -nojournal -notrace
IP_DIR    := $(AREA)/fpga/ip/build
LEGS      := bridge xbar sc
PERIODS   := 10.0 4.0
LEG       ?= bridge
PERIOD    ?= 10.0

.PHONY: help regen vendor-ip check-xbar ooc ooc-all ooc-report mig-example sim

help:
	@sed -n '/^#   make/s/^#   //p' $(lastword $(MAKEFILE_LIST))

regen:
	$(AREA)/bin/regen.sh

vendor-ip: regen
	mkdir -p $(AREA)/fpga/ip
	flock $(AREA)/fpga/ip/.lock $(VIVADO) -log $(AREA)/fpga/ip/vendor_ip.log \
	    -source $(AREA)/fpga/tcl/vendor_ip.tcl

check-xbar:
	python3 $(AREA)/bin/check_xbar_params.py

ooc:
	mkdir -p $(AREA)/reports/ooc/$(LEG)/$(PERIOD)ns
	cd $(AREA)/reports/ooc/$(LEG)/$(PERIOD)ns && FB_LEG=$(LEG) FB_PERIOD_NS=$(PERIOD) \
	    flock .lock $(VIVADO) -log ooc.log -source $(AREA)/fpga/tcl/ooc_fabric.tcl

ooc-all:
	$(MAKE) -f $(lastword $(MAKEFILE_LIST)) -j 6 $(foreach l,$(LEGS),$(foreach p,$(PERIODS),ooc-$(l)-$(p)))
	$(MAKE) -f $(lastword $(MAKEFILE_LIST)) ooc-report

ooc-%:
	$(MAKE) -f $(lastword $(MAKEFILE_LIST)) ooc LEG=$(word 1,$(subst -, ,$*)) PERIOD=$(word 2,$(subst -, ,$*))

ooc-report:
	python3 $(AREA)/bin/parse_ooc.py

mig-example:
	mkdir -p $(AREA)/reports/mig_example
	flock $(AREA)/fpga/ip/.lock $(VIVADO) -log $(AREA)/reports/mig_example/impl.log \
	    -source $(AREA)/fpga/tcl/mig_example_impl.tcl

sim:
	cd $(AREA)/dv/tests && $(MAKE) clean-all && $(MAKE) run-all-func
