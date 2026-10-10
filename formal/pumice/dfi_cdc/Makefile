# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_dfi_cdc.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Deps follow rtl/filelists/fub/pumice_dfi_cdc.f, which is the authority.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SHELL     := /bin/bash
# CI installs the pinned sv2v (v0.0.13) onto PATH (filelist-checks.yml). The
# dev machine keeps the same pinned binary at /mnt/data/tools/sv2v without
# putting it on PATH -- fall back to it so a bare `make formal-pumice` works
# locally. Override with SV2V=<path> if neither applies.
SV2V      ?= $(shell command -v sv2v 2>/dev/null || echo /mnt/data/tools/sv2v)
PUMICE    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
# Closure taken from rtl/cdc/filelists/cdc_fifo_bb.f, which is the authority --
# hand-assembling it missed gray2bin and counter_bingray and the build failed
# with "Module `\gray2bin' ... is not part of the design".
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/cdc/glitch_free_n_dff_arn.sv \
        $(REPO_ROOT)/rtl/common/find_first_set.sv \
        $(REPO_ROOT)/rtl/common/find_last_set.sv \
        $(REPO_ROOT)/rtl/common/leading_one_trailing_one.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/cdc/gray2bin.sv \
        $(REPO_ROOT)/rtl/cdc/bin2gray.sv \
        $(REPO_ROOT)/rtl/cdc/counter_bingray.sv \
        $(REPO_ROOT)/rtl/cdc/counter_johnson.sv \
        $(REPO_ROOT)/rtl/cdc/johnson2bin.sv \
        $(REPO_ROOT)/rtl/cdc/gaxi_fifo_async.sv
DUT  := $(PUMICE)/rtl/fub/pumice_dfi_cdc.sv

.PHONY: prove cover all clean check-flat
all: prove cover
prove: cdc_flat.v
	sby -f dfi_cdc.sby prove
cover: cdc_flat.v
	sby -f dfi_cdc.sby cover
# The wrapper needs the block's INTERNAL pairing/edge nets (w_wtok_push and
# friends). yosys 0.62 does not resolve dotted refs from the wrapper into the
# DUT -- they elaborate as implicit wires, which formal treats as FREE INPUTS
# (that was the name-resolution blocker; see inject_probes.py). So the
# generated flat file carries probe OUTPUT PORTS wired to those nets; the
# injection verifies every source hookup instance-by-instance and fails the
# build if the flat names drift. Tracked RTL is never modified.
cdc_flat.v: $(DUT) $(PKGS) $(DEPS) inject_probes.py
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > cdc_sv2v.v
	python3 inject_probes.py cdc_sv2v.v $@
clean:
	rm -rf *_flat.v cdc_flat.v cdc_sv2v.v dfi_cdc_prove dfi_cdc_cover

# House check-flat target (bin/formal_status.py --check-flats path (a)): the
# flatten recipe no longer has the single `<sv2v> > <flat>` redirect the
# replay path expects -- probe injection is a second step -- so this block
# answers the staleness question itself. The comparison masks the repo-root
# prefix (flatcmp.py, same normalization as the repo-wide sweep) so a flat
# built against a different checkout path still compares equal. The flat is
# gitignored here (built, not committed), so with no file present there is
# nothing to go stale.
check-flat:
	@tmp=$$(mktemp -d); trap "rm -rf $$tmp" EXIT; \
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $$tmp/raw.v && \
	python3 inject_probes.py $$tmp/raw.v $$tmp/probed.v || exit 1; \
	if [ ! -f cdc_flat.v ]; then \
	  echo "check-flat: no committed flat (gitignored area) -- nothing to compare"; \
	else \
	  python3 flatcmp.py cdc_flat.v $$tmp/probed.v \
	    && echo "check-flat: CURRENT" \
	    || { echo "check-flat: STALE -- run make cdc_flat.v"; exit 1; }; \
	fi
