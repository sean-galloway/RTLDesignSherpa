# SPDX-License-Identifier: MIT
# Formal verification Makefile for amber_snoop_resp
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Closure: amber_pkg + gaxi_skid_buffer + axi4ace_snoop_slave (the transport)
# + amber_snoop_resp. The proof is about the shipped responder including its
# skid-buffered ACE transport, not a fork.
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/includes/amber_pkg.sv
SRCS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/ace/axi4ace_snoop_slave.sv \
        $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_snoop_resp.sv
TMPDIR := /tmp/formal_amber_snoop_resp

.PHONY: prove cover all clean

all: prove cover

prove: amber_snoop_resp_flat.v
	sby -f amber_snoop_resp.sby prove

cover: amber_snoop_resp_flat.v
	sby -f amber_snoop_resp.sby cover

amber_snoop_resp_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	# specialize_params pins the geometry values and deletes the parameter
	# declarations of the DUT: yosys bind only fires on truly parameterless
	# modules (without this the properties would be silently dropped).
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) | python3 ../specialize_params.py - $@ \
	    --param ADDR_WIDTH=32 --param DATA_WIDTH=64 --param LINE_BYTES=64 \
	    --module amber_snoop_resp
	@rm -rf $(TMPDIR)

clean:
	rm -rf amber_snoop_resp_prove amber_snoop_resp_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < amber_snoop_resp_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: amber_snoop_resp_flat.v does not match the RTL."; \
		echo "Regenerate with: make amber_snoop_resp_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) | python3 ../specialize_params.py - $@ \
	    --param ADDR_WIDTH=32 --param DATA_WIDTH=64 --param LINE_BYTES=64 \
	    --module amber_snoop_resp
	@rm -rf $(TMPDIR)
