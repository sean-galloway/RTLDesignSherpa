# SPDX-License-Identifier: MIT
# Formal verification Makefile for stream_config_block
# Pure combinational module (assigns only), but uses `include "reset_defs.svh"
# so we run sv2v to strip the include and produce plain Verilog.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# No packages needed (pure combinational assign statements)
PKGS :=

# No RTL dependencies (no submodule instantiations)
DEPS :=

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/top/stream_config_block.sv

.PHONY: prove cover clean

prove: stream_config_block_flat.v
	sby -f stream_config_block.sby prove

cover: stream_config_block_flat.v
	sby -f stream_config_block.sby cover

stream_config_block_flat.v: $(DUT)
	$(SV2V) $(INC) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
