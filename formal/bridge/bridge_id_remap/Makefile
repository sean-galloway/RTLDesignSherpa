# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# bridge_id_remap: per-master transaction-ID remap table in a master adapter.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes
PKGS :=
DEPS :=
DUT := $(REPO_ROOT)/projects/components/fabric-gen-ip/bridge/rtl/bridge_id_remap.sv

.PHONY: prove bmc cover all clean

all: prove bmc cover

prove: bridge_id_remap_flat.v
	sby -f bridge_id_remap.sby prove

# bmc names the failing property in a trace; pdr (prove) only reports FAIL.
bmc: bridge_id_remap_flat.v
	sby -f bridge_id_remap.sby bmc

cover: bridge_id_remap_flat.v
	sby -f bridge_id_remap.sby cover

bridge_id_remap_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_bmc *_cover
