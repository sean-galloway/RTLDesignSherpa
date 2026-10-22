# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# bridge_id_remap: per-master transaction-ID remap table in a master adapter.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := bridge_id_remap_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_id_remap.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove bmc cover all clean

all: prove bmc cover

prove: bridge_id_remap_flat.v
	sby -f bridge_id_remap.sby prove

# bmc names the failing property in a trace; the prove engine (suprove) only reports FAIL.
bmc: bridge_id_remap_flat.v
	sby -f bridge_id_remap.sby bmc

cover: bridge_id_remap_flat.v
	sby -f bridge_id_remap.sby cover

clean:
	rm -rf *_flat.v *_prove *_bmc *_cover
