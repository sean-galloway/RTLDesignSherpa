# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# bridge_wr_rate_buf: write rate-matching buffer on a master's upsized path.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := bridge_wr_rate_buf_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_wr_rate_buf.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: bridge_wr_rate_buf_flat.v
	sby -f bridge_wr_rate_buf.sby prove

cover: bridge_wr_rate_buf_flat.v
	sby -f bridge_wr_rate_buf.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
