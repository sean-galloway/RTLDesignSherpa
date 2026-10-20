# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# axi_data_dnsize, TRACK_BURSTS=1 (burst framing from burst_len / start_lane).
# The untracked mode is ../axi_data_dnsize.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi_data_dnsize_track_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/filelists/axi_data_dnsize.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: axi_data_dnsize_track_flat.v
	sby -f axi_data_dnsize_track.sby prove

cover: axi_data_dnsize_track_flat.v
	sby -f axi_data_dnsize_track.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
