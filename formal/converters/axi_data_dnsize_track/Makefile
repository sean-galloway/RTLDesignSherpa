# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# axi_data_dnsize, TRACK_BURSTS=1 (burst framing from burst_len / start_lane).
# The untracked mode is ../axi_data_dnsize.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes
PKGS :=
DEPS :=
DUT := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv

.PHONY: prove cover all clean

all: prove cover

prove: axi_data_dnsize_track_flat.v
	sby -f axi_data_dnsize_track.sby prove

cover: axi_data_dnsize_track_flat.v
	sby -f axi_data_dnsize_track.sby cover

axi_data_dnsize_track_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
