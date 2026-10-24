# monbus_wr_mux2 formal harness. Two AXI4-shaped write FUBs onto one, in
# AW order: the harness keeps its own AW-order queue from the port
# handshakes and checks W and B routing against it. Flattened with sv2v
# like its siblings; `make prove cover`.
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

FLAT            := monbus_wr_mux2_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/monbus_wr_mux2.f
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean
all: prove cover
prove: monbus_wr_mux2_flat.v
	sby -f monbus_wr_mux2.sby prove
cover: monbus_wr_mux2_flat.v
	sby -f monbus_wr_mux2.sby cover
clean:
	rm -rf monbus_wr_mux2_flat.v monbus_wr_mux2_prove monbus_wr_mux2_cover
