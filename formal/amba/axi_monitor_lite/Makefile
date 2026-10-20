# axi_monitor_lite formal harness (TASK-098). Flattened with sv2v like its
# siblings; `make prove cover`.
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi_monitor_lite_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/axi_monitor_lite.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean
all: prove cover
prove: axi_monitor_lite_flat.v
	sby -f axi_monitor_lite.sby prove
cover: axi_monitor_lite_flat.v
	sby -f axi_monitor_lite.sby cover
clean:
	rm -rf axi_monitor_lite_flat.v axi_monitor_lite_prove axi_monitor_lite_cover
