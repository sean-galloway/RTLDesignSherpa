# monbus_group_core formal harness (amba TASK-041). The legacy monbus_axil_group
# proof (formal/stream, retired 2026-09-28) described a module that no longer
# exists; this one proves the core every protocol wrapper is a thin shell
# around. Flattened with sv2v like its siblings; `make prove cover`.
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := monbus_group_core_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/monbus_cam.f \
                   $(REPO_ROOT)/rtl/amba/filelists/monbus_group_core.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean
all: prove cover
prove: monbus_group_core_flat.v
	sby -f monbus_group_core.sby prove
cover: monbus_group_core_flat.v
	sby -f monbus_group_core.sby cover
clean:
	rm -rf monbus_group_core_flat.v monbus_group_core_prove monbus_group_core_cover
