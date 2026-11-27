# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# gatling Xcell interlock: bounded liveness of the core + Xcell unit against
# a fair abstract cell (gatling-rv32i TASK-005).  The flat is the real RTL,
# sv2v-flattened from the two blocks' own filelists.
#
#     export PATH=/mnt/data/tools/oss-cad-suite/bin:$PATH
#     make -C formal/gatling/xcell_live prove     # prove_live + prove_isolate + cover

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

FLAT          := gatling_xcell_live_flat.v
FLAT_FILELIST := $(REPO_ROOT)/projects/components/riscv-ip/gatling-rv32i/rtl/filelists/top/gatling_core.f \
                 $(REPO_ROOT)/projects/components/riscv-ip/gatling-rv32i/rtl/filelists/fub/gatling_xcell.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove live isolate cover clean
# One sby run for all tasks: separate concurrent runs of one .sby share
# its status database and crash on it.
prove: $(FLAT)
	sby -f gatling_xcell_live.sby prove_live prove_isolate cover

live: $(FLAT)
	sby -f gatling_xcell_live.sby prove_live

isolate: $(FLAT)
	sby -f gatling_xcell_live.sby prove_isolate

clean:
	rm -rf gatling_xcell_live_prove_live gatling_xcell_live_prove_isolate gatling_xcell_live_cover gatling_xcell_live .flat_build

cover: $(FLAT)
	sby -f gatling_xcell_live.sby cover
