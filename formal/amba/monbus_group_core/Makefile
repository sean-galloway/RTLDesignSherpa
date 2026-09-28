# monbus_group_core formal harness (amba TASK-041). The legacy monbus_axil_group
# proof (formal/stream, retired 2026-09-28) described a module that no longer
# exists; this one proves the core every protocol wrapper is a thin shell
# around. Flattened with sv2v like its siblings; `make prove cover`.
REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC := -I$(REPO_ROOT)/rtl/amba/includes
# The dependency closure of rtl/amba/filelists/monbus_group.f, in that order
# (bin/filelist_registry.py --resolve rtl/amba/filelists/monbus_group.f).
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/math/math_adder_carry_save_nbit.sv \
        $(REPO_ROOT)/rtl/math/math_mod_3_compress.sv \
        $(REPO_ROOT)/rtl/amba/monitor/monbus_cam.sv \
        $(REPO_ROOT)/rtl/amba/monitor/monbus_cam_pipe.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/monitor/monbus_compressor.sv \
        $(REPO_ROOT)/rtl/amba/monitor/monbus_halfbeat_packer.sv
DUT  := $(REPO_ROOT)/rtl/amba/monitor/monbus_group_core.sv
.PHONY: prove cover all clean
all: prove cover
prove: monbus_group_core_flat.v
	sby -f monbus_group_core.sby prove
cover: monbus_group_core_flat.v
	sby -f monbus_group_core.sby cover
monbus_group_core_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@
clean:
	rm -rf monbus_group_core_flat.v monbus_group_core_prove monbus_group_core_cover
