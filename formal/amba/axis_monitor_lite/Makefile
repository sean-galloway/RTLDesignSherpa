# axis_monitor_lite formal harness (rtl/amba/monitors TASK-003). Flattened with
# sv2v like its siblings; `make prove cover`.
REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC := -I$(REPO_ROOT)/rtl/amba/includes
DEPS := $(REPO_ROOT)/rtl/amba/includes/ocelus_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/ocelus_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT  := $(REPO_ROOT)/rtl/amba/ocelus/axis_monitor_lite.sv
.PHONY: prove cover all clean
all: prove cover
prove: axis_monitor_lite_flat.v
	sby -f axis_monitor_lite.sby prove
cover: axis_monitor_lite_flat.v
	sby -f axis_monitor_lite.sby cover
axis_monitor_lite_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@
clean:
	rm -rf axis_monitor_lite_flat.v axis_monitor_lite_prove axis_monitor_lite_cover
