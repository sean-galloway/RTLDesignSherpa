# axi_monitor_lite formal harness (TASK-098). Flattened with sv2v like its
# siblings; `make prove cover`.
REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC := -I$(REPO_ROOT)/rtl/amba/includes
DEPS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv
DUT  := $(REPO_ROOT)/rtl/amba/monitor-lite/axi_monitor_lite.sv
.PHONY: prove cover all clean
all: prove cover
prove: axi_monitor_lite_flat.v
	sby -f axi_monitor_lite.sby prove
cover: axi_monitor_lite_flat.v
	sby -f axi_monitor_lite.sby cover
axi_monitor_lite_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@
clean:
	rm -rf axi_monitor_lite_flat.v axi_monitor_lite_prove axi_monitor_lite_cover
