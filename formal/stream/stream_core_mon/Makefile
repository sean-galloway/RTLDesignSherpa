# SPDX-License-Identifier: MIT
# Formal verification Makefile for stream_core_mon
# Same as stream_core but with monitors always enabled (no USE_AXI_MONITORS toggle)

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v
TMPDIR    := .sv2v_prep

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/axi_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# Common primitives
COMMON := $(REPO_ROOT)/rtl/common/counter_bin.sv \
          $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
          $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
          $(REPO_ROOT)/rtl/common/fifo_control.sv \
          $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
          $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv

# AMBA infrastructure
AMBA := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/axi4/axi4_master_rd.sv \
        $(REPO_ROOT)/rtl/amba/axi4/axi4_master_wr.sv \
        $(REPO_ROOT)/rtl/amba/shared/monbus_arbiter.sv

# Monitor files that need preprocessing
MON_ORIG := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timer.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_trans_mgr.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timeout.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_reporter.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_base.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_filtered.sv \
            $(REPO_ROOT)/rtl/amba/axi4/axi4_master_rd_mon.sv \
            $(REPO_ROOT)/rtl/amba/axi4/axi4_master_wr_mon.sv

MON_PREP := $(patsubst %,$(TMPDIR)/%, $(notdir $(MON_ORIG)))

# Stream FUBs
FUBS := $(REPO_ROOT)/projects/components/stream/rtl/fub/descriptor_engine.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/scheduler.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_alloc_ctrl.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_drain_ctrl.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_latency_bridge.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/sram_controller_unit.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/sram_controller.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/axi_read_engine.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/axi_write_engine.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/perf_profiler.sv

# Stream macros
MACROS := $(REPO_ROOT)/projects/components/stream/rtl/macro/scheduler_group.sv \
          $(REPO_ROOT)/projects/components/stream/rtl/macro/scheduler_group_array.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/macro/stream_core_mon.sv

.PHONY: prove cover clean

prove: stream_core_mon_flat.v
	sby -f stream_core_mon.sby prove

cover: stream_core_mon_flat.v
	sby -f stream_core_mon.sby cover

# Preprocess monitor files
$(TMPDIR):
	mkdir -p $(TMPDIR)

$(TMPDIR)/%.sv: $(REPO_ROOT)/rtl/amba/shared/%.sv | $(TMPDIR)
	sed -e 's/import monitor_pkg::\*;/import monitor_common_pkg::*; import monitor_amba4_pkg::*; import monitor_amba5_pkg::*; import monitor_arbiter_pkg::*;/g' \
	    -e 's/monitor_pkg::/monitor_common_pkg::/g' $< > $@

$(TMPDIR)/axi4_master_rd_mon.sv: $(REPO_ROOT)/rtl/amba/axi4/axi4_master_rd_mon.sv | $(TMPDIR)
	sed -e 's/import monitor_pkg::\*;/import monitor_common_pkg::*; import monitor_amba4_pkg::*; import monitor_amba5_pkg::*; import monitor_arbiter_pkg::*;/g' \
	    -e 's/monitor_pkg::/monitor_common_pkg::/g' $< > $@

$(TMPDIR)/axi4_master_wr_mon.sv: $(REPO_ROOT)/rtl/amba/axi4/axi4_master_wr_mon.sv | $(TMPDIR)
	sed -e 's/import monitor_pkg::\*;/import monitor_common_pkg::*; import monitor_amba4_pkg::*; import monitor_amba5_pkg::*; import monitor_arbiter_pkg::*;/g' \
	    -e 's/monitor_pkg::/monitor_common_pkg::/g' $< > $@

stream_core_mon_flat.v: $(DUT) $(PKGS) $(COMMON) $(AMBA) $(MON_PREP) $(FUBS) $(MACROS)
	$(SV2V) $(INC) $(PKGS) $(COMMON) $(AMBA) $(MON_PREP) $(FUBS) $(MACROS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover $(TMPDIR)
