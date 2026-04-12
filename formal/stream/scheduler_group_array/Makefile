# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler_group_array
# Workflow: sed strips monitor_pkg imports -> sv2v flattens -> sby reads plain Verilog
#
# This module has the largest dependency tree in STREAM:
#   scheduler_group_array -> scheduler_group (x8) -> descriptor_engine -> gaxi_fifo_sync, gaxi_skid_buffer
#                                                  -> scheduler (pure logic)
#                                                  -> monbus_arbiter -> gaxi_skid_buffer, arbiter_round_robin
#                         -> arbiter_round_robin (descriptor AR arbitration)
#                         -> axi4_master_rd_mon -> axi4_master_rd -> gaxi_skid_buffer
#                                               -> axi_monitor_filtered -> axi_monitor_base
#                                                  -> axi_monitor_trans_mgr, axi_monitor_timer
#                                                  -> axi_monitor_timeout, axi_monitor_reporter -> gaxi_fifo_sync
#                         -> monbus_arbiter (9 sources)

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
# monitor_pkg_stub.sv provides an empty monitor_pkg so sv2v resolves the import
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        monitor_pkg_stub.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# All RTL dependencies requiring monitor_pkg stripping
# (axi4_master_rd_mon and its monitor infrastructure)
MON_DEPS := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timer.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_trans_mgr.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timeout.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_reporter.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_base.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_filtered.sv \
            $(REPO_ROOT)/rtl/amba/axi4/axi4_master_rd.sv \
            $(REPO_ROOT)/rtl/amba/axi4/axi4_master_rd_mon.sv

# RTL dependencies that do NOT import monitor_pkg
CLEAN_DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
              $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
              $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
              $(REPO_ROOT)/rtl/common/fifo_control.sv \
              $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
              $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
              $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
              $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
              $(REPO_ROOT)/rtl/amba/shared/monbus_arbiter.sv \
              $(REPO_ROOT)/projects/components/stream/rtl/fub/descriptor_engine.sv \
              $(REPO_ROOT)/projects/components/stream/rtl/fub/scheduler.sv \
              $(REPO_ROOT)/projects/components/stream/rtl/macro/scheduler_group.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/macro/scheduler_group_array.sv

# Post-processing script to fix multi-driver issues in sv2v output.
# descriptor_engine has two always_ff blocks driving r_descriptor_error
# (main FSM + separate APB address-0 check). sv2v emits both as independent
# always blocks, which yosys rejects. The patch merges the second block.
PATCH := python3 $(CURDIR)/patch_flat.py

TMPDIR := /tmp/formal_scheduler_group_array

.PHONY: prove cover clean

prove: scheduler_group_array_flat.v
	sby -f scheduler_group_array.sby prove

cover: scheduler_group_array_flat.v
	sby -f scheduler_group_array.sby cover

scheduler_group_array_flat.v: $(DUT) $(PKGS) $(MON_DEPS) $(CLEAN_DEPS) patch_flat.py
	@mkdir -p $(TMPDIR)
	@for f in $(MON_DEPS); do \
		sed -e 's/import monitor_pkg::\*;//g' \
		    -e 's/monitor_pkg:://g' $$f > $(TMPDIR)/$$(basename $$f); \
	done
	$(SV2V) $(INC) $(PKGS) \
		$(CLEAN_DEPS) \
		$(TMPDIR)/axi_monitor_timer.sv \
		$(TMPDIR)/axi_monitor_trans_mgr.sv \
		$(TMPDIR)/axi_monitor_timeout.sv \
		$(TMPDIR)/axi_monitor_reporter.sv \
		$(TMPDIR)/axi_monitor_base.sv \
		$(TMPDIR)/axi_monitor_filtered.sv \
		$(TMPDIR)/axi4_master_rd.sv \
		$(TMPDIR)/axi4_master_rd_mon.sv \
		$(DUT) > $@.raw
	$(PATCH) $@.raw $@
	rm -f $@.raw
	@rm -rf $(TMPDIR)

clean:
	rm -rf *_flat.v *.raw *_prove *_cover
