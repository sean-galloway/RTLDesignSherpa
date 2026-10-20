# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler_group_array
# Workflow: sed strips ocelus_pkg imports -> sv2v flattens -> sby reads plain Verilog
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

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := scheduler_group_array_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/macro/scheduler_group_array.f
# ocelus_pkg re-exports its sub-packages' types, which trips sv2v's
# "ambiguous identifier"; the prep strips the import and the scope prefix.
FLAT_PREP       := s/import ocelus_pkg::\*;//g;s/ocelus_pkg:://g
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: scheduler_group_array_flat.v
	sby -f scheduler_group_array.sby prove

cover: scheduler_group_array_flat.v
	sby -f scheduler_group_array.sby cover

clean:
	rm -rf *_flat.v *.raw *_prove *_cover
