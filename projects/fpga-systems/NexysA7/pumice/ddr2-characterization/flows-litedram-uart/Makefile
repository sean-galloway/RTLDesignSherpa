# LiteDRAM apples-to-apples characterization harness — Nexys A7 build/run.
SHELL      := /bin/bash
SELF_DIR   := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
# git rev-parse, not a ../ count: the ../../../.. here was correct at the OLD
# projects/NexysA7/... path and silently became two levels short when the area
# moved under projects/fpga-systems/ (2026-09-10). It only went unnoticed
# because callers usually have REPO_ROOT exported already.
REPO_ROOT  ?= $(shell git -C $(SELF_DIR) rev-parse --show-toplevel)
export REPO_ROOT
# The harness filelist chain reaches into the converters area.
export CONVERTERS_ROOT ?= $(REPO_ROOT)/projects/components/converters
VIVADO_BATCH := vivado -mode batch -nojournal -nolog
UART       ?= /dev/ttyUSB0
BAUD       ?= 115200

.PHONY: help regen bitstream program characterize status
help:
	@echo "LiteDRAM char harness targets:"
	@echo "  make regen        Regenerate litedram_core WITH bios (./regen.sh --bios)"
	@echo "  make bitstream    Vivado synth/impl/bitgen (litedram_char_top)"
	@echo "  make program      Flash the Nexys A7"
	@echo "  make characterize Perf sweep over UART (litedram host variant)"

regen:
	cd $(SELF_DIR) && ./regen.sh --bios

bitstream:
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source tcl/build_all.tcl

program:
	@[ -f $(SELF_DIR)/bitstream/litedram_char.bit ] || (echo "run 'make bitstream' first" && false)
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source tcl/program_fpga.tcl

characterize:
	@echo "[characterize] litedram host variant over $(UART) (see HARNESS_PLAN.md — "
	@echo "  reuse build-perf/host with the pumice-CSR config calls removed;"
	@echo "  harness_csr is at base 0)."
