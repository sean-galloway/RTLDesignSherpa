#==============================================================================
# pumice build-litedram -- LiteDRAM in pumice's place, the A/B yardstick.
# Flow logic is in the global make/fpga_flow.mk; this file is variables plus the
# one target that is genuinely specific to this build (core regeneration).
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

FLOW      := litedram_char
TOP       := litedram_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/litedram_char_harness.f
SIM_TESTS := $(SELF_DIR)/dv/tests
SEQ_DIR   := $(SELF_DIR)/../bin

include $(RDS_ROOT)/make/fpga_flow.mk

#---- LiteDRAM core generation (specific to this build) -----------------------
# Two cores from one YAML: gen/board (real A7DDRPHY, for silicon) and gen/sim
# (SDRAMPHYModel, verilatable). GENERATED -- never hand-edit; per CRITICAL RULE
# #0 the regen wipes and rebuilds both rather than refreshing one.
LITEDRAM_CFG ?= $(SELF_DIR)/litedram_hp.yml
LITEDRAM_GEN ?= $(SELF_DIR)/regen.sh

.PHONY: regen regen-bios

regen:              ## Regenerate both LiteDRAM cores into gen/ (RTL only)
	@[ -x $(LITEDRAM_GEN) ] || (echo "missing $(LITEDRAM_GEN)" && false)
	rm -rf $(SELF_DIR)/gen/board $(SELF_DIR)/gen/sim
	cd $(SELF_DIR) && ./regen.sh

regen-bios:         ## Regenerate with the BIOS compiled in (needs riscv-gcc)
	@[ -x $(LITEDRAM_GEN) ] || (echo "missing $(LITEDRAM_GEN)" && false)
	rm -rf $(SELF_DIR)/gen/board $(SELF_DIR)/gen/sim
	cd $(SELF_DIR) && ./regen.sh --bios

# The cores are an input to synthesis, so a build with no cores present is a
# confusing Vivado failure rather than an obvious one. Fail early instead.
bitstream: check-cores
synth:     check-cores

.PHONY: check-cores
check-cores:
	@[ -d $(SELF_DIR)/gen/board ] || \
	    (echo "No generated LiteDRAM core in gen/board -- run 'make regen' first." && false)
