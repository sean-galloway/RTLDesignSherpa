# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# peregrine riscv-formal ISA proofs (riscv-ip/peregrine-rv32im TASK-001
# stage 5, PRD P12) -- driver.  Shaped like formal/merlin/riscv-formal.
#
#     export PATH=/mnt/data/tools/oss-cad-suite/bin:/tmp/sv2v/sv2v-Linux:$PATH
#     make -C formal/peregrine/riscv-formal checks      # MUL_DSP=0 suite
#     make -C formal/peregrine/riscv-formal checks_dsp  # MUL_DSP=1 suite
#     make -C formal/peregrine/riscv-formal all         # both
#     make -C formal/peregrine/riscv-formal clean
#
# What a suite target does, in order (merlin's Makefile has the reasons):
#   1. builds the formal/checks symlink farm (with the sed-patched
#      rvfi_macros.vh this yosys needs) and the formal/insns link;
#   2. runs genchecks.py on <suite>.cfg, which rmtree's and rewrites
#      <suite>/;
#   3. converts peregrine_core with sv2v into peregrine_flat.v here
#      (untracked), with RISCV_FORMAL_ALTOPS defined: peregrine_mdu then
#      returns riscv-formal's stand-in M results with its real timing;
#   4. runs every task in parallel and fails unless every check is PASS.
#
# formal/checks and formal/insns are shared with the kestrel, merlin and
# gatling suites, which rebuild them the same way: do not run two cores'
# suites at once.

REPO_ROOT    := $(abspath $(CURDIR)/../../..)
RISCV_FORMAL := $(REPO_ROOT)/vendor/riscv-formal
OSS_CAD_SUITE ?= /mnt/data/tools/oss-cad-suite/bin

export PATH := $(OSS_CAD_SUITE):$(PATH)

# formal_flat.mk forces the *_ROOT variables it knows from REPO_ROOT;
# peregrine's is not among them, so it is forced here the same way.
export PEREGRINE_ROOT := $(REPO_ROOT)/projects/components/riscv-ip/peregrine-rv32im

FLAT            := peregrine_flat.v
FLAT_FILELIST   := $(PEREGRINE_ROOT)/rtl/filelists/top/peregrine_core.f
FLAT_SV2V_FLAGS := --define=RISCV_FORMAL_ALTOPS
include $(REPO_ROOT)/make/formal_flat.mk

# Re-convert on every run (merlin's reason: an RTL edit under an unchanged
# .f must reach the flat).
$(FLAT): FORCE
FORCE:

.PHONY: all checks checks_dsp clean harness FORCE

all: checks checks_dsp

harness:
	@for tool in sby yosys sv2v bitwuzla; do \
	    command -v $$tool >/dev/null 2>&1 || { \
	        echo "error: $$tool not on PATH (export PATH=/mnt/data/tools/oss-cad-suite/bin:<sv2v>:$$PATH)" >&2; \
	        exit 1; }; \
	done
	rm -rf $(REPO_ROOT)/formal/checks
	ln -sfn $(RISCV_FORMAL)/insns $(REPO_ROOT)/formal/insns
	mkdir -p $(REPO_ROOT)/formal/checks
	@for f in $(RISCV_FORMAL)/checks/*; do \
	    b=$$(basename $$f); \
	    [ "$$b" = rvfi_macros.vh ] && continue; \
	    ln -sfn $$f $(REPO_ROOT)/formal/checks/$$b; \
	done
	sed 's/const rand reg/(* anyconst *) reg/' \
	    $(RISCV_FORMAL)/checks/rvfi_macros.vh > $(REPO_ROOT)/formal/checks/rvfi_macros.vh

# One suite: genchecks, run, summarize.  $(1) is the cfg / directory name.
define run_suite
	cd $(CURDIR) && python3 $(RISCV_FORMAL)/checks/genchecks.py $(1)
	$(MAKE) --no-print-directory -C $(CURDIR)/$(1) -j$$(nproc) -f makefile
	@fails=0; total=0; \
	for s in $(CURDIR)/$(1)/*/status; do \
	    [ -f $$s ] || continue; \
	    total=$$((total+1)); \
	    st=$$(cut -d' ' -f1 $$s); \
	    if [ "$$st" != "PASS" ]; then \
	        echo "NOT PASS: $$(dirname $$s | xargs basename): $$st"; \
	        fails=$$((fails+1)); \
	    fi; \
	done; \
	echo "riscv-formal peregrine $(1): $$((total-fails))/$$total checks PASS"; \
	[ $$fails -eq 0 ]
endef

checks: harness $(FLAT)
	$(call run_suite,checks)

checks_dsp: harness $(FLAT)
	$(call run_suite,checks_dsp)

clean: flat-clean
	rm -rf $(CURDIR)/checks $(CURDIR)/checks_dsp $(FLAT)
	rm -rf $(REPO_ROOT)/formal/checks
	rm -f $(REPO_ROOT)/formal/insns
