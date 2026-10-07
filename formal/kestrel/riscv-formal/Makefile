# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# kestrel riscv-formal ISA proofs — driver.
#
# Regeneration (from the repo root, with oss-cad-suite + sv2v on PATH):
#
#     export PATH=/mnt/data/tools/oss-cad-suite/bin:/tmp/sv2v/sv2v-Linux:$PATH
#     make -C formal/kestrel/riscv-formal checks   # generate + run everything
#     make -C formal/kestrel/riscv-formal clean    # remove generated task dirs
#
# What this does, in order:
#   1. Builds the formal/checks and formal/insns harness entries genchecks.py
#      needs.  genchecks.py computes its root as cwd/../.. and opens
#      ../../insns/isa_<isa>.txt, so it must run exactly two levels below the
#      riscv-formal root; these entries let the proof live in the repo's
#      formal/ tree instead of inside vendor/.  formal/insns is a plain
#      symlink; formal/checks is a symlink farm around a sed-patched COPY of
#      rvfi_macros.vh — this yosys cannot parse `const rand reg` (used by the
#      consistency checkers) but accepts `(* anyconst *) reg` with identical
#      semantics, and sby re-copies [files] on every run so pre-patching the
#      task src/ would be clobbered.  The vendor tree is never modified.
#      `make clean` removes both entries.
#   2. Runs genchecks.py (reads checks.cfg here), which wipes and regenerates
#      the checks/ task directory with one <check>.sby per proof.
#   3. Converts the kestrel RTL with sv2v into checks/rtl_v/ (UNTRACKED).
#      The RTL uses package imports inside module bodies, which yosys's
#      read_verilog -sv cannot parse (yosys 0.62+95: "unexpected TOK_IMPORT"),
#      so riscv-formal cannot read the .sv directly; this is the repo's
#      standard sv2v step, only with the output left untracked.
#   4. Runs every generated sby task in parallel (z3 via smtbmc) and reports
#      a per-check PASS summary.  The target FAILS if any check is not PASS —
#      sby alone does not propagate that (`expect pass,fail`).

REPO_ROOT    := $(abspath $(CURDIR)/../../..)
RISCV_FORMAL := $(REPO_ROOT)/vendor/riscv-formal
RTL          := $(REPO_ROOT)/projects/components/riscv-ip/kestrel-rv32i/rtl
INCLUDES     := $(REPO_ROOT)/rtl/amba/includes
OSS_CAD_SUITE ?= /mnt/data/tools/oss-cad-suite/bin

export PATH := $(OSS_CAD_SUITE):$(PATH)

CHECKS_DIR := $(CURDIR)/checks
RTL_V      := $(CHECKS_DIR)/rtl_v
HARNESS    := $(REPO_ROOT)/formal/checks $(REPO_ROOT)/formal/insns

RTL_SV := $(RTL)/kestrel_pkg.sv \
          $(RTL)/kestrel_regfile.sv \
          $(RTL)/kestrel_alu.sv \
          $(RTL)/kestrel_imm_gen.sv \
          $(RTL)/kestrel_decode.sv \
          $(RTL)/kestrel_core.sv

.PHONY: checks clean

checks:
	@for tool in sby yosys sv2v z3; do \
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
	cd $(CURDIR) && python3 $(RISCV_FORMAL)/checks/genchecks.py checks
	mkdir -p $(RTL_V)
	sv2v -I $(INCLUDES) --write=$(RTL_V) $(RTL_SV)
	$(MAKE) --no-print-directory -C $(CHECKS_DIR) -j$$(nproc) -f makefile
	@fails=0; total=0; \
	for s in $(CHECKS_DIR)/*/status; do \
	    [ -f $$s ] || continue; \
	    total=$$((total+1)); \
	    st=$$(cut -d' ' -f1 $$s); \
	    if [ "$$st" != "PASS" ]; then \
	        echo "NOT PASS: $$(dirname $$s | xargs basename): $$st"; \
	        fails=$$((fails+1)); \
	    fi; \
	done; \
	echo "riscv-formal kestrel: $$((total-fails))/$$total checks PASS"; \
	[ $$fails -eq 0 ]

clean:
	rm -rf $(CHECKS_DIR)
	rm -rf $(REPO_ROOT)/formal/checks
	rm -f $(REPO_ROOT)/formal/insns
