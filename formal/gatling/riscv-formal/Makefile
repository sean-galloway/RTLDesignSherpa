# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# gatling riscv-formal ISA proofs (context 0) — driver.
#
# Regeneration (from the repo root, with oss-cad-suite + sv2v on PATH):
#
#     export PATH=/mnt/data/tools/oss-cad-suite/bin:/tmp/sv2v/sv2v-Linux:$PATH
#     make -C formal/gatling/riscv-formal checks   # generate + run everything
#     make -C formal/gatling/riscv-formal clean    # remove generated task dirs
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
#   3. Converts the gatling RTL with sv2v into gatling_flat.v here (UNTRACKED,
#      gitignored), beside this Makefile and outside checks/: genchecks.py
#      rmtree's checks/, and a flat inside it was deleted before sby ran.
#      The RTL uses package imports inside module bodies, which yosys's
#      read_verilog -sv cannot parse (yosys 0.62+95: "unexpected TOK_IMPORT"),
#      so riscv-formal cannot read the .sv directly; this is the repo's
#      standard sv2v step, only with the output left untracked.
#   4. Runs every generated sby task in parallel (bitwuzla via smtbmc) and reports
#      a per-check PASS summary.  The target FAILS if any check is not PASS —
#      sby alone does not propagate that (`expect pass,fail`).

REPO_ROOT    := $(abspath $(CURDIR)/../../..)
RISCV_FORMAL := $(REPO_ROOT)/vendor/riscv-formal
OSS_CAD_SUITE ?= /mnt/data/tools/oss-cad-suite/bin

export PATH := $(OSS_CAD_SUITE):$(PATH)

CHECKS_DIR := $(CURDIR)/checks
HARNESS    := $(REPO_ROOT)/formal/checks $(REPO_ROOT)/formal/insns

# The core's compile closure comes from its own filelist via
# bin/flatten_filelist.py (inside make/formal_flat.mk) -- never hand-listed.
# The hand list this replaced missed rtl/cdc/reset_sync.sv when the core
# gained its boundary reset synchronizer, and every check then failed to
# elaborate.
FLAT          := gatling_flat.v
FLAT_FILELIST := $(REPO_ROOT)/projects/components/riscv-ip/gatling-rv32i/rtl/filelists/top/gatling_core.f
include $(REPO_ROOT)/make/formal_flat.mk

# `checks` re-converts on every run: an RTL edit under an unchanged .f must
# still reach the flat, and formal_flat.mk's mtime rule alone would skip it.
# The flat sits in this directory, never under checks/: genchecks.py
# rmtree's checks/ (kestrel's flat lived in checks/rtl_v/ once and was deleted
# before sby ran, 2026-10-20); bin/check_formal_flat_sources.py fails any FLAT
# outside its unit dir.
#
# formal/checks and formal/insns are SHARED with formal/kestrel/riscv-formal
# (both build them identically): run the two proofs one after the other, not
# at once, or one `checks` deletes the other's harness mid-run.
$(FLAT): FORCE
FORCE:

.PHONY: checks clean FORCE

checks: $(FLAT)
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
	echo "riscv-formal gatling: $$((total-fails))/$$total checks PASS"; \
	[ $$fails -eq 0 ]

clean: flat-clean
	rm -rf $(CHECKS_DIR) $(FLAT)
	rm -rf $(REPO_ROOT)/formal/checks
	rm -f $(REPO_ROOT)/formal/insns
