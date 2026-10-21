# SPDX-License-Identifier: MIT
# make/formal_flat.mk -- build a formal unit's *_flat.v from the DUT's filelist.
#
# Every formal flat's source list comes from bin/flatten_filelist.py over the
# DUT's own .f -- the same closure sim and lint compile. Nothing is hand-listed.
# On 2026-10-19 140 of 141 formal Makefiles hand-listed SRCS/DEPS, and adding
# reset_sync inside three blocks broke twelve proofs at once: each list was a
# snapshot of a closure that had moved on. A missing module is fixed in the
# RTL's .f, where sim, lint and formal all pick it up.
#
# A unit Makefile sets, then includes this file:
#   FLAT             output, e.g. foo_flat.v                        (required)
#   FLAT_FILELIST    one or more .f files, flattened in order       (required)
#   FLAT_SV2V_FLAGS  extra sv2v flags (--define=FORMAL, --exclude=Assert, ...)
#   FLAT_PREP        sed script run over every source before sv2v (optional)
#   FLAT_POST        shell filter on sv2v's output (optional, default cat)
#   FLAT_EXCLUDE     flatten_filelist --exclude patterns (optional)
#   FLAT_SPLICE      a formal props file spliced in before `endmodule` of ONE
#   FLAT_SPLICE_INTO   source, named by basename (both or neither; the props
#                      stay out of the RTL -- no assertions in RTL)
#
# It provides: $(FLAT), check-flat (content compare, the target
# bin/formal_status.py --check-flats runs), flat-srcs (print the closure),
# flat-clean.
#
# REPO_ROOT may be overridden on the command line (check-flats passes a
# canonical root); every *_ROOT below is FORCED from it, never inherited, so the
# path strings sv2v bakes into the flat depend on REPO_ROOT alone.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT
export AMBER_ROOT        := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1
export BRIDGE_ROOT       := $(REPO_ROOT)/projects/components/fabric-gen-ip/bridge
export CACHE_COMMON_ROOT := $(REPO_ROOT)/projects/components/cache-ip/common-ip
export CONVERTERS_ROOT   := $(REPO_ROOT)/projects/components/utility-ip/converters
export GATLING_ROOT      := $(REPO_ROOT)/projects/components/riscv-ip/gatling-rv32itetrad
export KESTREL_ROOT      := $(REPO_ROOT)/projects/components/riscv-ip/kestrel-rv32i
export RAPIDS_ROOT       := $(REPO_ROOT)/projects/components/dma-ip/rapids
export RETRO_ROOT        := $(REPO_ROOT)/projects/components/legacy-ip/retro_legacy_blocks
export STREAM_ROOT       := $(REPO_ROOT)/projects/components/dma-ip/stream

SV2V    ?= sv2v
PYTHON  ?= python3
FLATTEN := $(PYTHON) $(REPO_ROOT)/bin/flatten_filelist.py

FLAT_SV2V_FLAGS ?=
FLAT_PREP       ?=
FLAT_POST       ?= cat
FLAT_EXCLUDE    ?=
FLAT_SPLICE      ?=
FLAT_SPLICE_INTO ?=

FLAT_BUILD := .flat_build
FLAT_LIST  := $(FLAT_BUILD)/sources.f

ifndef FLAT
$(error formal_flat.mk: set FLAT (the *_flat.v to build) before including)
endif
ifndef FLAT_FILELIST
$(error formal_flat.mk: set FLAT_FILELIST (the DUT's .f) before including)
endif

# One recipe for the flat and for check-flat's regeneration, so the two can
# never disagree. $(1) is the output file.
#  1. flatten each filelist; concatenate, dropping repeats (first one wins)
#     and anything that is not HDL (a .f may carry a Verilator .vlt)
#  2. optionally copy every source through FLAT_PREP (basename-unique copies)
#  3. sv2v: +incdir+ lines become -I, everything else is a source in order
# Writes through a temp file: `sv2v > $@` truncates the target first, so a
# failing sv2v would leave a 0-byte committed flat behind.
define formal_flat_recipe
	@mkdir -p $(FLAT_BUILD)
	@rm -f $(FLAT_LIST).cat
	@set -e; for f in $(FLAT_FILELIST); do \
		$(FLATTEN) $$f --absolute-paths --resolve-env \
			$(addprefix --exclude ,$(FLAT_EXCLUDE)) > $(FLAT_LIST).one; \
		grep -vE '^[[:space:]]*(#|$$)' $(FLAT_LIST).one >> $(FLAT_LIST).cat; \
	done
	@awk '!seen[$$0]++' $(FLAT_LIST).cat \
		| grep -E '^\+incdir\+|\.(sv|v|svh|vh)$$' > $(FLAT_LIST)
	@if [ -n "$(FLAT_PREP)$(FLAT_SPLICE)" ]; then \
		set -e; mkdir -p $(FLAT_BUILD)/prep; \
		dup=$$(grep -v '^+incdir+' $(FLAT_LIST) | xargs -n1 basename | sort | uniq -d); \
		if [ -n "$$dup" ]; then echo "formal_flat.mk: prep copies collide on: $$dup" >&2; exit 1; fi; \
		for s in $$(grep -v '^+incdir+' $(FLAT_LIST)); do \
			sed -e '$(FLAT_PREP)' $$s > $(FLAT_BUILD)/prep/$$(basename $$s); \
		done; \
		if [ -n "$(FLAT_SPLICE)" ]; then \
			t=$(FLAT_BUILD)/prep/$(FLAT_SPLICE_INTO); \
			if [ ! -f "$$t" ]; then echo "formal_flat.mk: FLAT_SPLICE_INTO=$(FLAT_SPLICE_INTO) is not in the closure" >&2; exit 1; fi; \
			sed -i '/^endmodule/e cat $(FLAT_SPLICE)' $$t; \
		fi; \
		awk '/^\+incdir\+/ {print; next} {n=split($$0,p,"/"); print "$(FLAT_BUILD)/prep/" p[n]}' \
			$(FLAT_LIST) > $(FLAT_LIST).prep; \
		mv $(FLAT_LIST).prep $(FLAT_LIST); \
	fi
	$(SV2V) $(FLAT_SV2V_FLAGS) \
		$$(grep '^+incdir+' $(FLAT_LIST) | sed 's/^+incdir+/-I/') \
		$$(grep -v '^+incdir+' $(FLAT_LIST)) | $(FLAT_POST) > $(1).tmp
	@mv $(1).tmp $(1)
endef

$(FLAT): $(FLAT_FILELIST) $(FLAT_SPLICE)
	$(call formal_flat_recipe,$@)

# Content, not mtime: a checkout stamps the committed flat newer than its
# sources, so make would never rebuild it. Whitespace is squeezed to match the
# token comparison bin/formal_status.py applies.
.PHONY: check-flat flat-srcs flat-clean
check-flat:
	$(call formal_flat_recipe,$(FLAT_BUILD)/check_flat.v)
	@if [ "$$(tr -s '[:space:]' ' ' < $(FLAT_BUILD)/check_flat.v)" = "$$(tr -s '[:space:]' ' ' < $(FLAT))" ]; then \
		echo "flat file is current"; \
	else \
		echo "STALE: $(FLAT) does not match the RTL."; \
		echo "Regenerate with: make -B $(FLAT)"; \
		exit 1; \
	fi

flat-srcs:
	@for f in $(FLAT_FILELIST); do \
		$(FLATTEN) $$f --absolute-paths --resolve-env $(addprefix --exclude ,$(FLAT_EXCLUDE)); \
	done

flat-clean:
	rm -rf $(FLAT_BUILD)
