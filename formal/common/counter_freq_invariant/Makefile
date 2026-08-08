# sv2v preprocessing for counter_freq_invariant
# Yosys can't parse SV function return statements
REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V := sv2v
INC := -I$(REPO_ROOT)/rtl/amba/includes

SRCS := $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv

.PHONY: prove cover clean

# Write via a temp file. `sv2v ... > $@` TRUNCATES the target before sv2v
# runs, so a missing or failing sv2v destroys the checked-in flat file and
# leaves 0 bytes behind -- which is exactly what happens on a machine without
# the OSS CAD Suite installed.
counter_freq_invariant_flat.v: $(SRCS)
	$(SV2V) $(INC) $(SRCS) > $@.tmp
	mv $@.tmp $@

# Is the checked-in flat file still what sv2v produces from the CURRENT RTL?
#
# The timestamp dependency above cannot answer that: the flat file is checked
# into git, and a clone or checkout stamps it with the time of the checkout, so
# make sees it as newer than its sources and never rebuilds. This file went
# THREE MONTHS stale that way (regenerated 2026-04-17, RTL changed 2026-07-25),
# and the proofs in between were run against a design that no longer existed.
# Compare content, not mtimes.
.PHONY: check-flat
check-flat:
	@$(SV2V) $(INC) $(SRCS) > $@.tmp
	@if diff -q $@.tmp counter_freq_invariant_flat.v >/dev/null; then \
		rm -f $@.tmp; echo "flat file is current"; \
	else \
		rm -f $@.tmp; \
		echo "STALE: counter_freq_invariant_flat.v does not match the RTL."; \
		echo "Regenerate with: make counter_freq_invariant_flat.v"; \
		exit 1; \
	fi

prove: counter_freq_invariant_flat.v
	sby -f counter_freq_invariant.sby prove

cover: counter_freq_invariant_flat.v
	sby -f counter_freq_invariant.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
