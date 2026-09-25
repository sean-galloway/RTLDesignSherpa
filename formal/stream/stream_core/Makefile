# SPDX-License-Identifier: MIT
# Formal verification Makefile for stream_core
# Workflow: filelist closure -> one sed prep -> sv2v flattens -> sby reads plain Verilog
#
# SOURCES COME FROM THE FILELIST, NOT A HAND LIST (BUG-003, 2026-09-24).
# This Makefile used to hand-list 31 sources and rotted behind the monitor
# rework: it was missing monitor_trans_cam and ALL SIX axi_monitor_reporter_*
# sub-blocks, so `make prove` died at elaboration. stream_core.f says why in
# its own header -- "a consumer that hand-lists a component's files has to
# track that component's internal dependencies, and it silently rots when they
# change". So we resolve the filelist instead, and the rot cannot recur.
#
# NOTE: no other formal Makefile drives from a filelist yet (0 of 124). This
# one does because its closure is large enough that hand-listing demonstrably
# failed. See vault BUG-003 and [[filelists]].
#
# The old `monitor_pkg` sed workaround is GONE. Its premise -- "sv2v cannot
# handle the typedef re-export ambiguity" -- was re-tested against sv2v v0.0.13
# on the full 51-source closure INCLUDING monitor_pkg.sv: RC=0, clean stderr.
# Seven sed-prepped monitor copies are no longer needed.
#
# ONE prep remains: sv2v does not honour `// synopsys translate_off`, so the
# hang-diagnostic $display in axi_write_engine survives into the flat and yosys
# cannot size its $time argument (AST_AUTOWIRE). Strip it for FORMAL ONLY --
# simulation reads the original source and still gets the prints.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PYTHON    ?= python3
TMPDIR    := .sv2v_prep

FILELIST  := $(REPO_ROOT)/projects/components/dmas/stream/rtl/filelists/macro/stream_core.f
FLATTEN   := $(PYTHON) $(REPO_ROOT)/bin/flatten_filelist.py

# The single file needing preprocessing, and its prepped copy.
AWE_SRC   := $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/axi_write_engine.sv
AWE_PREP  := $(TMPDIR)/axi_write_engine.sv

.PHONY: prove cover clean srcs

prove: stream_core_flat.v
	sby -f stream_core.sby prove

cover: stream_core_flat.v
	sby -f stream_core.sby cover

$(TMPDIR):
	mkdir -p $(TMPDIR)

$(AWE_PREP): $(AWE_SRC) | $(TMPDIR)
	sed '/synopsys translate_off/,/synopsys translate_on/d' $< > $@

# The closure is re-resolved on every build of the flat. A change INSIDE a
# nested .f does not retrigger this rule on its own (make cannot see through
# the -f indirection without expanding it at parse time, which would run the
# resolver on every invocation); `make clean` or touching $(FILELIST) forces it.
stream_core_flat.v: $(FILELIST) $(AWE_PREP)
	$(FLATTEN) $(FILELIST) --absolute-paths --resolve-env -o $(TMPDIR)/stream_core.flat.f
	$(SV2V) \
	  $$(grep '^+incdir+' $(TMPDIR)/stream_core.flat.f | sed 's/^+incdir+/-I/') \
	  $$(grep -E '\.sv$$' $(TMPDIR)/stream_core.flat.f \
	     | sed 's|^$(AWE_SRC)$$|$(AWE_PREP)|') \
	  > $@

# Show the resolved source list (debugging aid: what the closure actually is).
srcs: | $(TMPDIR)
	$(FLATTEN) $(FILELIST) --absolute-paths --resolve-env

clean:
	rm -rf *_flat.v *_prove *_cover $(TMPDIR)
