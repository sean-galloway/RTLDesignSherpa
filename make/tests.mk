# ==============================================================================
# RDS test-area master Makefile  (TOOL-008)
# ==============================================================================
#
# The ONLY place test-running logic lives. Every test area's Makefile is four
# lines that set two variables and include this file:
#
#     AREA        := amba
#     PYTEST_DIST := --dist=loadgroup          # optional, area-specific
#     RDS_ROOT    := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
#     include $(RDS_ROOT)/make/tests.mk
#
# Target grammar (the whole surface):
#
#     make run-<all|testroot>-<gate|func|full>-<serial|parallel>
#
#   testroot is the test file with `test_` and `.py` stripped:
#     test_grey2bin.py  ->  make run-grey2bin-func-parallel
#
# Targets are DISCOVERED by globbing test_*.py, never enumerated. A new test is
# runnable the moment it lands - there is no list to update.
#
# Worker count is DERIVED from the machine (see below). No file in this repo
# may hardcode `-n <number>` again; a fixed 48 on an 8-core box is a 6x
# oversubscription and has already forced a hard machine kill.
#
# Handbook: [[test-runner]] (REG_LEVEL vs TEST_LEVEL, build-dir uniqueness),
#           [[running-regressions]] (always clean-all first).
# ==============================================================================

SHELL := /bin/bash

ifndef AREA
$(error AREA is not set. A test-area Makefile must set AREA before including make/tests.mk)
endif

# ------------------------------------------------------------------------------
# R1: figure out the machine. Never assume.
# ------------------------------------------------------------------------------
# Two independent ceilings, take the lower:
#
#   cores  - one Verilator worker is a compile+sim process, so cores is the
#            upper bound on useful concurrency.
#   memory - each worker peaks around GB_PER_WORKER during elaboration. This is
#            the ceiling that actually bites: oversubscribing RAM drives the box
#            into swap and it stops responding, which is the failure that
#            motivated this rewrite. Cores alone would not have caught it.
#
# Override either way:  make JOBS=16 run-all-func-parallel
#                       GB_PER_WORKER=4 make run-all-full-parallel

NPROC         := $(shell nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
MEM_GB        := $(shell awk '/^MemTotal:/ {printf "%d", $$2/1048576}' /proc/meminfo 2>/dev/null || echo 0)
GB_PER_WORKER ?= 2

_MEM_JOBS := $(shell m=$(MEM_GB); g=$(GB_PER_WORKER); \
                 if [ "$$m" -le 0 ] 2>/dev/null; then echo $(NPROC); \
                 else j=$$(( m / g )); [ "$$j" -lt 1 ] && j=1; echo $$j; fi)

JOBS ?= $(shell n=$(NPROC); m=$(_MEM_JOBS); \
            j=$$([ "$$n" -le "$$m" ] && echo "$$n" || echo "$$m"); \
            [ "$$j" -lt 1 ] && j=1; echo $$j)

# ------------------------------------------------------------------------------
# pytest invocation
# ------------------------------------------------------------------------------
PYTEST        ?= python3 -m pytest
PYTEST_VERBOSE?= -v
PYTEST_TBSTYLE?= --tb=short
PYTEST_RERUNS ?= --reruns 3 --reruns-delay 1
PYTEST_DIST   ?=
PYTEST_EXTRA  ?=

PYTEST_OPTS = $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_RERUNS) $(PYTEST_EXTRA)

_xdist_parallel = -n $(JOBS) $(PYTEST_DIST)
_xdist_serial   =

# ------------------------------------------------------------------------------
# R3: discover tests by globbing. Nothing is enumerated.
# ------------------------------------------------------------------------------
TESTS := $(sort $(wildcard test_*.py))
ROOTS := $(patsubst test_%.py,%,$(TESTS))

LEVELS := gate func full

_reg_gate := GATE
_reg_func := FUNC
_reg_full := FULL

# Mode and waves are OPTIONAL suffixes. Bare `run-<x>-<level>` is parallel
# without waves - the common case types shortest:
#
#     run-apb5_master-gate                  parallel, no waves
#     run-apb5_master-gate-parallel         same thing, said explicitly
#     run-apb5_master-gate-serial           one worker
#     run-apb5_master-gate-waves            parallel + FST dump
#     run-apb5_master-gate-serial-waves     both suffixes
#
# NONE is a placeholder for "no suffix" - an empty string vanishes from a make
# list, so it cannot be carried literally.
_modes_parallel := NONE parallel
_modes_serial   := serial
MODEKINDS       := parallel serial
WAVEKINDS       := NONE waves

_sfx = $(if $(filter NONE,$(1)),,-$(1))

.DEFAULT_GOAL := help

# ------------------------------------------------------------------------------
# R2: generate the grammar
# ------------------------------------------------------------------------------
# $(1) selector (all|testroot)  $(2) level  $(3) mode  $(4) mode-suffix token
# $(5) waves token
define _rds_rule
.PHONY: run-$(1)-$(2)$(call _sfx,$(4))$(call _sfx,$(5))
run-$(1)-$(2)$(call _sfx,$(4))$(call _sfx,$(5)):
	@echo "=============================================================================="
	@echo "$(AREA): $(1)  level=$(2) ($(_reg_$(2)))  mode=$(3)$(if $(filter parallel,$(3)), workers=$$(JOBS))$(if $(filter waves,$(5)),  waves=on)"
	@echo "=============================================================================="
	REG_LEVEL=$(_reg_$(2)) $(if $(filter waves,$(5)),WAVES=1 )$$(PYTEST) $$(PYTEST_OPTS) $$(_xdist_$(3)) $$(if $$(filter all,$(1)),$$(TESTS),test_$(1).py)
endef

# selector x level x mode x mode-alias x waves
_rds_gen = $(foreach l,$(LEVELS),$(foreach m,$(MODEKINDS),$(foreach a,$(_modes_$(m)),\
             $(foreach w,$(WAVEKINDS),$(eval $(call _rds_rule,$(1),$(l),$(m),$(a),$(w)))))))

$(call _rds_gen,all)
$(foreach r,$(ROOTS),$(call _rds_gen,$(r)))

# ------------------------------------------------------------------------------
# Back-compat: the contract the parent Makefiles already invoke
# ------------------------------------------------------------------------------
# `val/Makefile` and the repo-root `Makefile` drive areas with
# `$(MAKE) -C <area> <target>`. Extracted from both, the full set they call is:
#
#   val/Makefile   clean-all clean-build clean-logs clean-vcd collect-all
#                  list-all run-all run-all-parallel status
#   root Makefile  run-all-{gate,func,full}[-parallel]
#
# The generated grammar already covers the level-qualified ones. These are the
# rest. Keep them until those callers are migrated - dropping one silently
# turns a regression into a no-op, which is the failure mode this whole task
# exists to stop.

DEFAULT_LEVEL ?= func

.PHONY: run-all run-all-parallel run-all-serial
run-all:          run-all-$(DEFAULT_LEVEL)
run-all-parallel: run-all-$(DEFAULT_LEVEL)-parallel
run-all-serial:   run-all-$(DEFAULT_LEVEL)-serial

.PHONY: collect-all list-all status
collect-all:
	@$(PYTEST) --collect-only -q $(TESTS)

list-all: list

status:
	@echo "area           : $(AREA)"
	@echo "test roots     : $(words $(ROOTS))"
	@echo "workers (JOBS) : $(JOBS)  (nproc=$(NPROC), mem=$(MEM_GB)GB)"
	@echo "default level  : $(DEFAULT_LEVEL)"
	@echo "artifacts      : $(if $(wildcard local_sim_build),local_sim_build/ PRESENT - run clean-all,clean)"

# ------------------------------------------------------------------------------
# Housekeeping - identical in every area, so it lives here too
# ------------------------------------------------------------------------------
.PHONY: clean-logs clean-pycache clean-build clean-waves clean-vcd clean-all clean

clean-logs:
	@rm -rf logs/
	@find . -type f -name '*.log' -delete
	@echo "cleaned: logs"

clean-pycache:
	@find . -type d -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
	@find . -type f -name '*.pyc' -delete
	@echo "cleaned: __pycache__"

clean-build:
	@rm -rf local_sim_build/ sim_build/
	@find . -type d \( -name 'local_sim_build' -o -name 'sim_build' \) -exec rm -rf {} + 2>/dev/null || true
	@echo "cleaned: sim build dirs"

clean-waves:
	@find . -type f \( -name '*.vcd' -o -name '*.fst' \) -delete
	@echo "cleaned: waveforms"

clean-vcd: clean-waves          # name val/Makefile calls

clean-all: clean-logs clean-pycache clean-build clean-waves
	@echo "$(AREA): all test artifacts cleaned"

clean: clean-all

# ------------------------------------------------------------------------------
# Introspection
# ------------------------------------------------------------------------------
.PHONY: jobs list help

jobs:
	@echo "cores (nproc)      : $(NPROC)"
	@echo "memory (GB)        : $(MEM_GB)"
	@echo "GB_PER_WORKER      : $(GB_PER_WORKER)"
	@echo "memory-capped jobs : $(_MEM_JOBS)"
	@echo "JOBS (min of both) : $(JOBS)"

list:
	@echo "$(AREA): $(words $(ROOTS)) test roots discovered"
	@printf '  %s\n' $(ROOTS)

help:
	@echo "=============================================================================="
	@echo "$(AREA) tests - $(words $(ROOTS)) test roots, $(JOBS) parallel workers"
	@echo "=============================================================================="
	@echo ""
	@echo "  make run-<all|testroot>-<gate|func|full>[-serial|-parallel][-waves]"
	@echo ""
	@echo "    testroot = test file minus 'test_' and '.py'"
	@echo "    e.g.  test_apb5_master.py  ->  make run-apb5_master-func"
	@echo ""
	@echo "    -serial / -parallel and -waves are OPTIONAL."
	@echo "    Bare run-<x>-<level> is parallel without waves."
	@echo ""
	@echo "  make run-all-gate              quick smoke over the whole area"
	@echo "  make run-all-full              sign-off regression"
	@echo "  make run-all-gate-serial       same, one worker at a time"
	@echo ""
	@echo "  make clean-all                 ALWAYS do this first - see [[running-regressions]]"
	@echo "  make list                      show every discovered test root"
	@echo "  make jobs                      show how the worker count was derived"
	@echo ""
	@echo "  Override workers:  make JOBS=16 run-all-func-parallel"
	@echo "  Fewer, fatter:     make GB_PER_WORKER=4 run-all-full-parallel"
	@echo ""
