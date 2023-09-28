CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(REPO_ROOT)/rtl/common
VERILOG_SOURCES = \
					$(REPO_ROOT)/rtl/common/math_adder_brent_kung_pg.sv \
					$(REPO_ROOT)/rtl/common/math_adder_brent_kung_black.sv \
					$(REPO_ROOT)/rtl/common/math_adder_brent_kung_gray.sv \
					$(REPO_ROOT)/rtl/common/math_adder_brent_kung_bitwisepg.sv \
					$(REPO_ROOT)/rtl/common/math_adder_brent_kung_grouppg_016.sv \
					$(REPO_ROOT)/rtl/common/math_adder_brent_kung_sum.sv \
					$(REPO_ROOT)/rtl/common/math_adder_brent_kung_016.sv

DUT = math_adder_brent_kung_016
MODULE = testbench
TOPLEVEL = $(DUT)


TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
