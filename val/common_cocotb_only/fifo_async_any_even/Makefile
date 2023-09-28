CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
SIM_ARGS=-v 

VERILOG_INCLUDE_DIRS = $(REPO_ROOT)/rtl/common
VERILOG_SOURCES = \
					$(REPO_ROOT)/rtl/common/find_first_set.sv \
					$(REPO_ROOT)/rtl/common/find_last_set.sv \
					$(REPO_ROOT)/rtl/common/leading_one_trailing_one.sv \
					$(REPO_ROOT)/rtl/common/counter_bin.sv \
					$(REPO_ROOT)/rtl/common/counter_johnson.sv \
					$(REPO_ROOT)/rtl/common/grayj2bin.sv \
					$(REPO_ROOT)/rtl/common/glitch_free_n_dff_arn.sv \
					$(REPO_ROOT)/rtl/common/fifo_async_any_even.sv

DUT = fifo_async_any_even
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).DEPTH=10
COMPILE_ARGS += -P $(DUT).DATA_WIDTH=8
COMPILE_ARGS += -P $(DUT).ALMOST_WR_MARGIN=2
COMPILE_ARGS += -P $(DUT).ALMOST_RD_MARGIN=2

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
