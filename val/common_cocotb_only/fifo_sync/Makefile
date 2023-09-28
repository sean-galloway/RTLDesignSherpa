CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(REPO_ROOT)/rtl/common
VERILOG_SOURCES = \
					$(REPO_ROOT)/rtl/common/counter_bin.sv \
					$(REPO_ROOT)/rtl/common/fifo_sync.sv

DUT = fifo_sync
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).DEPTH=4
COMPILE_ARGS += -P $(DUT).DATA_WIDTH=8

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
