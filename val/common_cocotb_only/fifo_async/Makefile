CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
SIM_ARGS=-v

VERILOG_INCLUDE_DIRS = $(REPO_ROOT)/rtl/common
VERILOG_SOURCES = \
					$(REPO_ROOT)/rtl/common/counter_bingray.sv \
					$(REPO_ROOT)/rtl/common/gray2bin.sv \
					$(REPO_ROOT)/rtl/common/glitch_free_n_dff_arn.sv \
					$(REPO_ROOT)/rtl/common/fifo_async.sv

DUT = fifo_async
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).DEPTH=8
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
