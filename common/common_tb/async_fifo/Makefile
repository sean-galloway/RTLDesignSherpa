CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../common
VERILOG_SOURCES = \
					$(CWD)/../../../common/bin2gray.sv \
					$(CWD)/../../../common/gray2bin.sv \
					$(CWD)/../../../common/glitch_free_n_dff_arn.sv \
					$(CWD)/../../../common/async_fifo.sv

DUT = async_fifo
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